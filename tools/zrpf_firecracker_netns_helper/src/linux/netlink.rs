use std::ffi::CString;
use std::mem::{size_of, zeroed};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};

use crate::NetnsHelperErrorV1;

const BUFFER_BYTES: usize = 64 * 1024;
const MAX_DUMP_DATAGRAMS: usize = 128;
const MAX_DUMP_MESSAGES: usize = 4096;
const SEQUENCE: u32 = 0x93a1_7c5d;
const NLM_F_REQUEST: u16 = 0x0001;
const NLM_F_DUMP: u16 = 0x0300;
const NLMSG_ERROR: u16 = 0x0002;
const NLMSG_DONE: u16 = 0x0003;
const RTM_NEWADDR: u16 = 20;
const RTM_GETADDR: u16 = 22;
const RTM_NEWROUTE: u16 = 24;
const RTM_GETROUTE: u16 = 26;
const RTA_OIF: u16 = 4;

pub(super) fn require_empty_network_inventory() -> Result<(), NetnsHelperErrorV1> {
    let loopback_name = CString::new("lo").map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
    let loopback_index = unsafe { libc::if_nametoindex(loopback_name.as_ptr()) };
    if loopback_index == 0 {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    let socket = open_netlink_socket()?;
    if dump_addresses(socket.as_raw_fd(), loopback_index)? != 0 {
        return Err(NetnsHelperErrorV1::NonLoopbackAddressPresent);
    }
    if dump_routes(socket.as_raw_fd(), loopback_index)? != 0 {
        return Err(NetnsHelperErrorV1::NonLoopbackRoutePresent);
    }
    Ok(())
}

fn open_netlink_socket() -> Result<OwnedFd, NetnsHelperErrorV1> {
    let descriptor = unsafe {
        libc::socket(
            libc::AF_NETLINK,
            libc::SOCK_RAW | libc::SOCK_CLOEXEC,
            libc::NETLINK_ROUTE,
        )
    };
    if descriptor < 0 {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    let socket = unsafe { OwnedFd::from_raw_fd(descriptor) };
    let mut address: libc::sockaddr_nl = unsafe { zeroed() };
    address.nl_family = c_int_u16(libc::AF_NETLINK)?;
    if unsafe {
        libc::bind(
            socket.as_raw_fd(),
            (&raw const address).cast::<libc::sockaddr>(),
            u32::try_from(size_of::<libc::sockaddr_nl>())
                .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
        )
    } != 0
    {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    Ok(socket)
}

#[repr(C)]
#[derive(Clone, Copy)]
struct NetlinkHeader {
    length: u32,
    message_type: u16,
    flags: u16,
    sequence: u32,
    port_id: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct AddressMessage {
    family: u8,
    prefix_length: u8,
    flags: u8,
    scope: u8,
    interface_index: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct RouteMessage {
    family: u8,
    destination_length: u8,
    source_length: u8,
    tos: u8,
    table: u8,
    protocol: u8,
    scope: u8,
    route_type: u8,
    flags: u32,
}

fn dump_addresses(socket: RawFd, loopback_index: u32) -> Result<u32, NetnsHelperErrorV1> {
    let payload = AddressMessage {
        family: c_int_u8(libc::AF_UNSPEC)?,
        prefix_length: 0,
        flags: 0,
        scope: 0,
        interface_index: 0,
    };
    let messages = netlink_dump(socket, RTM_GETADDR, bytes_of(&payload))?;
    let mut count = 0_u32;
    for message in messages {
        if message.message_type != RTM_NEWADDR {
            continue;
        }
        if message.payload.len() < size_of::<AddressMessage>() {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let address = read_unaligned::<AddressMessage>(&message.payload)?;
        if address.interface_index != loopback_index {
            count = count
                .checked_add(1)
                .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
        }
    }
    Ok(count)
}

fn dump_routes(socket: RawFd, loopback_index: u32) -> Result<u32, NetnsHelperErrorV1> {
    let payload = RouteMessage {
        family: c_int_u8(libc::AF_UNSPEC)?,
        destination_length: 0,
        source_length: 0,
        tos: 0,
        table: 0,
        protocol: 0,
        scope: 0,
        route_type: 0,
        flags: 0,
    };
    let messages = netlink_dump(socket, RTM_GETROUTE, bytes_of(&payload))?;
    let mut count = 0_u32;
    for message in messages {
        if message.message_type != RTM_NEWROUTE {
            continue;
        }
        if message.payload.len() < size_of::<RouteMessage>() {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let attributes = &message.payload[align4(size_of::<RouteMessage>())..];
        if route_output_interface(attributes)? != Some(loopback_index) {
            count = count
                .checked_add(1)
                .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
        }
    }
    Ok(count)
}

struct NetlinkMessage {
    message_type: u16,
    payload: Vec<u8>,
}

fn netlink_dump(
    socket: RawFd,
    message_type: u16,
    payload: &[u8],
) -> Result<Vec<NetlinkMessage>, NetnsHelperErrorV1> {
    let request = encode_dump_request(message_type, payload)?;
    send_dump_request(socket, &request)?;
    receive_dump(socket)
}

fn encode_dump_request(message_type: u16, payload: &[u8]) -> Result<Vec<u8>, NetnsHelperErrorV1> {
    let header = NetlinkHeader {
        length: u32::try_from(size_of::<NetlinkHeader>() + payload.len())
            .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
        message_type,
        flags: NLM_F_REQUEST | NLM_F_DUMP,
        sequence: SEQUENCE,
        port_id: 0,
    };
    let mut request = Vec::with_capacity(size_of::<NetlinkHeader>() + payload.len());
    request.extend_from_slice(bytes_of(&header));
    request.extend_from_slice(payload);
    Ok(request)
}

fn send_dump_request(socket: RawFd, request: &[u8]) -> Result<(), NetnsHelperErrorV1> {
    let mut kernel: libc::sockaddr_nl = unsafe { zeroed() };
    kernel.nl_family = c_int_u16(libc::AF_NETLINK)?;
    let sent = unsafe {
        libc::sendto(
            socket,
            request.as_ptr().cast(),
            request.len(),
            0,
            (&raw const kernel).cast::<libc::sockaddr>(),
            u32::try_from(size_of::<libc::sockaddr_nl>())
                .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
        )
    };
    if sent != isize::try_from(request.len()).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)? {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    Ok(())
}

fn receive_dump(socket: RawFd) -> Result<Vec<NetlinkMessage>, NetnsHelperErrorV1> {
    let mut messages = Vec::new();
    for _ in 0..MAX_DUMP_DATAGRAMS {
        let mut buffer = vec![0_u8; BUFFER_BYTES];
        let received = unsafe {
            libc::recv(
                socket,
                buffer.as_mut_ptr().cast(),
                buffer.len(),
                libc::MSG_TRUNC,
            )
        };
        if received <= 0 {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let received =
            usize::try_from(received).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
        if received > buffer.len() {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        buffer.truncate(received);
        if parse_datagram(&buffer, &mut messages)? {
            return Ok(messages);
        }
    }
    Err(NetnsHelperErrorV1::NetlinkRejected)
}

fn parse_datagram(
    buffer: &[u8],
    messages: &mut Vec<NetlinkMessage>,
) -> Result<bool, NetnsHelperErrorV1> {
    let mut offset = 0_usize;
    while offset < buffer.len() {
        let header = read_unaligned::<NetlinkHeader>(&buffer[offset..])?;
        let length =
            usize::try_from(header.length).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
        if length < size_of::<NetlinkHeader>() || offset + length > buffer.len() {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if header.sequence != SEQUENCE || header.port_id != 0 {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let payload = &buffer[offset + size_of::<NetlinkHeader>()..offset + length];
        if header.message_type == NLMSG_DONE {
            return Ok(true);
        }
        if header.message_type == NLMSG_ERROR {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if messages.len() >= MAX_DUMP_MESSAGES {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        messages.push(NetlinkMessage {
            message_type: header.message_type,
            payload: payload.to_vec(),
        });
        offset = offset
            .checked_add(align4(length))
            .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
    }
    Ok(false)
}

fn route_output_interface(attributes: &[u8]) -> Result<Option<u32>, NetnsHelperErrorV1> {
    let mut offset = 0_usize;
    let mut output = None;
    while offset < attributes.len() {
        if attributes.len() - offset < 4 {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let length = usize::from(u16::from_ne_bytes([
            attributes[offset],
            attributes[offset + 1],
        ]));
        let kind = u16::from_ne_bytes([attributes[offset + 2], attributes[offset + 3]]);
        if length < 4 || offset + length > attributes.len() {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if kind == RTA_OIF {
            if length != 8 || output.is_some() {
                return Err(NetnsHelperErrorV1::NetlinkRejected);
            }
            output = Some(u32::from_ne_bytes(
                attributes[offset + 4..offset + 8]
                    .try_into()
                    .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
            ));
        }
        offset = offset
            .checked_add(align4(length))
            .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
    }
    Ok(output)
}

fn align4(value: usize) -> usize {
    (value + 3) & !3
}

fn bytes_of<T>(value: &T) -> &[u8] {
    unsafe { core::slice::from_raw_parts((value as *const T).cast::<u8>(), size_of::<T>()) }
}

fn read_unaligned<T: Copy>(bytes: &[u8]) -> Result<T, NetnsHelperErrorV1> {
    if bytes.len() < size_of::<T>() {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    Ok(unsafe { core::ptr::read_unaligned(bytes.as_ptr().cast::<T>()) })
}

fn c_int_u8(value: libc::c_int) -> Result<u8, NetnsHelperErrorV1> {
    u8::try_from(value).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)
}

fn c_int_u16(value: libc::c_int) -> Result<u16, NetnsHelperErrorV1> {
    u16::try_from(value).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_or_duplicate_route_attributes_reject() {
        assert_eq!(
            route_output_interface(&[3, 0, 4, 0]),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        let mut duplicate = Vec::new();
        for value in [7_u32, 11_u32] {
            duplicate.extend_from_slice(&8_u16.to_ne_bytes());
            duplicate.extend_from_slice(&RTA_OIF.to_ne_bytes());
            duplicate.extend_from_slice(&value.to_ne_bytes());
        }
        assert_eq!(
            route_output_interface(&duplicate),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
    }

    #[test]
    fn message_bound_is_an_active_rejecting_witness() -> Result<(), NetnsHelperErrorV1> {
        let header = NetlinkHeader {
            length: u32::try_from(size_of::<NetlinkHeader>())
                .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
            message_type: RTM_NEWROUTE,
            flags: 0,
            sequence: SEQUENCE,
            port_id: 0,
        };
        let mut messages = (0..MAX_DUMP_MESSAGES)
            .map(|_| NetlinkMessage {
                message_type: RTM_NEWROUTE,
                payload: Vec::new(),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            parse_datagram(bytes_of(&header), &mut messages),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        Ok(())
    }
}
