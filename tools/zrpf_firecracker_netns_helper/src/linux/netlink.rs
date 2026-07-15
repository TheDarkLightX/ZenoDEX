use std::mem::{size_of, zeroed};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

use crate::NetnsHelperErrorV1;

const BUFFER_BYTES: usize = 64 * 1024;
const MAX_DUMP_DATAGRAMS: usize = 128;
const MAX_DUMP_MESSAGES: usize = 4096;
const SEQUENCE: u32 = 0x93a1_7c5d;
const NLM_F_REQUEST: u16 = 0x0001;
const NLM_F_MULTI: u16 = 0x0002;
const NLM_F_DUMP: u16 = 0x0300;
const NLM_F_DUMP_INTR: u16 = 0x0010;
const NLM_F_DUMP_FILTERED: u16 = 0x0020;
const NLMSG_ERROR: u16 = 0x0002;
const NLMSG_DONE: u16 = 0x0003;
const RTM_NEWLINK: u16 = 16;
const RTM_GETLINK: u16 = 18;
const RTM_NEWADDR: u16 = 20;
const RTM_GETADDR: u16 = 22;
const RTM_NEWROUTE: u16 = 24;
const RTM_GETROUTE: u16 = 26;
const IFLA_IFNAME: u16 = 3;
const RTA_OIF: u16 = 4;

pub(super) fn require_empty_network_inventory() -> Result<(), NetnsHelperErrorV1> {
    let socket = open_netlink_socket()?;
    let loopback_index = discover_loopback_index(&socket)?;
    if dump_addresses(&socket, loopback_index)? != 0 {
        return Err(NetnsHelperErrorV1::NonLoopbackAddressPresent);
    }
    if dump_routes(&socket, loopback_index)? != 0 {
        return Err(NetnsHelperErrorV1::NonLoopbackRoutePresent);
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn smoke_real_kernel_dumps_under_filter() -> Result<(), NetnsHelperErrorV1> {
    let socket = open_netlink_socket()?;
    let loopback_index = discover_loopback_index(&socket)?;
    let _ = dump_addresses(&socket, loopback_index)?;
    let _ = dump_routes(&socket, loopback_index)?;
    Ok(())
}

struct RouteNetlinkSocket {
    descriptor: OwnedFd,
    port_id: u32,
}

fn open_netlink_socket() -> Result<RouteNetlinkSocket, NetnsHelperErrorV1> {
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
    let mut assigned: libc::sockaddr_nl = unsafe { zeroed() };
    let mut assigned_length = u32::try_from(size_of::<libc::sockaddr_nl>())
        .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
    if unsafe {
        libc::getsockname(
            socket.as_raw_fd(),
            (&raw mut assigned).cast::<libc::sockaddr>(),
            &mut assigned_length,
        )
    } != 0
    {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    if assigned_length
        != u32::try_from(size_of::<libc::sockaddr_nl>())
            .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?
        || assigned.nl_family != c_int_u16(libc::AF_NETLINK)?
        || assigned.nl_pid == 0
        || assigned.nl_groups != 0
    {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    Ok(RouteNetlinkSocket {
        descriptor: socket,
        port_id: assigned.nl_pid,
    })
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
struct LinkMessage {
    family: u8,
    padding: u8,
    link_type: u16,
    interface_index: i32,
    flags: u32,
    change: u32,
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

fn discover_loopback_index(socket: &RouteNetlinkSocket) -> Result<u32, NetnsHelperErrorV1> {
    let payload = LinkMessage {
        family: c_int_u8(libc::AF_UNSPEC)?,
        padding: 0,
        link_type: 0,
        interface_index: 0,
        flags: 0,
        change: 0,
    };
    let messages = netlink_dump(socket, RTM_GETLINK, RTM_NEWLINK, bytes_of(&payload))?;
    let loopback_flag =
        u32::try_from(libc::IFF_LOOPBACK).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
    let mut loopback_index = None;
    for message in messages {
        if message.payload.len() < size_of::<LinkMessage>() {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let link = read_unaligned::<LinkMessage>(&message.payload)?;
        let index =
            u32::try_from(link.interface_index).map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
        if index == 0 {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let attributes = &message.payload[align4(size_of::<LinkMessage>())..];
        let name = required_interface_name(attributes)?;
        if name == b"lo"
            && (link.flags & loopback_flag == 0 || loopback_index.replace(index).is_some())
        {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
    }
    loopback_index.ok_or(NetnsHelperErrorV1::NetlinkRejected)
}

fn dump_addresses(
    socket: &RouteNetlinkSocket,
    loopback_index: u32,
) -> Result<u32, NetnsHelperErrorV1> {
    let payload = AddressMessage {
        family: c_int_u8(libc::AF_UNSPEC)?,
        prefix_length: 0,
        flags: 0,
        scope: 0,
        interface_index: 0,
    };
    let messages = netlink_dump(socket, RTM_GETADDR, RTM_NEWADDR, bytes_of(&payload))?;
    let mut count = 0_u32;
    for message in messages {
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

fn dump_routes(
    socket: &RouteNetlinkSocket,
    loopback_index: u32,
) -> Result<u32, NetnsHelperErrorV1> {
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
    let messages = netlink_dump(socket, RTM_GETROUTE, RTM_NEWROUTE, bytes_of(&payload))?;
    let mut count = 0_u32;
    for message in messages {
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
    payload: Vec<u8>,
}

fn netlink_dump(
    socket: &RouteNetlinkSocket,
    message_type: u16,
    expected_response_type: u16,
    payload: &[u8],
) -> Result<Vec<NetlinkMessage>, NetnsHelperErrorV1> {
    let request = encode_dump_request(message_type, socket.port_id, payload)?;
    send_dump_request(socket, &request)?;
    receive_dump(socket, expected_response_type)
}

fn encode_dump_request(
    message_type: u16,
    port_id: u32,
    payload: &[u8],
) -> Result<Vec<u8>, NetnsHelperErrorV1> {
    let header = NetlinkHeader {
        length: u32::try_from(size_of::<NetlinkHeader>() + payload.len())
            .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
        message_type,
        flags: NLM_F_REQUEST | NLM_F_DUMP,
        sequence: SEQUENCE,
        port_id,
    };
    let mut request = Vec::with_capacity(size_of::<NetlinkHeader>() + payload.len());
    request.extend_from_slice(bytes_of(&header));
    request.extend_from_slice(payload);
    Ok(request)
}

fn send_dump_request(
    socket: &RouteNetlinkSocket,
    request: &[u8],
) -> Result<(), NetnsHelperErrorV1> {
    let mut kernel: libc::sockaddr_nl = unsafe { zeroed() };
    kernel.nl_family = c_int_u16(libc::AF_NETLINK)?;
    let sent = unsafe {
        libc::sendto(
            socket.descriptor.as_raw_fd(),
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

fn receive_dump(
    socket: &RouteNetlinkSocket,
    expected_response_type: u16,
) -> Result<Vec<NetlinkMessage>, NetnsHelperErrorV1> {
    let mut messages = Vec::new();
    for _ in 0..MAX_DUMP_DATAGRAMS {
        let mut buffer = vec![0_u8; BUFFER_BYTES];
        let mut sender: libc::sockaddr_nl = unsafe { zeroed() };
        let mut sender_length = u32::try_from(size_of::<libc::sockaddr_nl>())
            .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
        let received = unsafe {
            libc::recvfrom(
                socket.descriptor.as_raw_fd(),
                buffer.as_mut_ptr().cast(),
                buffer.len(),
                libc::MSG_TRUNC,
                (&raw mut sender).cast::<libc::sockaddr>(),
                &mut sender_length,
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
        require_kernel_sender(&sender, sender_length)?;
        buffer.truncate(received);
        if parse_datagram(
            &buffer,
            expected_response_type,
            socket.port_id,
            &mut messages,
        )? {
            return Ok(messages);
        }
    }
    Err(NetnsHelperErrorV1::NetlinkRejected)
}

fn require_kernel_sender(
    sender: &libc::sockaddr_nl,
    sender_length: u32,
) -> Result<(), NetnsHelperErrorV1> {
    if sender_length
        != u32::try_from(size_of::<libc::sockaddr_nl>())
            .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?
        || sender.nl_family != c_int_u16(libc::AF_NETLINK)?
        || sender.nl_pid != 0
        || sender.nl_groups != 0
    {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    Ok(())
}

fn parse_datagram(
    buffer: &[u8],
    expected_response_type: u16,
    expected_port_id: u32,
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
        if header.sequence != SEQUENCE || header.port_id != expected_port_id {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if header.flags & (NLM_F_DUMP_INTR | NLM_F_DUMP_FILTERED) != 0 {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if header.flags & NLM_F_MULTI == 0 {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        let payload = &buffer[offset + size_of::<NetlinkHeader>()..offset + length];
        if header.message_type == NLMSG_DONE {
            if payload.len() != size_of::<i32>()
                || i32::from_ne_bytes(
                    payload
                        .try_into()
                        .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?,
                ) != 0
            {
                return Err(NetnsHelperErrorV1::NetlinkRejected);
            }
            let end = offset
                .checked_add(align4(length))
                .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
            if end != buffer.len() {
                return Err(NetnsHelperErrorV1::NetlinkRejected);
            }
            return Ok(true);
        }
        if header.message_type == NLMSG_ERROR {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if header.message_type != expected_response_type {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        if messages.len() >= MAX_DUMP_MESSAGES {
            return Err(NetnsHelperErrorV1::NetlinkRejected);
        }
        messages.push(NetlinkMessage {
            payload: payload.to_vec(),
        });
        offset = offset
            .checked_add(align4(length))
            .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
    }
    Ok(false)
}

fn required_interface_name(attributes: &[u8]) -> Result<&[u8], NetnsHelperErrorV1> {
    let mut offset = 0_usize;
    let mut name = None;
    while offset < attributes.len() {
        let (length, kind) = attribute_header(attributes, offset)?;
        if kind == IFLA_IFNAME {
            if name.is_some() || length < 5 {
                return Err(NetnsHelperErrorV1::NetlinkRejected);
            }
            let raw = &attributes[offset + 4..offset + length];
            if raw.last() != Some(&0) || raw[..raw.len() - 1].contains(&0) {
                return Err(NetnsHelperErrorV1::NetlinkRejected);
            }
            name = Some(&raw[..raw.len() - 1]);
        }
        offset = next_attribute_offset(offset, length)?;
    }
    name.ok_or(NetnsHelperErrorV1::NetlinkRejected)
}

fn route_output_interface(attributes: &[u8]) -> Result<Option<u32>, NetnsHelperErrorV1> {
    let mut offset = 0_usize;
    let mut output = None;
    while offset < attributes.len() {
        let (length, kind) = attribute_header(attributes, offset)?;
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
        offset = next_attribute_offset(offset, length)?;
    }
    Ok(output)
}

fn attribute_header(attributes: &[u8], offset: usize) -> Result<(usize, u16), NetnsHelperErrorV1> {
    if attributes.len().saturating_sub(offset) < 4 {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    let length = usize::from(u16::from_ne_bytes([
        attributes[offset],
        attributes[offset + 1],
    ]));
    let kind = u16::from_ne_bytes([attributes[offset + 2], attributes[offset + 3]]);
    let end = offset
        .checked_add(length)
        .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
    if length < 4 || end > attributes.len() {
        return Err(NetnsHelperErrorV1::NetlinkRejected);
    }
    Ok((length, kind))
}

fn next_attribute_offset(offset: usize, length: usize) -> Result<usize, NetnsHelperErrorV1> {
    let next = offset
        .checked_add(align4(length))
        .ok_or(NetnsHelperErrorV1::NetlinkRejected)?;
    Ok(next)
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

    const TEST_PORT_ID: u32 = 0x175a_39c1;

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
            flags: NLM_F_MULTI,
            sequence: SEQUENCE,
            port_id: TEST_PORT_ID,
        };
        let mut messages = (0..MAX_DUMP_MESSAGES)
            .map(|_| NetlinkMessage {
                payload: Vec::new(),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            parse_datagram(bytes_of(&header), RTM_NEWROUTE, TEST_PORT_ID, &mut messages,),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        Ok(())
    }

    #[test]
    fn interrupted_filtered_and_unexpected_dump_records_reject() {
        for flags in [NLM_F_DUMP_INTR, NLM_F_DUMP_FILTERED] {
            assert_eq!(
                parse_datagram(
                    &done_datagram(TEST_PORT_ID, NLM_F_MULTI | flags, 0),
                    RTM_NEWROUTE,
                    TEST_PORT_ID,
                    &mut Vec::new(),
                ),
                Err(NetnsHelperErrorV1::NetlinkRejected)
            );
        }

        let unexpected = NetlinkHeader {
            length: header_size_for_test(),
            message_type: RTM_NEWADDR,
            flags: NLM_F_MULTI,
            sequence: SEQUENCE,
            port_id: TEST_PORT_ID,
        };
        let done = done_datagram(TEST_PORT_ID, NLM_F_MULTI, 0);
        let mut datagram = bytes_of(&unexpected).to_vec();
        datagram.extend_from_slice(&done);
        assert_eq!(
            parse_datagram(&datagram, RTM_NEWROUTE, TEST_PORT_ID, &mut Vec::new(),),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );

        assert_eq!(
            parse_datagram(
                &done_datagram(TEST_PORT_ID ^ 1, NLM_F_MULTI, 0),
                RTM_NEWROUTE,
                TEST_PORT_ID,
                &mut Vec::new(),
            ),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );

        let mut trailing_after_done = done;
        trailing_after_done.extend_from_slice(bytes_of(&unexpected));
        assert_eq!(
            parse_datagram(
                &trailing_after_done,
                RTM_NEWROUTE,
                TEST_PORT_ID,
                &mut Vec::new(),
            ),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
    }

    #[test]
    fn done_requires_multipart_and_exact_zero_status() {
        assert_eq!(
            parse_datagram(
                &done_datagram(TEST_PORT_ID, NLM_F_MULTI, 0),
                RTM_NEWROUTE,
                TEST_PORT_ID,
                &mut Vec::new(),
            ),
            Ok(true)
        );
        for rejected in [
            done_datagram(TEST_PORT_ID, 0, 0),
            done_datagram(TEST_PORT_ID, NLM_F_MULTI, -1),
            done_without_status_datagram(),
            truncated_done_status_datagram(),
        ] {
            assert_eq!(
                parse_datagram(&rejected, RTM_NEWROUTE, TEST_PORT_ID, &mut Vec::new(),),
                Err(NetnsHelperErrorV1::NetlinkRejected)
            );
        }
    }

    #[test]
    fn kernel_sender_identity_fields_are_active_witnesses() -> Result<(), NetnsHelperErrorV1> {
        let length = u32::try_from(size_of::<libc::sockaddr_nl>())
            .map_err(|_| NetnsHelperErrorV1::NetlinkRejected)?;
        let mut sender: libc::sockaddr_nl = unsafe { zeroed() };
        sender.nl_family = c_int_u16(libc::AF_NETLINK)?;
        assert_eq!(require_kernel_sender(&sender, length), Ok(()));

        sender.nl_pid = 1;
        assert_eq!(
            require_kernel_sender(&sender, length),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        sender.nl_pid = 0;
        sender.nl_groups = 1;
        assert_eq!(
            require_kernel_sender(&sender, length),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        sender.nl_groups = 0;
        assert_eq!(
            require_kernel_sender(&sender, length - 1),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        sender.nl_family = c_int_u16(libc::AF_UNIX)?;
        assert_eq!(
            require_kernel_sender(&sender, length),
            Err(NetnsHelperErrorV1::NetlinkRejected)
        );
        Ok(())
    }

    const fn header_size_for_test() -> u32 {
        16
    }

    fn done_datagram(port_id: u32, flags: u16, status: i32) -> Vec<u8> {
        let header = NetlinkHeader {
            length: header_size_for_test() + 4,
            message_type: NLMSG_DONE,
            flags,
            sequence: SEQUENCE,
            port_id,
        };
        let mut datagram = bytes_of(&header).to_vec();
        datagram.extend_from_slice(&status.to_ne_bytes());
        datagram
    }

    fn done_without_status_datagram() -> Vec<u8> {
        bytes_of(&NetlinkHeader {
            length: header_size_for_test(),
            message_type: NLMSG_DONE,
            flags: NLM_F_MULTI,
            sequence: SEQUENCE,
            port_id: TEST_PORT_ID,
        })
        .to_vec()
    }

    fn truncated_done_status_datagram() -> Vec<u8> {
        let mut datagram = bytes_of(&NetlinkHeader {
            length: header_size_for_test() + 4,
            message_type: NLMSG_DONE,
            flags: NLM_F_MULTI,
            sequence: SEQUENCE,
            port_id: TEST_PORT_ID,
        })
        .to_vec();
        datagram.extend_from_slice(&0_i16.to_ne_bytes());
        datagram
    }
}
