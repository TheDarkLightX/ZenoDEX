use crate::NetnsHelperErrorV1;

pub(super) fn install_netlink_only() -> Result<(), NetnsHelperErrorV1> {
    if unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) } != 0 {
        return Err(NetnsHelperErrorV1::SeccompRejected);
    }
    let architecture = match std::env::consts::ARCH {
        "x86_64" => 0xc000_003e,
        "aarch64" => 0xc000_00b7,
        _ => return Err(NetnsHelperErrorV1::SeccompRejected),
    };
    let mut filters = filters(architecture)?;
    let program = libc::sock_fprog {
        len: u16::try_from(filters.len()).map_err(|_| NetnsHelperErrorV1::SeccompRejected)?,
        filter: filters.as_mut_ptr(),
    };
    let result = unsafe {
        libc::syscall(
            libc::SYS_seccomp,
            libc::SECCOMP_SET_MODE_FILTER,
            0_u32,
            core::ptr::from_ref(&program),
        )
    };
    if result != 0 {
        return Err(NetnsHelperErrorV1::SeccompRejected);
    }
    Ok(())
}

fn filters(architecture: u32) -> Result<[libc::sock_filter; 24], NetnsHelperErrorV1> {
    let socket = syscall_number(libc::SYS_socket)?;
    let socketpair = syscall_number(libc::SYS_socketpair)?;
    let connect = syscall_number(libc::SYS_connect)?;
    let clone = syscall_number(libc::SYS_clone)?;
    let clone3 = syscall_number(libc::SYS_clone3)?;
    let fork = syscall_number(libc::SYS_fork)?;
    let vfork = syscall_number(libc::SYS_vfork)?;
    let operation_not_permitted = constant_u32(libc::EPERM)?;
    let address_family_netlink = constant_u32(libc::AF_NETLINK)?;
    let socket_raw = constant_u32(libc::SOCK_RAW)?;
    let route_netlink = constant_u32(libc::NETLINK_ROUTE)?;
    Ok([
        statement(0x20, 4),
        jump(0x15, architecture, 1, 0),
        statement(0x06, 0x8000_0000),
        statement(0x20, 0),
        jump(0x15, socket, 8, 0),
        jump(0x15, socketpair, 6, 0),
        jump(0x15, connect, 5, 0),
        jump(0x15, clone, 4, 0),
        jump(0x15, clone3, 3, 0),
        jump(0x15, fork, 2, 0),
        jump(0x15, vfork, 1, 0),
        statement(0x06, 0x7fff_0000),
        statement(0x06, 0x0005_0000 | operation_not_permitted),
        statement(0x20, 16),
        jump(0x15, address_family_netlink, 1, 0),
        statement(0x06, 0x0005_0000 | operation_not_permitted),
        statement(0x20, 24),
        statement(0x54, 0x0f),
        jump(0x15, socket_raw, 1, 0),
        statement(0x06, 0x0005_0000 | operation_not_permitted),
        statement(0x20, 32),
        jump(0x15, route_netlink, 1, 0),
        statement(0x06, 0x0005_0000 | operation_not_permitted),
        statement(0x06, 0x7fff_0000),
    ])
}

fn syscall_number(value: libc::c_long) -> Result<u32, NetnsHelperErrorV1> {
    u32::try_from(value).map_err(|_| NetnsHelperErrorV1::SeccompRejected)
}

fn constant_u32(value: libc::c_int) -> Result<u32, NetnsHelperErrorV1> {
    u32::try_from(value).map_err(|_| NetnsHelperErrorV1::SeccompRejected)
}

const fn statement(code: u16, value: u32) -> libc::sock_filter {
    libc::sock_filter {
        code,
        jt: 0,
        jf: 0,
        k: value,
    }
}

const fn jump(code: u16, value: u32, jt: u8, jf: u8) -> libc::sock_filter {
    libc::sock_filter {
        code,
        jt,
        jf,
        k: value,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ARCH: u32 = 0xc000_003e;
    const ALLOW: u32 = 0x7fff_0000;
    const KILL: u32 = 0x8000_0000;

    #[test]
    fn only_route_netlink_socket_is_allowed() -> Result<(), String> {
        let errno =
            0x0005_0000 | u32::try_from(libc::EPERM).map_err(|_| "EPERM is negative".to_owned())?;
        assert_eq!(evaluate(libc::SYS_read, ARCH, [0, 0, 0])?, ALLOW);
        assert_eq!(evaluate(libc::SYS_connect, ARCH, [0, 0, 0])?, errno);
        assert_eq!(evaluate(libc::SYS_socketpair, ARCH, [0, 0, 0])?, errno);
        for syscall in [
            libc::SYS_clone,
            libc::SYS_clone3,
            libc::SYS_fork,
            libc::SYS_vfork,
        ] {
            assert_eq!(evaluate(syscall, ARCH, [0, 0, 0])?, errno);
        }
        assert_eq!(evaluate(libc::SYS_socket, ARCH ^ 1, [0, 0, 0])?, KILL);
        assert_eq!(
            evaluate(
                libc::SYS_socket,
                ARCH,
                [
                    test_u64(libc::AF_NETLINK)?,
                    test_u64(libc::SOCK_RAW | libc::SOCK_CLOEXEC)?,
                    test_u64(libc::NETLINK_ROUTE)?,
                ],
            )?,
            ALLOW
        );
        for arguments in [
            [
                test_u64(libc::AF_INET)?,
                test_u64(libc::SOCK_RAW)?,
                test_u64(libc::NETLINK_ROUTE)?,
            ],
            [
                test_u64(libc::AF_NETLINK)?,
                test_u64(libc::SOCK_DGRAM)?,
                test_u64(libc::NETLINK_ROUTE)?,
            ],
            [
                test_u64(libc::AF_NETLINK)?,
                test_u64(libc::SOCK_RAW)?,
                test_u64(libc::NETLINK_USERSOCK)?,
            ],
        ] {
            assert_eq!(evaluate(libc::SYS_socket, ARCH, arguments)?, errno);
        }
        Ok(())
    }

    #[test]
    fn installed_filter_allows_real_kernel_route_dumps() -> Result<(), NetnsHelperErrorV1> {
        install_netlink_only()?;
        super::super::netlink::smoke_real_kernel_dumps_under_filter()
    }

    fn evaluate(
        number: libc::c_long,
        architecture: u32,
        arguments: [u64; 3],
    ) -> Result<u32, String> {
        let program = filters(ARCH).map_err(|error| error.to_string())?;
        let mut accumulator = 0_u32;
        let mut index = 0_usize;
        loop {
            let instruction = program[index];
            match instruction.code {
                0x20 => {
                    accumulator = match instruction.k {
                        0 => u32::try_from(number)
                            .map_err(|_| "syscall number is negative".to_owned())?,
                        4 => architecture,
                        16 => u32::try_from(arguments[0])
                            .map_err(|_| "argument zero exceeds u32".to_owned())?,
                        24 => u32::try_from(arguments[1])
                            .map_err(|_| "argument one exceeds u32".to_owned())?,
                        32 => u32::try_from(arguments[2])
                            .map_err(|_| "argument two exceeds u32".to_owned())?,
                        _ => return Err("unexpected seccomp load offset".to_owned()),
                    };
                    index += 1;
                }
                0x15 => {
                    index += if accumulator == instruction.k {
                        usize::from(instruction.jt) + 1
                    } else {
                        usize::from(instruction.jf) + 1
                    };
                }
                0x54 => {
                    accumulator &= instruction.k;
                    index += 1;
                }
                0x06 => return Ok(instruction.k),
                _ => return Err("unexpected seccomp opcode".to_owned()),
            }
        }
    }

    fn test_u64(value: libc::c_int) -> Result<u64, String> {
        u64::try_from(value).map_err(|_| "test constant is negative".to_owned())
    }
}
