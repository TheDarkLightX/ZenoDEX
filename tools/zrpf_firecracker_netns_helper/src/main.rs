use std::io::{ErrorKind, Read, Write};

use zenodex_zrpf_firecracker_netns_helper_v1::{
    execute_request_with_kernel_v1, linux::close_unexpected_descriptors_v1,
    linux::LinuxNetnsKernelV1, REQUEST_BYTES_V1,
};

fn main() {
    if let Err(error) = run() {
        let _ = writeln!(std::io::stderr(), "zrpf_netns_rejected:{}", error.code());
        std::process::exit(2);
    }
}

fn run() -> Result<(), zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1> {
    close_unexpected_descriptors_v1()?;
    let mut request = Vec::with_capacity(REQUEST_BYTES_V1 + 1);
    std::io::stdin()
        .take(u64::try_from(REQUEST_BYTES_V1 + 1).map_err(|_| {
            zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected
        })?)
        .read_to_end(&mut request)
        .map_err(|_| zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected)?;
    let mut kernel = LinuxNetnsKernelV1::new()?;
    let response = execute_request_with_kernel_v1(&request, &mut kernel)?;
    write_protocol_response_v1(&response)
}

fn write_protocol_response_v1(
    response: &[u8],
) -> Result<(), zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1> {
    // Stdout is the fixed binary helper ABI. A direct descriptor write keeps
    // this transport distinct from the diagnostic logging path on stderr.
    let mut offset = 0_usize;
    while offset < response.len() {
        let remaining = &response[offset..];
        let written = unsafe {
            libc::write(
                libc::STDOUT_FILENO,
                remaining.as_ptr().cast(),
                remaining.len(),
            )
        };
        if written < 0 {
            if std::io::Error::last_os_error().kind() == ErrorKind::Interrupted {
                continue;
            }
            return Err(zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected);
        }
        let written = usize::try_from(written).map_err(|_| {
            zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected
        })?;
        if written == 0 || written > remaining.len() {
            return Err(zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected);
        }
        offset = offset
            .checked_add(written)
            .ok_or(zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected)?;
    }
    Ok(())
}
