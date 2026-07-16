use std::io::{Read, Write};

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
    // This fixed 256-byte binary protocol response contains only bounded
    // observations and SHA-256 commitments. It contains no namespace path or
    // name bytes, and stdout is the helper ABI rather than a diagnostic log.
    std::io::stdout()
        .write_all(&response) // codeql[rust/cleartext-logging]
        .and_then(|()| std::io::stdout().flush())
        .map_err(|_| zenodex_zrpf_firecracker_netns_helper_v1::NetnsHelperErrorV1::IoRejected)
}
