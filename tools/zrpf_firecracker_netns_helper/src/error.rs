use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetnsHelperErrorV1 {
    RequestSize,
    RequestMagic,
    RequestVersion(u16),
    RequestOperation(u16),
    RequestFlags,
    TrustedUid,
    NamespaceRootLength,
    NamespaceNameLength,
    NamespaceRootEncoding,
    NamespaceNameEncoding,
    NamespaceRootCanonical,
    NamespaceNameCanonical,
    NamespaceRootPadding,
    NamespaceNamePadding,
    RequestReserved,
    RequestDigest,
    UnexpectedIdentity,
    MissingIdentity,
    NamespaceIdentityMismatch,
    ProcessMembershipNotEmpty,
    NonLoopbackAddressPresent,
    NonLoopbackRoutePresent,
    RootDirectoryRejected,
    NamespaceAlreadyExists,
    NamespaceOpenRejected,
    NamespaceMountRejected,
    NamespaceTypeRejected,
    NamespaceOwnershipRejected,
    NamespaceCreateRejected,
    NamespaceSetnsRejected,
    NamespaceDestroyRejected,
    NamespaceCleanupRejected,
    NamespaceAbsenceRejected,
    NetlinkRejected,
    SeccompRejected,
    ResponseInvariant,
    ResponseEncoding,
    IoRejected,
}

impl NetnsHelperErrorV1 {
    pub fn code(&self) -> &'static str {
        match self {
            Self::RequestSize => "request_size",
            Self::RequestMagic => "request_magic",
            Self::RequestVersion(_) => "request_version",
            Self::RequestOperation(_) => "request_operation",
            Self::RequestFlags => "request_flags",
            Self::TrustedUid => "trusted_uid",
            Self::NamespaceRootLength => "namespace_root_length",
            Self::NamespaceNameLength => "namespace_name_length",
            Self::NamespaceRootEncoding => "namespace_root_encoding",
            Self::NamespaceNameEncoding => "namespace_name_encoding",
            Self::NamespaceRootCanonical => "namespace_root_canonical",
            Self::NamespaceNameCanonical => "namespace_name_canonical",
            Self::NamespaceRootPadding => "namespace_root_padding",
            Self::NamespaceNamePadding => "namespace_name_padding",
            Self::RequestReserved => "request_reserved",
            Self::RequestDigest => "request_digest",
            Self::UnexpectedIdentity => "unexpected_identity",
            Self::MissingIdentity => "missing_identity",
            Self::NamespaceIdentityMismatch => "namespace_identity_mismatch",
            Self::ProcessMembershipNotEmpty => "process_membership_not_empty",
            Self::NonLoopbackAddressPresent => "non_loopback_address_present",
            Self::NonLoopbackRoutePresent => "non_loopback_route_present",
            Self::RootDirectoryRejected => "root_directory_rejected",
            Self::NamespaceAlreadyExists => "namespace_already_exists",
            Self::NamespaceOpenRejected => "namespace_open_rejected",
            Self::NamespaceMountRejected => "namespace_mount_rejected",
            Self::NamespaceTypeRejected => "namespace_type_rejected",
            Self::NamespaceOwnershipRejected => "namespace_ownership_rejected",
            Self::NamespaceCreateRejected => "namespace_create_rejected",
            Self::NamespaceSetnsRejected => "namespace_setns_rejected",
            Self::NamespaceDestroyRejected => "namespace_destroy_rejected",
            Self::NamespaceCleanupRejected => "namespace_cleanup_rejected",
            Self::NamespaceAbsenceRejected => "namespace_absence_rejected",
            Self::NetlinkRejected => "netlink_rejected",
            Self::SeccompRejected => "seccomp_rejected",
            Self::ResponseInvariant => "response_invariant",
            Self::ResponseEncoding => "response_encoding",
            Self::IoRejected => "io_rejected",
        }
    }
}

impl fmt::Display for NetnsHelperErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code())
    }
}
