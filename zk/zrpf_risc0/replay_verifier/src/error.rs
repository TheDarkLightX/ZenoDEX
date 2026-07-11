#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayError {
    Usage,
    BundleDirectory,
    BundleInventory,
    #[cfg(not(unix))]
    UnsupportedPlatform,
    ReceiptArtifact(&'static str),
    ReceiptArtifactBinding(&'static str),
    ReceiptDecode(&'static str),
    ReceiptNonCanonical(&'static str),
    ReceiptVerification(&'static str, &'static str),
    StructuralComposition(&'static str),
    RootBinding,
    MutationShape,
    MutationAccepted,
    MutationRejectClass(&'static str, &'static str),
    ReportEncoding,
}

impl ReplayError {
    pub(crate) const fn code(self) -> &'static str {
        match self {
            Self::Usage => "usage",
            Self::BundleDirectory => "bundle_directory",
            Self::BundleInventory => "bundle_inventory",
            #[cfg(not(unix))]
            Self::UnsupportedPlatform => "unsupported_platform",
            Self::ReceiptArtifact(_) => "receipt_artifact",
            Self::ReceiptArtifactBinding(_) => "receipt_artifact_binding",
            Self::ReceiptDecode(_) => "receipt_decode",
            Self::ReceiptNonCanonical(_) => "receipt_noncanonical",
            Self::ReceiptVerification(_, _) => "receipt_verification",
            Self::StructuralComposition(_) => "structural_composition",
            Self::RootBinding => "root_binding",
            Self::MutationShape => "mutation_shape",
            Self::MutationAccepted => "mutation_accepted",
            Self::MutationRejectClass(_, _) => "mutation_reject_class",
            Self::ReportEncoding => "report_encoding",
        }
    }

    pub(crate) const fn context(self) -> &'static str {
        match self {
            Self::ReceiptArtifact(context)
            | Self::ReceiptArtifactBinding(context)
            | Self::ReceiptDecode(context)
            | Self::ReceiptNonCanonical(context)
            | Self::StructuralComposition(context) => context,
            Self::ReceiptVerification(context, _) => context,
            Self::MutationRejectClass(context, _) => context,
            _ => "replay",
        }
    }

    pub(crate) const fn verifier_code(self) -> Option<&'static str> {
        match self {
            Self::ReceiptVerification(_, code) | Self::MutationRejectClass(_, code) => Some(code),
            _ => None,
        }
    }
}
