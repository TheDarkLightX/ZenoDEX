use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_assumption_manifest_v1, decode_exact_proof_shape_registry_v1,
    decode_exact_proof_shape_v1, encode_assumption_manifest_v1, encode_proof_shape_registry_v1,
    encode_proof_shape_v1, resolve_assumptions_v1, AllowedChildBindingIdV1,
    AllowedChildBindingInputV1, AssumptionManifestInputV1, AssumptionManifestV1,
    AssumptionRequirementInputV1, CommitmentV3, ProfileIdV3, ProgramIdV3,
    ProofResourceCeilingsInputV1, ProofResourceCeilingsV1, ProofShapeErrorV1, ProofShapeIdV1,
    ProofShapeInputV1, ProofShapeKindV1, ProofShapeRegistrationV1, ProofShapeRegistryV1,
    ProofShapeV1, ResolvedChildClaimInputV1, ResolvedChildClaimV1, MAX_ALLOWED_CHILD_BINDINGS_V1,
    MAX_ASSUMPTION_MANIFEST_BYTES_V1, MAX_PROOF_SHAPE_BYTES_V1, MAX_PROOF_SHAPE_REGISTRY_BYTES_V1,
    MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1,
};

fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

fn child_shape(seed: u8) -> ProofShapeIdV1 {
    ProofShapeIdV1::new(bytes(seed)).unwrap()
}

fn binding(seed: u8, max_child_journal_bytes: u64) -> AllowedChildBindingInputV1 {
    AllowedChildBindingInputV1 {
        child_shape_id: child_shape(seed),
        child_program_id: ProgramIdV3::new(bytes(seed.wrapping_add(20))).unwrap(),
        child_profile_id: ProfileIdV3::new(bytes(seed.wrapping_add(40))).unwrap(),
        max_child_journal_bytes,
    }
}

fn requirement(
    slot: u16,
    allowed_child_binding_id: AllowedChildBindingIdV1,
    claim_seed: u8,
    journal_seed: u8,
) -> AssumptionRequirementInputV1 {
    AssumptionRequirementInputV1 {
        slot,
        allowed_child_binding_id,
        expected_verification_claim_hash: commitment(claim_seed),
        expected_child_journal_hash: commitment(journal_seed),
    }
}

fn aggregate_resources(
    max_assumptions: u64,
    max_total_child_journal_bytes: u64,
) -> ProofResourceCeilingsV1 {
    ProofResourceCeilingsV1::new(ProofResourceCeilingsInputV1 {
        max_input_bytes: 1_048_576,
        max_journal_bytes: 16_384,
        max_proof_bytes: 4_194_304,
        max_cycles: 5_000_000,
        max_memory_bytes: 536_870_912,
        max_assumptions,
        max_total_child_journal_bytes,
    })
    .unwrap()
}

fn leaf_resources() -> ProofResourceCeilingsV1 {
    ProofResourceCeilingsV1::new(ProofResourceCeilingsInputV1 {
        max_input_bytes: 1024,
        max_journal_bytes: 1024,
        max_proof_bytes: 4096,
        max_cycles: 10_000,
        max_memory_bytes: 1_048_576,
        max_assumptions: 0,
        max_total_child_journal_bytes: 0,
    })
    .unwrap()
}

fn aggregate_shape_input() -> ProofShapeInputV1 {
    ProofShapeInputV1 {
        shape_kind: ProofShapeKindV1::Aggregate,
        program_id: ProgramIdV3::new(bytes(1)).unwrap(),
        profile_id: ProfileIdV3::new(bytes(2)).unwrap(),
        resource_ceilings: aggregate_resources(4, 32_768),
        allowed_child_bindings: vec![binding(11, 8_192), binding(12, 12_288)],
    }
}

fn fixture() -> (
    ProofShapeV1,
    AssumptionManifestV1,
    Vec<ResolvedChildClaimV1>,
) {
    let shape = ProofShapeV1::derive(aggregate_shape_input()).unwrap();
    let bindings = shape.allowed_child_bindings();
    let manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![
            requirement(1, bindings[1].binding_id(), 101, 72),
            requirement(0, bindings[0].binding_id(), 100, 71),
        ],
    })
    .unwrap();
    let claims = manifest
        .required_assumptions()
        .iter()
        .rev()
        .map(|requirement| {
            let allowed = shape
                .allowed_child_bindings()
                .iter()
                .find(|value| value.binding_id() == requirement.allowed_child_binding_id())
                .unwrap();
            ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
                assumption_id: requirement.assumption_id(),
                verification_claim_hash: requirement.expected_verification_claim_hash(),
                child_shape_id: allowed.child_shape_id(),
                child_program_id: allowed.child_program_id(),
                child_profile_id: allowed.child_profile_id(),
                child_journal_hash: requirement.expected_child_journal_hash(),
                child_journal_bytes: allowed.max_child_journal_bytes() / 2,
            })
            .unwrap()
        })
        .collect();
    (shape, manifest, claims)
}

#[test]
fn canonical_shape_manifest_registry_and_exact_resolution_round_trip() {
    let (shape, manifest, claims) = fixture();
    assert_eq!(shape.allowed_child_bindings().len(), 2);
    assert!(
        shape.allowed_child_bindings()[0].binding_id()
            < shape.allowed_child_bindings()[1].binding_id()
    );
    assert_eq!(manifest.required_assumptions()[0].slot(), 0);
    assert_eq!(manifest.required_assumptions()[1].slot(), 1);

    let shape_bytes = encode_proof_shape_v1(&shape).unwrap();
    assert_eq!(decode_exact_proof_shape_v1(&shape_bytes).unwrap(), shape);
    let manifest_bytes = encode_assumption_manifest_v1(&manifest).unwrap();
    assert_eq!(
        decode_exact_assumption_manifest_v1(&manifest_bytes).unwrap(),
        manifest
    );

    let registry = ProofShapeRegistryV1::derive(vec![ProofShapeRegistrationV1::new(
        shape.clone(),
        manifest.clone(),
    )
    .unwrap()])
    .unwrap();
    let registry_bytes = encode_proof_shape_registry_v1(&registry).unwrap();
    assert_eq!(
        decode_exact_proof_shape_registry_v1(&registry_bytes).unwrap(),
        registry
    );
    assert_eq!(registry.shape(shape.shape_id()), Some(&shape));
    assert_eq!(
        registry.assumption_manifest(manifest.manifest_id()),
        Some(&manifest)
    );

    let resolution = registry
        .resolve(manifest.manifest_id(), claims.clone())
        .unwrap();
    assert_eq!(resolution.claims().len(), claims.len());
    assert_eq!(
        resolution.claims()[0].assumption_id(),
        manifest.required_assumptions()[0].assumption_id()
    );
    assert!(!shape.proof_authority());
    assert!(!shape.release_authority());
    assert!(!shape.settlement_authority());
    assert!(!shape.production_authority());
    assert!(!manifest.proof_authority());
    assert!(!manifest.release_authority());
    assert!(!manifest.settlement_authority());
    assert!(!manifest.production_authority());
    for claim in &claims {
        assert!(!claim.proof_authority());
        assert!(!claim.release_authority());
        assert!(!claim.settlement_authority());
        assert!(!claim.production_authority());
    }
    assert!(!resolution.proof_authority());
    assert!(!resolution.release_authority());
    assert!(!resolution.settlement_authority());
    assert!(!resolution.production_authority());
    assert!(!registry.proof_authority());
    assert!(!registry.release_authority());
    assert!(!registry.settlement_authority());
    assert!(!registry.production_authority());
}

#[test]
fn caller_order_does_not_change_canonical_contracts() {
    let (shape, manifest, claims) = fixture();

    let mut reversed_shape_input = aggregate_shape_input();
    reversed_shape_input.allowed_child_bindings.reverse();
    assert_eq!(ProofShapeV1::derive(reversed_shape_input).unwrap(), shape);

    let forward_manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: shape
            .allowed_child_bindings()
            .iter()
            .enumerate()
            .map(|(slot, binding)| {
                requirement(
                    u16::try_from(slot).unwrap(),
                    binding.binding_id(),
                    100_u8.wrapping_add(u8::try_from(slot).unwrap()),
                    71_u8.wrapping_add(u8::try_from(slot).unwrap()),
                )
            })
            .collect(),
    })
    .unwrap();
    assert_eq!(forward_manifest, manifest);

    let forward_resolution = resolve_assumptions_v1(&shape, &manifest, claims.clone()).unwrap();
    let mut reversed_claims = claims;
    reversed_claims.reverse();
    let reversed_resolution = resolve_assumptions_v1(&shape, &manifest, reversed_claims).unwrap();
    assert_eq!(forward_resolution, reversed_resolution);

    let leaf = ProofShapeV1::derive(ProofShapeInputV1 {
        shape_kind: ProofShapeKindV1::Leaf,
        program_id: ProgramIdV3::new(bytes(3)).unwrap(),
        profile_id: ProfileIdV3::new(bytes(4)).unwrap(),
        resource_ceilings: leaf_resources(),
        allowed_child_bindings: vec![],
    })
    .unwrap();
    let leaf_manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: leaf.shape_id(),
        required_assumptions: vec![],
    })
    .unwrap();
    let aggregate_registration = ProofShapeRegistrationV1::new(shape, manifest).unwrap();
    let leaf_registration = ProofShapeRegistrationV1::new(leaf, leaf_manifest).unwrap();
    let forward_registry = ProofShapeRegistryV1::derive(vec![
        aggregate_registration.clone(),
        leaf_registration.clone(),
    ])
    .unwrap();
    let reverse_registry =
        ProofShapeRegistryV1::derive(vec![leaf_registration, aggregate_registration]).unwrap();
    assert_eq!(forward_registry, reverse_registry);
}

#[test]
fn exact_resolution_rejects_missing_surplus_and_duplicate_claims() {
    let (shape, manifest, claims) = fixture();
    assert!(matches!(
        resolve_assumptions_v1(&shape, &manifest, claims[..1].to_vec()),
        Err(ProofShapeErrorV1::UnresolvedAssumption { .. })
    ));

    let mut surplus = claims.clone();
    surplus.push(
        ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
            assumption_id: zenodex_zrpf_protocol_v3::AssumptionIdV1::new(bytes(90)).unwrap(),
            verification_claim_hash: commitment(91),
            child_shape_id: child_shape(92),
            child_program_id: ProgramIdV3::new(bytes(93)).unwrap(),
            child_profile_id: ProfileIdV3::new(bytes(94)).unwrap(),
            child_journal_hash: commitment(95),
            child_journal_bytes: 1,
        })
        .unwrap(),
    );
    assert!(matches!(
        resolve_assumptions_v1(&shape, &manifest, surplus),
        Err(ProofShapeErrorV1::SurplusResolvedClaim { .. })
    ));

    let mut duplicate_assumption = claims.clone();
    duplicate_assumption[1] = ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
        assumption_id: duplicate_assumption[0].assumption_id(),
        verification_claim_hash: commitment(96),
        child_shape_id: duplicate_assumption[1].child_shape_id(),
        child_program_id: duplicate_assumption[1].child_program_id(),
        child_profile_id: duplicate_assumption[1].child_profile_id(),
        child_journal_hash: duplicate_assumption[1].child_journal_hash(),
        child_journal_bytes: duplicate_assumption[1].child_journal_bytes(),
    })
    .unwrap();
    assert_eq!(
        resolve_assumptions_v1(&shape, &manifest, duplicate_assumption),
        Err(ProofShapeErrorV1::DuplicateResolvedAssumption)
    );

    let mut duplicate_claim = claims;
    duplicate_claim[1] = ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
        assumption_id: duplicate_claim[1].assumption_id(),
        verification_claim_hash: duplicate_claim[0].verification_claim_hash(),
        child_shape_id: duplicate_claim[1].child_shape_id(),
        child_program_id: duplicate_claim[1].child_program_id(),
        child_profile_id: duplicate_claim[1].child_profile_id(),
        child_journal_hash: duplicate_claim[1].child_journal_hash(),
        child_journal_bytes: duplicate_claim[1].child_journal_bytes(),
    })
    .unwrap();
    assert_eq!(
        resolve_assumptions_v1(&shape, &manifest, duplicate_claim),
        Err(ProofShapeErrorV1::DuplicateVerificationClaim)
    );

    let (_, _, mut duplicate_journal) = fixture();
    duplicate_journal[1] = ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
        assumption_id: duplicate_journal[1].assumption_id(),
        verification_claim_hash: duplicate_journal[1].verification_claim_hash(),
        child_shape_id: duplicate_journal[1].child_shape_id(),
        child_program_id: duplicate_journal[1].child_program_id(),
        child_profile_id: duplicate_journal[1].child_profile_id(),
        child_journal_hash: duplicate_journal[0].child_journal_hash(),
        child_journal_bytes: duplicate_journal[1].child_journal_bytes(),
    })
    .unwrap();
    assert_eq!(
        resolve_assumptions_v1(&shape, &manifest, duplicate_journal),
        Err(ProofShapeErrorV1::DuplicateResolvedChildJournal)
    );
}

#[test]
fn exact_resolution_rejects_every_child_binding_substitution() {
    let (shape, manifest, claims) = fixture();
    let original = &claims[0];
    let variants = [
        ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
            assumption_id: original.assumption_id(),
            verification_claim_hash: original.verification_claim_hash(),
            child_shape_id: child_shape(70),
            child_program_id: original.child_program_id(),
            child_profile_id: original.child_profile_id(),
            child_journal_hash: original.child_journal_hash(),
            child_journal_bytes: original.child_journal_bytes(),
        })
        .unwrap(),
        ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
            assumption_id: original.assumption_id(),
            verification_claim_hash: original.verification_claim_hash(),
            child_shape_id: original.child_shape_id(),
            child_program_id: ProgramIdV3::new(bytes(71)).unwrap(),
            child_profile_id: original.child_profile_id(),
            child_journal_hash: original.child_journal_hash(),
            child_journal_bytes: original.child_journal_bytes(),
        })
        .unwrap(),
        ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
            assumption_id: original.assumption_id(),
            verification_claim_hash: commitment(74),
            child_shape_id: original.child_shape_id(),
            child_program_id: original.child_program_id(),
            child_profile_id: original.child_profile_id(),
            child_journal_hash: original.child_journal_hash(),
            child_journal_bytes: original.child_journal_bytes(),
        })
        .unwrap(),
        ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
            assumption_id: original.assumption_id(),
            verification_claim_hash: original.verification_claim_hash(),
            child_shape_id: original.child_shape_id(),
            child_program_id: original.child_program_id(),
            child_profile_id: ProfileIdV3::new(bytes(72)).unwrap(),
            child_journal_hash: original.child_journal_hash(),
            child_journal_bytes: original.child_journal_bytes(),
        })
        .unwrap(),
        ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
            assumption_id: original.assumption_id(),
            verification_claim_hash: original.verification_claim_hash(),
            child_shape_id: original.child_shape_id(),
            child_program_id: original.child_program_id(),
            child_profile_id: original.child_profile_id(),
            child_journal_hash: commitment(73),
            child_journal_bytes: original.child_journal_bytes(),
        })
        .unwrap(),
    ];
    let expected = [
        ProofShapeErrorV1::ChildShapeMismatch,
        ProofShapeErrorV1::ChildProgramMismatch,
        ProofShapeErrorV1::VerificationClaimMismatch,
        ProofShapeErrorV1::ChildProfileMismatch,
        ProofShapeErrorV1::ChildJournalMismatch,
    ];
    for (variant, expected_error) in variants.into_iter().zip(expected) {
        let mut mutated = claims.clone();
        mutated[0] = variant;
        assert_eq!(
            resolve_assumptions_v1(&shape, &manifest, mutated),
            Err(expected_error)
        );
    }

    let required_binding_id = manifest
        .required_assumptions()
        .iter()
        .find(|requirement| requirement.assumption_id() == claims[0].assumption_id())
        .unwrap()
        .allowed_child_binding_id();
    let allowed = shape
        .allowed_child_bindings()
        .iter()
        .find(|binding| binding.binding_id() == required_binding_id)
        .unwrap()
        .max_child_journal_bytes();
    let mut oversized = claims;
    oversized[0] = ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
        assumption_id: oversized[0].assumption_id(),
        verification_claim_hash: oversized[0].verification_claim_hash(),
        child_shape_id: oversized[0].child_shape_id(),
        child_program_id: oversized[0].child_program_id(),
        child_profile_id: oversized[0].child_profile_id(),
        child_journal_hash: oversized[0].child_journal_hash(),
        child_journal_bytes: allowed + 1,
    })
    .unwrap();
    assert!(matches!(
        resolve_assumptions_v1(&shape, &manifest, oversized),
        Err(ProofShapeErrorV1::ChildJournalBytesExceeded { .. })
    ));
}

#[test]
fn shape_manifest_and_registry_reject_duplicates_and_resource_excess() {
    assert_eq!(
        ProofShapeRegistryV1::derive(vec![]),
        Err(ProofShapeErrorV1::EmptyRegistry)
    );

    let mut duplicate_binding = aggregate_shape_input();
    duplicate_binding.allowed_child_bindings[1] =
        duplicate_binding.allowed_child_bindings[0].clone();
    assert_eq!(
        ProofShapeV1::derive(duplicate_binding),
        Err(ProofShapeErrorV1::DuplicateAllowedChildBinding)
    );

    let mut too_many = aggregate_shape_input();
    too_many.allowed_child_bindings = (0..=MAX_ALLOWED_CHILD_BINDINGS_V1)
        .map(|index| binding(u8::try_from(index + 1).unwrap(), 1))
        .collect();
    assert!(matches!(
        ProofShapeV1::derive(too_many),
        Err(ProofShapeErrorV1::TooManyAllowedChildBindings { .. })
    ));

    let (shape, manifest, _claims) = fixture();
    let bindings = shape.allowed_child_bindings();
    let duplicate_slot = AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![
            requirement(0, bindings[0].binding_id(), 110, 111),
            requirement(0, bindings[1].binding_id(), 112, 113),
        ],
    };
    assert_eq!(
        AssumptionManifestV1::derive(duplicate_slot),
        Err(ProofShapeErrorV1::DuplicateAssumptionSlot)
    );

    let repeated_required_binding = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![
            requirement(0, bindings[0].binding_id(), 114, 115),
            requirement(1, bindings[0].binding_id(), 116, 117),
        ],
    })
    .unwrap();
    ProofShapeRegistrationV1::new(shape.clone(), repeated_required_binding.clone()).unwrap();
    let repeated_binding = &bindings[0];
    let repeated_claims = repeated_required_binding
        .required_assumptions()
        .iter()
        .map(|required| {
            ResolvedChildClaimV1::new(ResolvedChildClaimInputV1 {
                assumption_id: required.assumption_id(),
                verification_claim_hash: required.expected_verification_claim_hash(),
                child_shape_id: repeated_binding.child_shape_id(),
                child_program_id: repeated_binding.child_program_id(),
                child_profile_id: repeated_binding.child_profile_id(),
                child_journal_hash: required.expected_child_journal_hash(),
                child_journal_bytes: repeated_binding.max_child_journal_bytes() / 2,
            })
            .unwrap()
        })
        .collect();
    assert_eq!(
        resolve_assumptions_v1(&shape, &repeated_required_binding, repeated_claims)
            .unwrap()
            .claims()
            .len(),
        2
    );

    let duplicate_expected_claim = AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![
            requirement(0, bindings[0].binding_id(), 118, 119),
            requirement(1, bindings[1].binding_id(), 118, 120),
        ],
    };
    assert_eq!(
        AssumptionManifestV1::derive(duplicate_expected_claim),
        Err(ProofShapeErrorV1::DuplicateExpectedVerificationClaim)
    );

    let duplicate_expected_journal = AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![
            requirement(0, bindings[0].binding_id(), 121, 122),
            requirement(1, bindings[1].binding_id(), 123, 122),
        ],
    };
    assert_eq!(
        AssumptionManifestV1::derive(duplicate_expected_journal),
        Err(ProofShapeErrorV1::DuplicateExpectedChildJournal)
    );

    let non_dense = AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![
            requirement(0, bindings[0].binding_id(), 124, 125),
            requirement(2, bindings[1].binding_id(), 126, 127),
        ],
    };
    assert_eq!(
        AssumptionManifestV1::derive(non_dense),
        Err(ProofShapeErrorV1::NonDenseAssumptionSlots)
    );

    let unallowed = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: shape.shape_id(),
        required_assumptions: vec![requirement(
            0,
            AllowedChildBindingIdV1::new(bytes(200)).unwrap(),
            128,
            129,
        )],
    })
    .unwrap();
    assert_eq!(
        ProofShapeRegistrationV1::new(shape.clone(), unallowed),
        Err(ProofShapeErrorV1::RequiredBindingNotAllowed)
    );

    let different_shape = ProofShapeV1::derive(ProofShapeInputV1 {
        program_id: ProgramIdV3::new(bytes(201)).unwrap(),
        ..aggregate_shape_input()
    })
    .unwrap();
    assert!(matches!(
        ProofShapeRegistrationV1::new(different_shape, manifest.clone()),
        Err(ProofShapeErrorV1::ProofShapeMismatch { .. })
    ));

    let duplicate_registration =
        ProofShapeRegistrationV1::new(shape.clone(), manifest.clone()).unwrap();
    assert_eq!(
        ProofShapeRegistryV1::derive(vec![duplicate_registration.clone(), duplicate_registration]),
        Err(ProofShapeErrorV1::DuplicateProofShape)
    );

    let too_many_registrations = (0..=MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1)
        .map(|index| {
            let seed = u8::try_from(index + 1).unwrap();
            let leaf = ProofShapeV1::derive(ProofShapeInputV1 {
                shape_kind: ProofShapeKindV1::Leaf,
                program_id: ProgramIdV3::new(bytes(seed)).unwrap(),
                profile_id: ProfileIdV3::new(bytes(seed.wrapping_add(64))).unwrap(),
                resource_ceilings: leaf_resources(),
                allowed_child_bindings: vec![],
            })
            .unwrap();
            let leaf_manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
                proof_shape_id: leaf.shape_id(),
                required_assumptions: vec![],
            })
            .unwrap();
            ProofShapeRegistrationV1::new(leaf, leaf_manifest).unwrap()
        })
        .collect();
    assert_eq!(
        ProofShapeRegistryV1::derive(too_many_registrations),
        Err(ProofShapeErrorV1::TooManyRegistryEntries {
            actual: MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1 + 1,
            maximum: MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1,
        })
    );

    let narrow_shape = ProofShapeV1::derive(ProofShapeInputV1 {
        resource_ceilings: aggregate_resources(1, 32_768),
        ..aggregate_shape_input()
    })
    .unwrap();
    let narrow_bindings = narrow_shape.allowed_child_bindings();
    let excessive_manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: narrow_shape.shape_id(),
        required_assumptions: vec![
            requirement(0, narrow_bindings[0].binding_id(), 130, 131),
            requirement(1, narrow_bindings[1].binding_id(), 132, 133),
        ],
    })
    .unwrap();
    assert_eq!(
        ProofShapeRegistrationV1::new(narrow_shape, excessive_manifest),
        Err(ProofShapeErrorV1::AssumptionCountCeilingExceeded {
            actual: 2,
            maximum: 1,
        })
    );

    let total_narrow_shape = ProofShapeV1::derive(ProofShapeInputV1 {
        resource_ceilings: aggregate_resources(4, 16_384),
        ..aggregate_shape_input()
    })
    .unwrap();
    let total_narrow_bindings = total_narrow_shape.allowed_child_bindings();
    let total_excessive_manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: total_narrow_shape.shape_id(),
        required_assumptions: vec![
            requirement(0, total_narrow_bindings[0].binding_id(), 134, 135),
            requirement(1, total_narrow_bindings[1].binding_id(), 136, 137),
        ],
    })
    .unwrap();
    assert_eq!(
        ProofShapeRegistrationV1::new(total_narrow_shape, total_excessive_manifest),
        Err(ProofShapeErrorV1::TotalChildJournalCeilingExceeded {
            actual: 20_480,
            maximum: 16_384,
        })
    );
}

#[test]
fn leaf_shape_requires_an_empty_manifest_and_no_child_resources() {
    let leaf = ProofShapeV1::derive(ProofShapeInputV1 {
        shape_kind: ProofShapeKindV1::Leaf,
        program_id: ProgramIdV3::new(bytes(3)).unwrap(),
        profile_id: ProfileIdV3::new(bytes(4)).unwrap(),
        resource_ceilings: leaf_resources(),
        allowed_child_bindings: vec![],
    })
    .unwrap();
    let manifest = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: leaf.shape_id(),
        required_assumptions: vec![],
    })
    .unwrap();
    let resolution = resolve_assumptions_v1(&leaf, &manifest, vec![]).unwrap();
    assert!(resolution.claims().is_empty());

    let mut invalid = aggregate_shape_input();
    invalid.shape_kind = ProofShapeKindV1::Leaf;
    assert_eq!(
        ProofShapeV1::derive(invalid),
        Err(ProofShapeErrorV1::LeafHasChildContract)
    );
}

#[test]
fn exact_codecs_reject_truncation_trailing_oversize_and_unknown_fields() {
    let (shape, manifest, _) = fixture();
    let registry = ProofShapeRegistryV1::derive(vec![ProofShapeRegistrationV1::new(
        shape.clone(),
        manifest.clone(),
    )
    .unwrap()])
    .unwrap();

    assert_codec_rejections(
        encode_proof_shape_v1(&shape).unwrap(),
        MAX_PROOF_SHAPE_BYTES_V1,
        decode_exact_proof_shape_v1,
    );
    assert_codec_rejections(
        encode_assumption_manifest_v1(&manifest).unwrap(),
        MAX_ASSUMPTION_MANIFEST_BYTES_V1,
        decode_exact_assumption_manifest_v1,
    );
    assert_codec_rejections(
        encode_proof_shape_registry_v1(&registry).unwrap(),
        MAX_PROOF_SHAPE_REGISTRY_BYTES_V1,
        decode_exact_proof_shape_registry_v1,
    );

    let mut shape_json = serde_json::to_value(&shape).unwrap();
    shape_json["publisher_note"] = serde_json::json!(true);
    assert!(serde_json::from_value::<ProofShapeV1>(shape_json).is_err());
    let mut manifest_json = serde_json::to_value(&manifest).unwrap();
    manifest_json["operator_note"] = serde_json::json!(true);
    assert!(serde_json::from_value::<AssumptionManifestV1>(manifest_json).is_err());

    let mut noncanonical_shape_json = serde_json::to_value(&shape).unwrap();
    noncanonical_shape_json["allowed_child_bindings"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert!(serde_json::from_value::<ProofShapeV1>(noncanonical_shape_json).is_err());

    let mut noncanonical_manifest_json = serde_json::to_value(&manifest).unwrap();
    noncanonical_manifest_json["required_assumptions"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert!(serde_json::from_value::<AssumptionManifestV1>(noncanonical_manifest_json).is_err());

    let mut forged_shape_id_json = serde_json::to_value(shape).unwrap();
    forged_shape_id_json["shape_id"] = serde_json::json!(bytes(250));
    assert!(serde_json::from_value::<ProofShapeV1>(forged_shape_id_json).is_err());
}

fn assert_codec_rejections<T>(
    bytes: Vec<u8>,
    maximum: usize,
    decode: fn(&[u8]) -> Result<T, ProofShapeErrorV1>,
) {
    assert!(decode(&[]).is_err());
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(matches!(
        decode(&trailing),
        Err(ProofShapeErrorV1::TrailingBytes)
    ));
    assert!(matches!(
        decode(&vec![0; maximum + 1]),
        Err(ProofShapeErrorV1::InputTooLarge { .. })
    ));
    assert!(decode(&bytes[..bytes.len() - 1]).is_err());
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn manual_binding_id(input: &AllowedChildBindingInputV1) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zkpf.allowed_child_binding_id.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(input.child_shape_id.as_bytes());
    hasher.update(input.child_program_id.as_bytes());
    hasher.update(input.child_profile_id.as_bytes());
    hasher.update(input.max_child_journal_bytes.to_be_bytes());
    hasher.finalize().into()
}

fn manual_shape_id(shape: &ProofShapeV1) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zkpf.proof_shape_id.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update([match shape.shape_kind() {
        ProofShapeKindV1::Leaf => 0,
        ProofShapeKindV1::Aggregate => 1,
    }]);
    hasher.update(shape.program_id().as_bytes());
    hasher.update(shape.profile_id().as_bytes());
    let resources = shape.resource_ceilings();
    for value in [
        resources.max_input_bytes(),
        resources.max_journal_bytes(),
        resources.max_proof_bytes(),
        resources.max_cycles(),
        resources.max_memory_bytes(),
        resources.max_assumptions(),
        resources.max_total_child_journal_bytes(),
    ] {
        hasher.update(value.to_be_bytes());
    }
    hasher.update(
        u16::try_from(shape.allowed_child_bindings().len())
            .unwrap()
            .to_be_bytes(),
    );
    for binding in shape.allowed_child_bindings() {
        hasher.update(binding.binding_id().as_bytes());
    }
    hasher.finalize().into()
}

fn manual_assumption_id(
    proof_shape_id: ProofShapeIdV1,
    requirement: &zenodex_zrpf_protocol_v3::AssumptionRequirementV1,
) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zkpf.assumption_id.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(proof_shape_id.as_bytes());
    hasher.update(requirement.slot().to_be_bytes());
    hasher.update(requirement.allowed_child_binding_id().as_bytes());
    hasher.update(requirement.expected_verification_claim_hash().as_bytes());
    hasher.update(requirement.expected_child_journal_hash().as_bytes());
    hasher.finalize().into()
}

fn manual_manifest_id(manifest: &AssumptionManifestV1) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zkpf.assumption_manifest_id.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(manifest.proof_shape_id().as_bytes());
    hasher.update(
        u16::try_from(manifest.required_assumptions().len())
            .unwrap()
            .to_be_bytes(),
    );
    for requirement in manifest.required_assumptions() {
        hasher.update(requirement.assumption_id().as_bytes());
    }
    hasher.finalize().into()
}

fn manual_resolution_id(resolution: &zenodex_zrpf_protocol_v3::AssumptionResolutionV1) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zkpf.assumption_resolution_id.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(resolution.proof_shape_id().as_bytes());
    hasher.update(resolution.assumption_manifest_id().as_bytes());
    hasher.update(
        u16::try_from(resolution.claims().len())
            .unwrap()
            .to_be_bytes(),
    );
    for claim in resolution.claims() {
        hasher.update(claim.assumption_id().as_bytes());
        hasher.update(claim.verification_claim_hash().as_bytes());
        hasher.update(claim.child_shape_id().as_bytes());
        hasher.update(claim.child_program_id().as_bytes());
        hasher.update(claim.child_profile_id().as_bytes());
        hasher.update(claim.child_journal_hash().as_bytes());
        hasher.update(claim.child_journal_bytes().to_be_bytes());
    }
    hasher.finalize().into()
}

fn manual_registry_id(registry: &ProofShapeRegistryV1) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zkpf.proof_shape_registry_id.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(
        u16::try_from(registry.registrations().len())
            .unwrap()
            .to_be_bytes(),
    );
    for registration in registry.registrations() {
        hasher.update(registration.shape().shape_id().as_bytes());
        hasher.update(registration.assumption_manifest().manifest_id().as_bytes());
    }
    hasher.finalize().into()
}

#[test]
fn stable_binding_id_matches_independent_hash_vector() {
    let input = binding(11, 8_192);
    let manual = manual_binding_id(&input);
    assert_eq!(
        zenodex_zrpf_protocol_v3::derive_allowed_child_binding_id_v1(&input)
            .unwrap()
            .as_bytes(),
        &manual
    );
    assert_eq!(
        manual,
        [
            0xeb, 0xe9, 0xee, 0x3b, 0x0e, 0x18, 0x20, 0xfb, 0x6a, 0xc4, 0x0b, 0xbb, 0x11, 0x47,
            0xed, 0x71, 0x05, 0x20, 0xcd, 0xa7, 0xc1, 0xcd, 0xad, 0xde, 0x44, 0x81, 0xbe, 0xd8,
            0x07, 0x9e, 0x22, 0x69,
        ]
    );
}

#[test]
fn stable_object_ids_and_encodings_match_independent_vectors() {
    let (shape, manifest, claims) = fixture();
    let resolution = resolve_assumptions_v1(&shape, &manifest, claims).unwrap();
    let registry = ProofShapeRegistryV1::derive(vec![ProofShapeRegistrationV1::new(
        shape.clone(),
        manifest.clone(),
    )
    .unwrap()])
    .unwrap();
    for requirement in manifest.required_assumptions() {
        assert_eq!(
            requirement.assumption_id().as_bytes(),
            &manual_assumption_id(shape.shape_id(), requirement)
        );
    }
    assert_eq!(shape.shape_id().as_bytes(), &manual_shape_id(&shape));
    assert_eq!(
        manifest.manifest_id().as_bytes(),
        &manual_manifest_id(&manifest)
    );
    assert_eq!(
        resolution.resolution_id().as_bytes(),
        &manual_resolution_id(&resolution)
    );
    assert_eq!(
        registry.registry_id().as_bytes(),
        &manual_registry_id(&registry)
    );

    assert_eq!(
        shape.shape_id().as_bytes(),
        &[
            0x1d, 0xc6, 0x03, 0x52, 0xe9, 0xf5, 0xdd, 0xf0, 0x1d, 0xdd, 0x9e, 0x88, 0xda, 0x46,
            0x00, 0xa2, 0xdb, 0xae, 0x28, 0xf2, 0xa6, 0xde, 0xed, 0x36, 0xfe, 0x5c, 0x9b, 0x9d,
            0xc6, 0x6b, 0x98, 0x3f,
        ]
    );
    assert_eq!(
        manifest.manifest_id().as_bytes(),
        &[
            0xb7, 0xee, 0x88, 0x21, 0x29, 0x93, 0xf4, 0x79, 0x5f, 0xbe, 0xcf, 0x31, 0x78, 0x6f,
            0xcb, 0x8d, 0x8d, 0x0a, 0x1e, 0x89, 0x6f, 0x20, 0x6b, 0xc6, 0xfc, 0x0b, 0x99, 0x78,
            0x48, 0xba, 0xd4, 0x98,
        ]
    );
    assert_eq!(
        resolution.resolution_id().as_bytes(),
        &[
            0xdd, 0xf0, 0x04, 0x7f, 0x65, 0xbb, 0x4a, 0x85, 0x5f, 0x22, 0x0f, 0x2b, 0x3f, 0xa4,
            0xfb, 0x9f, 0x2d, 0x07, 0xf6, 0xfe, 0xae, 0x9a, 0x43, 0x6a, 0xe0, 0x58, 0xd1, 0xf4,
            0xa5, 0x33, 0x70, 0x94,
        ]
    );
    assert_eq!(
        registry.registry_id().as_bytes(),
        &[
            0xa7, 0x2c, 0x81, 0x82, 0xe4, 0x42, 0x07, 0xa3, 0x49, 0xfe, 0x57, 0xde, 0x7f, 0x14,
            0x15, 0xd1, 0xa0, 0x4a, 0xb9, 0xa7, 0x22, 0x1e, 0xfc, 0x22, 0x82, 0x8a, 0xb4, 0xd5,
            0x7e, 0xb0, 0x4a, 0xfb,
        ]
    );
    assert_eq!(
        Sha256::digest(encode_proof_shape_v1(&shape).unwrap()).as_slice(),
        &[
            0x3b, 0x6e, 0x5f, 0x9b, 0xd3, 0x2f, 0xca, 0xdf, 0xeb, 0xb8, 0x9d, 0x2c, 0xd3, 0x48,
            0x75, 0xf3, 0x2c, 0xf4, 0xfa, 0xc0, 0x4e, 0xea, 0xc8, 0x71, 0xfb, 0xa4, 0x82, 0x37,
            0x56, 0x2a, 0xd4, 0x92,
        ]
    );
    assert_eq!(
        Sha256::digest(encode_assumption_manifest_v1(&manifest).unwrap()).as_slice(),
        &[
            0x98, 0xe8, 0x17, 0xe8, 0xb2, 0x85, 0x4e, 0x7c, 0xba, 0xf3, 0x30, 0x2d, 0x08, 0xfa,
            0x5d, 0xab, 0xf7, 0xfa, 0x8a, 0x23, 0x45, 0x81, 0x5a, 0xcb, 0x01, 0x83, 0x26, 0x78,
            0x58, 0xa4, 0x6a, 0x2f,
        ]
    );
    assert_eq!(
        Sha256::digest(encode_proof_shape_registry_v1(&registry).unwrap()).as_slice(),
        &[
            0xbb, 0xfc, 0x16, 0xa8, 0xb9, 0x95, 0xe2, 0xb4, 0xe4, 0x5e, 0x0a, 0xb1, 0x5d, 0x51,
            0x2e, 0x0c, 0x97, 0x1c, 0xc5, 0xc5, 0x4c, 0x43, 0xca, 0xca, 0x4c, 0xf8, 0x7a, 0x96,
            0x68, 0x73, 0x25, 0x67,
        ]
    );
}

#[test]
fn reusable_shape_identity_excludes_instance_claim_and_journal_hashes() {
    let static_binding = AllowedChildBindingInputV1 {
        child_shape_id: child_shape(11),
        child_program_id: ProgramIdV3::new(bytes(31)).unwrap(),
        child_profile_id: ProfileIdV3::new(bytes(51)).unwrap(),
        max_child_journal_bytes: 8_192,
    };
    let shape_a = ProofShapeV1::derive(ProofShapeInputV1 {
        shape_kind: ProofShapeKindV1::Aggregate,
        program_id: ProgramIdV3::new(bytes(1)).unwrap(),
        profile_id: ProfileIdV3::new(bytes(2)).unwrap(),
        resource_ceilings: aggregate_resources(1, 8_192),
        allowed_child_bindings: vec![static_binding.clone()],
    })
    .unwrap();
    let shape_b = ProofShapeV1::derive(ProofShapeInputV1 {
        shape_kind: ProofShapeKindV1::Aggregate,
        program_id: ProgramIdV3::new(bytes(1)).unwrap(),
        profile_id: ProfileIdV3::new(bytes(2)).unwrap(),
        resource_ceilings: aggregate_resources(1, 8_192),
        allowed_child_bindings: vec![static_binding],
    })
    .unwrap();
    assert_eq!(shape_a.shape_id(), shape_b.shape_id());

    let binding_id = shape_a.allowed_child_bindings()[0].binding_id();
    let manifest_a = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: shape_a.shape_id(),
        required_assumptions: vec![AssumptionRequirementInputV1 {
            slot: 0,
            allowed_child_binding_id: binding_id,
            expected_verification_claim_hash: commitment(90),
            expected_child_journal_hash: commitment(91),
        }],
    })
    .unwrap();
    let manifest_b = AssumptionManifestV1::derive(AssumptionManifestInputV1 {
        proof_shape_id: shape_b.shape_id(),
        required_assumptions: vec![AssumptionRequirementInputV1 {
            slot: 0,
            allowed_child_binding_id: binding_id,
            expected_verification_claim_hash: commitment(92),
            expected_child_journal_hash: commitment(93),
        }],
    })
    .unwrap();
    assert_ne!(manifest_a.manifest_id(), manifest_b.manifest_id());
    assert_ne!(
        manifest_a.required_assumptions()[0].assumption_id(),
        manifest_b.required_assumptions()[0].assumption_id()
    );
}
