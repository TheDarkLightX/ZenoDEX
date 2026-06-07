// Type declarations for @zenodex/proof-client/bls.
// This subpath intentionally exposes only the BLS verifier module surface.

export interface VerifyEnvelopeOptions {
  expectedPayloadKind?: string;
  expectedPayloadHash?: string;
}

export interface VerifyEnvelopeSuccess {
  ok: true;
  envelopeHash: string;
}

export interface VerifyEnvelopeFailure {
  ok: false;
  error: string;
}

export function verifyBlsEnvelopeV0(
  envelope: unknown,
  options?: VerifyEnvelopeOptions,
): Promise<VerifyEnvelopeSuccess | VerifyEnvelopeFailure>;

export interface VerifyQuorumOptions {
  expectedPayloadHash?: string;
}

export interface AcceptedSigner {
  signer_id: string;
  key_id: string;
  weight: number;
}

export interface AcceptedSignature extends AcceptedSigner {
  envelope_hash: string;
}

export interface VerifyQuorumSuccess {
  ok: true;
  acceptedWeight: number;
  threshold: number;
  acceptedSigners: AcceptedSigner[];
  acceptedSignatures: AcceptedSignature[];
  quorumReportHash: string;
  payloadKind: string;
  payloadHash: string;
}

export interface VerifyQuorumFailure {
  ok: false;
  error: string;
  accepted?: AcceptedSigner[];
  acceptedWeight?: number;
  threshold?: number;
}

export function verifyBlsQuorumV0(
  bundle: unknown,
  options?: VerifyQuorumOptions,
): Promise<VerifyQuorumSuccess | VerifyQuorumFailure>;

export function validateSignerRegistryV0(registry: unknown): Promise<unknown>;
