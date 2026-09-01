// Copyright 2025 RISC Zero, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{Result, RzupError};

use std::{fmt, str};

#[cfg(feature = "signature")]
#[derive(Debug, PartialEq, Eq)]
pub struct Signature(rsa::pss::Signature);

#[cfg(not(feature = "signature"))]
#[derive(Debug, PartialEq, Eq)]
pub struct Signature(Vec<u8>);

impl fmt::Display for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(feature = "signature")]
        use rsa::signature::SignatureEncoding as _;

        #[cfg(feature = "signature")]
        let bytes = self.0.to_bytes();
        #[cfg(not(feature = "signature"))]
        let bytes = &self.0;
        write!(f, "{}", hex::encode(bytes))
    }
}

impl str::FromStr for Signature {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let signature = hex::decode(s).map_err(|e| format!("invalid RSA signature: {s:?}: {e}"))?;
        #[cfg(feature = "signature")]
        {
            return Ok(Self(
                rsa::pss::Signature::try_from(&signature[..])
                    .map_err(|e| format!("invalid RSA signature: {s:?}: {e}"))?,
            ));
        }
        #[cfg(not(feature = "signature"))]
        {
            Ok(Self(signature))
        }
    }
}

#[cfg(all(test, feature = "signature"))]
#[test]
fn signature_encode_round_trip() {
    let mut rng = rand::thread_rng();
    let pk: PrivateKey = rsa::RsaPrivateKey::new(&mut rng, 2048).unwrap().into();
    let sig = pk.sign(&[1, 2, 3, 4]);

    let rt_sig: Signature = sig.to_string().parse().unwrap();
    assert_eq!(rt_sig, sig);
}

#[cfg(feature = "signature")]
#[derive(Clone)]
#[cfg_attr(not(feature = "publish"), allow(dead_code))]
pub struct PrivateKey(rsa::pss::SigningKey<sha2::Sha256>);

#[cfg(not(feature = "signature"))]
#[derive(Clone)]
pub struct PrivateKey;

impl PrivateKey {
    #[cfg(feature = "signature")]
    pub fn new(pem: &str) -> Result<Self> {
        use rsa::pkcs8::DecodePrivateKey as _;

        let private_key = rsa::RsaPrivateKey::from_pkcs8_pem(pem)
            .map_err(|e| RzupError::Other(format!("invalid private-key PEM: {e}")))?;
        Ok(private_key.into())
    }

    #[cfg(not(feature = "signature"))]
    pub fn new(_pem: &str) -> Result<Self> {
        Err(RzupError::Other("signature feature not enabled".into()))
    }

    #[cfg(feature = "publish")]
    pub fn sign(&self, data: &[u8]) -> Signature {
        use rsa::signature::RandomizedSigner as _;

        let mut rng = rand::thread_rng();
        Signature(self.0.sign_with_rng(&mut rng, data))
    }

    #[cfg(all(test, feature = "signature"))]
    pub fn public_key(&self) -> PublicKey {
        use rsa::signature::Keypair as _;

        PublicKey(self.0.verifying_key())
    }
}

#[cfg(all(test, not(feature = "signature")))]
#[test]
fn signature_disabled_operations_fail_closed() {
    let signature = Signature(vec![0]);

    assert!(PrivateKey::new("").is_err());
    assert!(PublicKey::official().verify(&[], &signature).is_err());
}

#[cfg(feature = "signature")]
impl From<rsa::RsaPrivateKey> for PrivateKey {
    fn from(k: rsa::RsaPrivateKey) -> Self {
        Self(rsa::pss::SigningKey::new(k))
    }
}

#[cfg(feature = "signature")]
pub struct PublicKey(rsa::pss::VerifyingKey<sha2::Sha256>);

#[cfg(not(feature = "signature"))]
pub struct PublicKey;

impl PublicKey {
    #[cfg(feature = "signature")]
    pub fn official() -> Self {
        use rsa::pkcs8::DecodePublicKey as _;

        let pub_key =
            rsa::RsaPublicKey::from_public_key_pem(include_str!("public_key.pem")).unwrap();
        Self(rsa::pss::VerifyingKey::new(pub_key))
    }

    #[cfg(not(feature = "signature"))]
    pub fn official() -> Self {
        Self
    }

    #[cfg(feature = "signature")]
    pub fn verify(&self, data: &[u8], signature: &Signature) -> Result<()> {
        use rsa::signature::Verifier as _;

        self.0
            .verify(data, &signature.0)
            .map_err(|e| RzupError::InvalidSignature(e.to_string()))
    }

    #[cfg(not(feature = "signature"))]
    pub fn verify(&self, _data: &[u8], _signature: &Signature) -> Result<()> {
        Err(RzupError::Other("signature feature not enabled".into()))
    }
}
