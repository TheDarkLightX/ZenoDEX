"""Research-only named Boolean-choice polynomial.

The authoritative research value is a function on a closed, named Boolean
cube.  Support sets and probability distributions are projections and must not
be substituted for the named function or its choice manifest.

This module has no settlement, governance, proof, or runtime authority.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import re
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Mapping

_CHOICE_ID = re.compile(r"[a-z][a-z0-9_.:-]{0,127}\Z")
_HEX_ROOT = re.compile(r"[0-9a-f]{64}\Z")
_MANIFEST_DOMAIN = b"zenodex.choice-fiber.manifest.v1\x00"
_FUNCTION_DOMAIN = b"zenodex.choice-fiber.function.v1\x00"
_SUPPORT_DOMAIN = b"zenodex.choice-fiber.support.v1\x00"
_DISTRIBUTION_DOMAIN = b"zenodex.choice-fiber.distribution.v1\x00"


class ChoiceFiberReject(ValueError):
    """Typed research-boundary rejection."""


def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")


def _root(domain: bytes, value: object) -> str:
    return hashlib.sha256(domain + _canonical_json(value)).hexdigest()


@dataclass(frozen=True, slots=True)
class ChoiceAtomV1:
    """One exact named choice and its non-authoritative source identity."""

    choice_id: str
    source_occurrence_root: str

    def __post_init__(self) -> None:
        if not isinstance(self.choice_id, str):
            raise ChoiceFiberReject("INVALID_CHOICE_ID")
        if _CHOICE_ID.fullmatch(self.choice_id) is None:
            raise ChoiceFiberReject("INVALID_CHOICE_ID")
        if not isinstance(self.source_occurrence_root, str):
            raise ChoiceFiberReject("INVALID_SOURCE_OCCURRENCE_ROOT")
        if _HEX_ROOT.fullmatch(self.source_occurrence_root) is None:
            raise ChoiceFiberReject("INVALID_SOURCE_OCCURRENCE_ROOT")

    def canonical_record(self) -> dict[str, str]:
        return {
            "choice_id": self.choice_id,
            "source_occurrence_root": self.source_occurrence_root,
        }


@dataclass(frozen=True, slots=True)
class ChoiceManifestV1:
    """Closed ordered universe of choices.

    An atom remains in the manifest even when its coefficient is zero.  This
    prevents semantic simplification from silently erasing coverage lineage.
    """

    atoms: tuple[ChoiceAtomV1, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.atoms, tuple) or any(
            not isinstance(atom, ChoiceAtomV1) for atom in self.atoms
        ):
            raise ChoiceFiberReject("INVALID_CHOICE_ATOMS")
        ids = tuple(atom.choice_id for atom in self.atoms)
        if ids != tuple(sorted(ids)):
            raise ChoiceFiberReject("NON_CANONICAL_CHOICE_ORDER")
        if len(set(ids)) != len(ids):
            raise ChoiceFiberReject("DUPLICATE_CHOICE_ID")

    @property
    def choice_ids(self) -> tuple[str, ...]:
        return tuple(atom.choice_id for atom in self.atoms)

    @property
    def root(self) -> str:
        return _root(
            _MANIFEST_DOMAIN,
            {
                "atoms": [atom.canonical_record() for atom in self.atoms],
                "correlation_rule": "equal_choice_id_means_shared_sign",
                "sign_domain": [-1, 1],
                "version": 1,
            },
        )


@dataclass(frozen=True, slots=True)
class TermV1:
    """Canonical Fourier-Walsh monomial coefficient."""

    monomial: tuple[str, ...]
    coefficient: int

    def __post_init__(self) -> None:
        if not isinstance(self.monomial, tuple):
            raise ChoiceFiberReject("INVALID_MONOMIAL")
        if not isinstance(self.coefficient, int) or isinstance(self.coefficient, bool):
            raise ChoiceFiberReject("NON_INTEGER_COEFFICIENT")
        if self.coefficient == 0:
            raise ChoiceFiberReject("ZERO_TERM_MUST_BE_OMITTED")
        if self.monomial != tuple(sorted(self.monomial)):
            raise ChoiceFiberReject("NON_CANONICAL_MONOMIAL_ORDER")
        if len(set(self.monomial)) != len(self.monomial):
            raise ChoiceFiberReject("NON_REDUCED_MONOMIAL")
        if any(_CHOICE_ID.fullmatch(choice_id) is None for choice_id in self.monomial):
            raise ChoiceFiberReject("INVALID_MONOMIAL_CHOICE_ID")

    def canonical_record(self) -> dict[str, object]:
        return {
            "coefficient": self.coefficient,
            "monomial": list(self.monomial),
        }


def _reduce_monomial(choice_ids: Iterable[str]) -> tuple[str, ...]:
    parity: set[str] = set()
    for choice_id in choice_ids:
        if _CHOICE_ID.fullmatch(choice_id) is None:
            raise ChoiceFiberReject("INVALID_MONOMIAL_CHOICE_ID")
        if choice_id in parity:
            parity.remove(choice_id)
        else:
            parity.add(choice_id)
    return tuple(sorted(parity))


@dataclass(frozen=True, slots=True)
class ChoiceFiberPolynomialV1:
    """Exact named function on a finite Boolean cube.

    Multiplication is performed in the quotient where each named sign obeys
    ``epsilon_i ** 2 = 1``.  Monomial multiplication is therefore symmetric
    difference of choice identifiers.
    """

    manifest: ChoiceManifestV1
    terms: tuple[TermV1, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.manifest, ChoiceManifestV1):
            raise ChoiceFiberReject("INVALID_CHOICE_MANIFEST")
        if not isinstance(self.terms, tuple) or any(
            not isinstance(term, TermV1) for term in self.terms
        ):
            raise ChoiceFiberReject("INVALID_TERMS")
        monomials = tuple(term.monomial for term in self.terms)
        if monomials != tuple(sorted(monomials)):
            raise ChoiceFiberReject("NON_CANONICAL_TERM_ORDER")
        if len(set(monomials)) != len(monomials):
            raise ChoiceFiberReject("DUPLICATE_MONOMIAL")
        allowed = set(self.manifest.choice_ids)
        if any(not set(term.monomial) <= allowed for term in self.terms):
            raise ChoiceFiberReject("CHOICE_OUTSIDE_MANIFEST")

    @classmethod
    def from_coefficients(
        cls,
        manifest: ChoiceManifestV1,
        coefficients: Mapping[tuple[str, ...], int],
    ) -> ChoiceFiberPolynomialV1:
        """Normalize a boundary mapping into one immutable canonical value."""

        accumulated: dict[tuple[str, ...], int] = {}
        for raw_monomial, coefficient in coefficients.items():
            if not isinstance(coefficient, int) or isinstance(coefficient, bool):
                raise ChoiceFiberReject("NON_INTEGER_COEFFICIENT")
            monomial = _reduce_monomial(raw_monomial)
            accumulated[monomial] = accumulated.get(monomial, 0) + coefficient
        terms = tuple(
            TermV1(monomial=monomial, coefficient=coefficient)
            for monomial, coefficient in sorted(accumulated.items())
            if coefficient != 0
        )
        return cls(manifest=manifest, terms=terms)

    @classmethod
    def affine(
        cls,
        manifest: ChoiceManifestV1,
        *,
        center: int,
        coefficients: Mapping[str, int],
    ) -> ChoiceFiberPolynomialV1:
        if set(coefficients) - set(manifest.choice_ids):
            raise ChoiceFiberReject("CHOICE_OUTSIDE_MANIFEST")
        raw: dict[tuple[str, ...], int] = {(): center}
        raw.update({(choice_id,): coefficient for choice_id, coefficient in coefficients.items()})
        return cls.from_coefficients(manifest, raw)

    @property
    def function_root(self) -> str:
        return _root(
            _FUNCTION_DOMAIN,
            {
                "choice_manifest_root": self.manifest.root,
                "terms": [term.canonical_record() for term in self.terms],
                "version": 1,
            },
        )

    def coefficient_map(self) -> dict[tuple[str, ...], int]:
        return {term.monomial: term.coefficient for term in self.terms}

    def evaluate(self, assignment: Mapping[str, int]) -> int:
        if set(assignment) != set(self.manifest.choice_ids):
            raise ChoiceFiberReject("ASSIGNMENT_DOMAIN_MISMATCH")
        if any(
            not isinstance(sign, int) or isinstance(sign, bool) or sign not in (-1, 1)
            for sign in assignment.values()
        ):
            raise ChoiceFiberReject("INVALID_SIGN_VALUE")
        total = 0
        for term in self.terms:
            value = term.coefficient
            for choice_id in term.monomial:
                value *= assignment[choice_id]
            total += value
        return total

    def assignments(self) -> tuple[dict[str, int], ...]:
        ids = self.manifest.choice_ids
        return tuple(
            dict(zip(ids, signs, strict=True))
            for signs in itertools.product((-1, 1), repeat=len(ids))
        )

    def branch_values(self) -> tuple[int, ...]:
        """Values in canonical assignment order, retaining multiplicity."""

        return tuple(self.evaluate(assignment) for assignment in self.assignments())

    def support(self) -> tuple[int, ...]:
        """Sorted distinct semantic projection."""

        return tuple(sorted(set(self.branch_values())))

    @property
    def distribution_root(self) -> str:
        return _root(
            _DISTRIBUTION_DOMAIN,
            {
                "choice_manifest_root": self.manifest.root,
                "uniform_assignment_values": list(self.branch_values()),
                "version": 1,
            },
        )

    @property
    def support_root(self) -> str:
        return _root(
            _SUPPORT_DOMAIN,
            {
                "distinct_values": list(self.support()),
                "version": 1,
            },
        )

    def _require_same_manifest(self, other: ChoiceFiberPolynomialV1) -> None:
        if self.manifest != other.manifest:
            raise ChoiceFiberReject("FOREIGN_CHOICE_MANIFEST")

    def add(self, other: ChoiceFiberPolynomialV1) -> ChoiceFiberPolynomialV1:
        self._require_same_manifest(other)
        coefficients = self.coefficient_map()
        for monomial, coefficient in other.coefficient_map().items():
            coefficients[monomial] = coefficients.get(monomial, 0) + coefficient
        return ChoiceFiberPolynomialV1.from_coefficients(self.manifest, coefficients)

    def subtract(self, other: ChoiceFiberPolynomialV1) -> ChoiceFiberPolynomialV1:
        self._require_same_manifest(other)
        coefficients = self.coefficient_map()
        for monomial, coefficient in other.coefficient_map().items():
            coefficients[monomial] = coefficients.get(monomial, 0) - coefficient
        return ChoiceFiberPolynomialV1.from_coefficients(self.manifest, coefficients)

    def multiply(self, other: ChoiceFiberPolynomialV1) -> ChoiceFiberPolynomialV1:
        self._require_same_manifest(other)
        coefficients: dict[tuple[str, ...], int] = {}
        for left in self.terms:
            for right in other.terms:
                monomial = _reduce_monomial((*left.monomial, *right.monomial))
                coefficients[monomial] = (
                    coefficients.get(monomial, 0) + left.coefficient * right.coefficient
                )
        return ChoiceFiberPolynomialV1.from_coefficients(self.manifest, coefficients)

    def is_affine(self) -> bool:
        return all(len(term.monomial) <= 1 for term in self.terms)

    def exact_affine_bounds(self) -> tuple[int, int]:
        if not self.is_affine():
            raise ChoiceFiberReject("NON_AFFINE_POLYNOMIAL")
        coefficients = self.coefficient_map()
        center = coefficients.get((), 0)
        radius = sum(
            abs(coefficient) for monomial, coefficient in coefficients.items() if len(monomial) == 1
        )
        return center - radius, center + radius

    def uniform_assignment_moments(self) -> tuple[Fraction, Fraction]:
        values = self.branch_values()
        if not values:
            raise ChoiceFiberReject("EMPTY_ASSIGNMENT_SPACE")
        count = len(values)
        mean = Fraction(sum(values), count)
        variance = (
            sum(
                ((Fraction(value) - mean) ** 2 for value in values),
                start=Fraction(0),
            )
            / count
        )
        return mean, variance
