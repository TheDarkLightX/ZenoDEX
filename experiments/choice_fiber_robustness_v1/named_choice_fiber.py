"""Deterministic reference model for named choice-fiber polynomials.

This module is research-only.  It deliberately uses exact integers and
recomputes every certificate from its source polynomial at verification time.
"""

from __future__ import annotations

import json
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from hashlib import sha256
from itertools import product
from typing import TypeVar

MAX_CHOICE_COUNT = 256
MAX_EXHAUSTIVE_CHOICES = 20
MAX_EXHAUSTIVE_WORK = 20_000_000
MAX_IDENTIFIER_BYTES = 128
MAX_OCCURRENCE_COUNT = 4096
MAX_RAW_TERM_COUNT = 4096
MAX_CANONICAL_TERM_COUNT = 4096
MAX_TERM_OCCURRENCES = 256
MAX_COEFFICIENT_BITS = 256

T = TypeVar("T")


class ChoiceFiberError(ValueError):
    """Typed construction or verification rejection."""


def _framed(domain: str, value: object) -> bytes:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    tag = domain.encode("ascii")
    return len(tag).to_bytes(4, "big") + tag + len(payload).to_bytes(8, "big") + payload


def _root(domain: str, value: object) -> str:
    return sha256(_framed(domain, value)).hexdigest()


def _require_text(value: object, code: str) -> str:
    if type(value) is not str or not value:
        raise ChoiceFiberError(code)
    try:
        encoded = value.encode("utf-8")
    except UnicodeError as error:
        raise ChoiceFiberError(code) from error
    if len(encoded) > MAX_IDENTIFIER_BYTES:
        raise ChoiceFiberError(code)
    return value


def _require_digest(value: object, code: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ChoiceFiberError(code)
    return value


def _require_assignment(
    value: object,
    code: str,
) -> tuple[tuple[str, int], ...]:
    if type(value) is not tuple:
        raise ChoiceFiberError(code)
    if len(value) > MAX_CHOICE_COUNT:
        raise ChoiceFiberError(code)
    previous = ""
    for item in value:
        if (
            type(item) is not tuple
            or len(item) != 2
            or type(item[1]) is not int
            or item[1] not in (-1, 1)
        ):
            raise ChoiceFiberError(code)
        choice_id = _require_text(item[0], code)
        if choice_id <= previous:
            raise ChoiceFiberError(code)
        previous = choice_id
    return value


def _bounded_tuple(values: Iterable[T], limit: int, code: str) -> tuple[T, ...]:
    retained: list[T] = []
    try:
        for item in values:
            if len(retained) == limit:
                raise ChoiceFiberError(code)
            retained.append(item)
    except ChoiceFiberError:
        raise
    except Exception as error:
        raise ChoiceFiberError(code) from error
    return tuple(retained)


def _bounded_mapping_items(
    value: object,
    *,
    limit: int,
    invalid_code: str,
    capacity_code: str,
) -> tuple[tuple[object, object], ...]:
    if not isinstance(value, Mapping):
        raise ChoiceFiberError(invalid_code)
    retained: list[tuple[object, object]] = []
    try:
        for item in value.items():
            if len(retained) == limit:
                raise ChoiceFiberError(capacity_code)
            if type(item) is not tuple or len(item) != 2:
                raise ChoiceFiberError(invalid_code)
            retained.append(item)
    except ChoiceFiberError:
        raise
    except Exception as error:
        raise ChoiceFiberError(invalid_code) from error
    return tuple(retained)


@dataclass(frozen=True, order=True)
class ChoiceOccurrence:
    """One exact syntactic occurrence of a shared signed choice variable."""

    occurrence_id: str
    choice_id: str
    polarity: int = 1

    def __post_init__(self) -> None:
        _require_text(self.occurrence_id, "EMPTY_CHOICE_IDENTITY")
        _require_text(self.choice_id, "EMPTY_CHOICE_IDENTITY")
        if type(self.polarity) is not int or self.polarity not in (-1, 1):
            raise ChoiceFiberError("INVALID_CHOICE_POLARITY")


@dataclass(frozen=True)
class ChoiceFiberManifest:
    """Closed choice universe plus exact occurrence-to-choice correlation map."""

    choice_ids: tuple[str, ...]
    occurrences: tuple[ChoiceOccurrence, ...]

    def __post_init__(self) -> None:
        if type(self.choice_ids) is not tuple:
            raise ChoiceFiberError("INVALID_CHOICE_IDENTITIES")
        if len(self.choice_ids) > MAX_CHOICE_COUNT:
            raise ChoiceFiberError("CHOICE_CAPACITY_EXCEEDED")
        if any(type(choice_id) is not str or not choice_id for choice_id in self.choice_ids):
            raise ChoiceFiberError("INVALID_CHOICE_IDENTITIES")
        for choice_id in self.choice_ids:
            _require_text(choice_id, "INVALID_CHOICE_IDENTITIES")
        if type(self.occurrences) is not tuple:
            raise ChoiceFiberError("INVALID_CHOICE_OCCURRENCES")
        if len(self.occurrences) > MAX_OCCURRENCE_COUNT:
            raise ChoiceFiberError("OCCURRENCE_CAPACITY_EXCEEDED")
        if any(type(item) is not ChoiceOccurrence for item in self.occurrences):
            raise ChoiceFiberError("INVALID_CHOICE_OCCURRENCES")
        if tuple(sorted(self.choice_ids)) != self.choice_ids:
            raise ChoiceFiberError("NONCANONICAL_CHOICE_ORDER")
        if len(set(self.choice_ids)) != len(self.choice_ids):
            raise ChoiceFiberError("DUPLICATE_CHOICE_ID")
        if tuple(sorted(self.occurrences)) != self.occurrences:
            raise ChoiceFiberError("NONCANONICAL_OCCURRENCE_ORDER")
        occurrence_ids = tuple(item.occurrence_id for item in self.occurrences)
        if len(set(occurrence_ids)) != len(occurrence_ids):
            raise ChoiceFiberError("DUPLICATE_OCCURRENCE_ID")
        known = set(self.choice_ids)
        if any(item.choice_id not in known for item in self.occurrences):
            raise ChoiceFiberError("UNKNOWN_OCCURRENCE_CHOICE")

    @classmethod
    def admit(
        cls,
        choice_ids: Iterable[str],
        occurrences: Iterable[ChoiceOccurrence],
    ) -> ChoiceFiberManifest:
        retained_choice_ids = _bounded_tuple(
            choice_ids,
            MAX_CHOICE_COUNT,
            "CHOICE_CAPACITY_EXCEEDED",
        )
        retained_occurrences = _bounded_tuple(
            occurrences,
            MAX_OCCURRENCE_COUNT,
            "OCCURRENCE_CAPACITY_EXCEEDED",
        )
        if any(type(choice_id) is not str or not choice_id for choice_id in retained_choice_ids):
            raise ChoiceFiberError("INVALID_CHOICE_IDENTITIES")
        for choice_id in retained_choice_ids:
            _require_text(choice_id, "INVALID_CHOICE_IDENTITIES")
        if any(type(item) is not ChoiceOccurrence for item in retained_occurrences):
            raise ChoiceFiberError("INVALID_CHOICE_OCCURRENCES")
        return cls(
            tuple(sorted(retained_choice_ids)),
            tuple(sorted(retained_occurrences)),
        )

    @property
    def root(self) -> str:
        return _root(
            "zenodex.choice-fiber-manifest.v1",
            {
                "choices": self.choice_ids,
                "occurrences": [
                    (item.occurrence_id, item.choice_id, item.polarity) for item in self.occurrences
                ],
            },
        )

    @property
    def occurrence_map(self) -> dict[str, ChoiceOccurrence]:
        return {item.occurrence_id: item for item in self.occurrences}


@dataclass(frozen=True)
class RawTerm:
    coefficient: int
    occurrence_ids: tuple[str, ...]
    source_id: str

    def __post_init__(self) -> None:
        _require_text(self.source_id, "EMPTY_TERM_SOURCE")
        if type(self.coefficient) is not int:
            raise ChoiceFiberError("NONINTEGER_COEFFICIENT")
        if abs(self.coefficient).bit_length() > MAX_COEFFICIENT_BITS:
            raise ChoiceFiberError("COEFFICIENT_CAPACITY_EXCEEDED")
        if type(self.occurrence_ids) is not tuple:
            raise ChoiceFiberError("INVALID_TERM_OCCURRENCES")
        if len(self.occurrence_ids) > MAX_TERM_OCCURRENCES:
            raise ChoiceFiberError("TERM_OCCURRENCE_CAPACITY_EXCEEDED")
        if any(
            type(occurrence_id) is not str or not occurrence_id
            for occurrence_id in self.occurrence_ids
        ):
            raise ChoiceFiberError("INVALID_TERM_OCCURRENCES")
        for occurrence_id in self.occurrence_ids:
            _require_text(occurrence_id, "INVALID_TERM_OCCURRENCES")


@dataclass(frozen=True, order=True)
class CanonicalTerm:
    choices: tuple[str, ...]
    coefficient: int

    def __post_init__(self) -> None:
        if type(self.choices) is not tuple:
            raise ChoiceFiberError("INVALID_MONOMIAL_CHOICES")
        if len(self.choices) > MAX_CHOICE_COUNT:
            raise ChoiceFiberError("MONOMIAL_CAPACITY_EXCEEDED")
        if any(type(choice_id) is not str or not choice_id for choice_id in self.choices):
            raise ChoiceFiberError("INVALID_MONOMIAL_CHOICES")
        for choice_id in self.choices:
            _require_text(choice_id, "INVALID_MONOMIAL_CHOICES")
        if tuple(sorted(self.choices)) != self.choices:
            raise ChoiceFiberError("NONCANONICAL_MONOMIAL_ORDER")
        if len(set(self.choices)) != len(self.choices):
            raise ChoiceFiberError("NONMULTILINEAR_MONOMIAL")
        if type(self.coefficient) is not int:
            raise ChoiceFiberError("NONINTEGER_COEFFICIENT")
        if abs(self.coefficient).bit_length() > MAX_COEFFICIENT_BITS:
            raise ChoiceFiberError("COEFFICIENT_CAPACITY_EXCEEDED")
        if self.coefficient == 0:
            raise ChoiceFiberError("ZERO_CANONICAL_COEFFICIENT")


def _derive_terms_and_lineage(
    manifest: ChoiceFiberManifest,
    raw_terms: Sequence[RawTerm],
) -> tuple[tuple[CanonicalTerm, ...], tuple[object, ...]]:
    occurrence_map = manifest.occurrence_map
    coefficients: dict[tuple[str, ...], int] = {}
    exact_lineage: list[object] = []
    seen_source_ids: set[str] = set()

    for raw in raw_terms:
        if raw.source_id in seen_source_ids:
            raise ChoiceFiberError("DUPLICATE_TERM_SOURCE")
        seen_source_ids.add(raw.source_id)
        parity: set[str] = set()
        polarity = 1
        resolved: list[tuple[str, str, int]] = []
        for occurrence_id in raw.occurrence_ids:
            occurrence = occurrence_map.get(occurrence_id)
            if occurrence is None:
                raise ChoiceFiberError("UNKNOWN_TERM_OCCURRENCE")
            polarity *= occurrence.polarity
            if occurrence.choice_id in parity:
                parity.remove(occurrence.choice_id)
            else:
                parity.add(occurrence.choice_id)
            resolved.append(
                (
                    occurrence.occurrence_id,
                    occurrence.choice_id,
                    occurrence.polarity,
                )
            )
        monomial = tuple(sorted(parity))
        coefficient = raw.coefficient * polarity
        coefficients[monomial] = coefficients.get(monomial, 0) + coefficient
        exact_lineage.append(
            (
                raw.source_id,
                raw.coefficient,
                tuple(raw.occurrence_ids),
                tuple(resolved),
            )
        )

    canonical = tuple(
        CanonicalTerm(choices, coefficient)
        for choices, coefficient in sorted(coefficients.items())
        if coefficient != 0
    )
    return canonical, tuple(exact_lineage)


@dataclass(frozen=True)
class ChoiceFiberPolynomial:
    """Unique multilinear polynomial over a closed named ±1 choice universe."""

    manifest: ChoiceFiberManifest
    terms: tuple[CanonicalTerm, ...]
    raw_terms: tuple[RawTerm, ...]

    def __post_init__(self) -> None:
        if type(self.manifest) is not ChoiceFiberManifest:
            raise ChoiceFiberError("INVALID_CHOICE_MANIFEST")
        if type(self.terms) is not tuple:
            raise ChoiceFiberError("INVALID_CANONICAL_TERMS")
        if len(self.terms) > MAX_CANONICAL_TERM_COUNT:
            raise ChoiceFiberError("CANONICAL_TERM_CAPACITY_EXCEEDED")
        if any(type(term) is not CanonicalTerm for term in self.terms):
            raise ChoiceFiberError("INVALID_CANONICAL_TERMS")
        if type(self.raw_terms) is not tuple:
            raise ChoiceFiberError("INVALID_RAW_TERMS")
        if len(self.raw_terms) > MAX_RAW_TERM_COUNT:
            raise ChoiceFiberError("RAW_TERM_CAPACITY_EXCEEDED")
        if any(type(term) is not RawTerm for term in self.raw_terms):
            raise ChoiceFiberError("INVALID_RAW_TERMS")
        term_keys = tuple(term.choices for term in self.terms)
        if tuple(sorted(term_keys)) != term_keys:
            raise ChoiceFiberError("NONCANONICAL_TERM_ORDER")
        if len(set(term_keys)) != len(term_keys):
            raise ChoiceFiberError("DUPLICATE_CANONICAL_MONOMIAL")
        known = set(self.manifest.choice_ids)
        if any(not set(term.choices).issubset(known) for term in self.terms):
            raise ChoiceFiberError("UNKNOWN_TERM_CHOICE")
        derived_terms, _ = _derive_terms_and_lineage(self.manifest, self.raw_terms)
        if self.terms != derived_terms:
            raise ChoiceFiberError("DERIVED_TERM_MISMATCH")

    @classmethod
    def compile(
        cls,
        manifest: ChoiceFiberManifest,
        raw_terms: Sequence[RawTerm],
    ) -> ChoiceFiberPolynomial:
        retained_raw_terms = _bounded_tuple(
            raw_terms,
            MAX_RAW_TERM_COUNT,
            "RAW_TERM_CAPACITY_EXCEEDED",
        )
        canonical, _ = _derive_terms_and_lineage(manifest, retained_raw_terms)
        return cls(manifest, canonical, retained_raw_terms)

    @classmethod
    def from_coefficients(
        cls,
        choice_ids: Iterable[str],
        coefficients: Mapping[tuple[str, ...], int],
        source_namespace: str = "direct",
    ) -> ChoiceFiberPolynomial:
        _require_text(source_namespace, "INVALID_SOURCE_NAMESPACE")
        retained_choices = _bounded_tuple(
            choice_ids,
            MAX_CHOICE_COUNT,
            "CHOICE_CAPACITY_EXCEEDED",
        )
        if any(type(choice_id) is not str or not choice_id for choice_id in retained_choices):
            raise ChoiceFiberError("INVALID_CHOICE_IDENTITIES")
        choices = tuple(sorted(retained_choices))
        occurrence_items: list[ChoiceOccurrence] = []
        raw_terms: list[RawTerm] = []
        retained_coefficients = _bounded_mapping_items(
            coefficients,
            limit=MAX_RAW_TERM_COUNT,
            invalid_code="INVALID_COEFFICIENT_MAPPING",
            capacity_code="RAW_TERM_CAPACITY_EXCEEDED",
        )
        seen_monomials: set[tuple[str, ...]] = set()
        validated_coefficients: list[tuple[tuple[str, ...], int]] = []
        for monomial, coefficient in retained_coefficients:
            if type(monomial) is not tuple:
                raise ChoiceFiberError("INVALID_MONOMIAL_CHOICES")
            if len(monomial) > MAX_TERM_OCCURRENCES:
                raise ChoiceFiberError("TERM_OCCURRENCE_CAPACITY_EXCEEDED")
            if type(coefficient) is not int:
                raise ChoiceFiberError("NONINTEGER_COEFFICIENT")
            if abs(coefficient).bit_length() > MAX_COEFFICIENT_BITS:
                raise ChoiceFiberError("COEFFICIENT_CAPACITY_EXCEEDED")
            if any(type(choice_id) is not str or not choice_id for choice_id in monomial):
                raise ChoiceFiberError("INVALID_MONOMIAL_CHOICES")
            for choice_id in monomial:
                _require_text(choice_id, "INVALID_MONOMIAL_CHOICES")
            if monomial in seen_monomials:
                raise ChoiceFiberError("INVALID_COEFFICIENT_MAPPING")
            seen_monomials.add(monomial)
            validated_coefficients.append((monomial, coefficient))
        for index, (monomial, coefficient) in enumerate(sorted(validated_coefficients)):
            occurrence_ids: list[str] = []
            for inner, choice_id in enumerate(monomial):
                if len(occurrence_items) == MAX_OCCURRENCE_COUNT:
                    raise ChoiceFiberError("OCCURRENCE_CAPACITY_EXCEEDED")
                occurrence_id = f"{source_namespace}:term:{index}:occ:{inner}"
                occurrence_items.append(ChoiceOccurrence(occurrence_id, choice_id))
                occurrence_ids.append(occurrence_id)
            raw_terms.append(
                RawTerm(
                    coefficient,
                    tuple(occurrence_ids),
                    f"{source_namespace}:term:{index}",
                )
            )
        manifest = ChoiceFiberManifest.admit(choices, occurrence_items)
        return cls.compile(manifest, raw_terms)

    @property
    def coefficient_map(self) -> dict[tuple[str, ...], int]:
        return {term.choices: term.coefficient for term in self.terms}

    @property
    def degree(self) -> int:
        return max((len(term.choices) for term in self.terms), default=0)

    @property
    def semantic_root(self) -> str:
        """Identity of the named function, excluding occurrence decomposition."""
        return _root(
            "zenodex.choice-fiber-semantic-function.v1",
            {
                "choices": self.manifest.choice_ids,
                "terms": [(term.choices, term.coefficient) for term in self.terms],
            },
        )

    @property
    def lineage_root(self) -> str:
        """Identity of the exact source decomposition and correlation mapping."""
        _, exact_lineage = _derive_terms_and_lineage(self.manifest, self.raw_terms)
        return _root(
            "zenodex.choice-fiber-lineage.v1",
            {
                "manifest_root": self.manifest.root,
                "raw_terms": exact_lineage,
            },
        )

    @property
    def root(self) -> str:
        """Complete identity binding semantic function and exact lineage."""
        return _root(
            "zenodex.choice-fiber-polynomial.v1",
            {
                "manifest_root": self.manifest.root,
                "semantic_root": self.semantic_root,
                "lineage_root": self.lineage_root,
            },
        )

    def evaluate(self, assignment: Mapping[str, int]) -> int:
        retained = _bounded_mapping_items(
            assignment,
            limit=MAX_CHOICE_COUNT,
            invalid_code="INVALID_ASSIGNMENT_MAPPING",
            capacity_code="INCOMPLETE_OR_SURPLUS_ASSIGNMENT",
        )
        assignment_snapshot: dict[str, int] = {}
        for choice_id, value in retained:
            if type(choice_id) is not str:
                raise ChoiceFiberError("INVALID_ASSIGNMENT_MAPPING")
            if type(value) is not int or value not in (-1, 1):
                raise ChoiceFiberError("INVALID_ASSIGNMENT_SIGN")
            if choice_id in assignment_snapshot:
                raise ChoiceFiberError("INVALID_ASSIGNMENT_MAPPING")
            assignment_snapshot[choice_id] = value
        if set(assignment_snapshot) != set(self.manifest.choice_ids):
            raise ChoiceFiberError("INCOMPLETE_OR_SURPLUS_ASSIGNMENT")
        total = 0
        for term in self.terms:
            value = term.coefficient
            for choice_id in term.choices:
                value *= assignment_snapshot[choice_id]
            total += value
        return total


def _owned_polynomial_snapshot(value: object) -> ChoiceFiberPolynomial:
    if type(value) is not ChoiceFiberPolynomial:
        raise ChoiceFiberError("INVALID_CHOICE_FIBER_POLYNOMIAL")
    try:
        manifest = value.manifest
        if type(manifest) is not ChoiceFiberManifest:
            raise ChoiceFiberError("INVALID_CHOICE_MANIFEST")
        choice_ids = _bounded_tuple(
            manifest.choice_ids,
            MAX_CHOICE_COUNT,
            "CHOICE_CAPACITY_EXCEEDED",
        )
        occurrence_source = _bounded_tuple(
            manifest.occurrences,
            MAX_OCCURRENCE_COUNT,
            "OCCURRENCE_CAPACITY_EXCEEDED",
        )
        occurrences = tuple(
            ChoiceOccurrence(item.occurrence_id, item.choice_id, item.polarity)
            for item in occurrence_source
            if type(item) is ChoiceOccurrence
        )
        if len(occurrences) != len(occurrence_source):
            raise ChoiceFiberError("INVALID_CHOICE_OCCURRENCES")
        owned_manifest = ChoiceFiberManifest(choice_ids, occurrences)
        raw_source = _bounded_tuple(
            value.raw_terms,
            MAX_RAW_TERM_COUNT,
            "RAW_TERM_CAPACITY_EXCEEDED",
        )
        raw_terms = tuple(
            RawTerm(
                item.coefficient,
                _bounded_tuple(
                    item.occurrence_ids,
                    MAX_TERM_OCCURRENCES,
                    "TERM_OCCURRENCE_CAPACITY_EXCEEDED",
                ),
                item.source_id,
            )
            for item in raw_source
            if type(item) is RawTerm
        )
        if len(raw_terms) != len(raw_source):
            raise ChoiceFiberError("INVALID_RAW_TERMS")
        term_source = _bounded_tuple(
            value.terms,
            MAX_CANONICAL_TERM_COUNT,
            "CANONICAL_TERM_CAPACITY_EXCEEDED",
        )
        terms = tuple(
            CanonicalTerm(
                _bounded_tuple(
                    item.choices,
                    MAX_CHOICE_COUNT,
                    "MONOMIAL_CAPACITY_EXCEEDED",
                ),
                item.coefficient,
            )
            for item in term_source
            if type(item) is CanonicalTerm
        )
        if len(terms) != len(term_source):
            raise ChoiceFiberError("INVALID_CANONICAL_TERMS")
        return ChoiceFiberPolynomial(owned_manifest, terms, raw_terms)
    except ChoiceFiberError:
        raise
    except Exception as error:
        raise ChoiceFiberError("INVALID_CHOICE_FIBER_POLYNOMIAL") from error


@dataclass(frozen=True)
class MinimumWitness:
    minimum: int
    assignment: tuple[tuple[str, int], ...]
    assignments_checked: int

    def __post_init__(self) -> None:
        if type(self.minimum) is not int or type(self.assignments_checked) is not int:
            raise ChoiceFiberError("INVALID_MINIMUM_WITNESS")
        _require_assignment(self.assignment, "INVALID_MINIMUM_WITNESS")


def brute_force_minimum(polynomial: ChoiceFiberPolynomial) -> MinimumWitness:
    polynomial = _owned_polynomial_snapshot(polynomial)
    choices = polynomial.manifest.choice_ids
    if len(choices) > MAX_EXHAUSTIVE_CHOICES:
        raise ChoiceFiberError("BRUTE_FORCE_CAPACITY_EXCEEDED")
    term_work = max(
        1,
        sum(max(1, len(term.choices)) for term in polynomial.terms),
    )
    if (1 << len(choices)) * term_work > MAX_EXHAUSTIVE_WORK:
        raise ChoiceFiberError("EXHAUSTIVE_WORK_CAPACITY_EXCEEDED")
    best_value: int | None = None
    best_assignment: tuple[tuple[str, int], ...] | None = None
    checks = 0
    for signs in product((-1, 1), repeat=len(choices)):
        assignment_tuple = tuple(zip(choices, signs, strict=True))
        value = polynomial.evaluate(dict(assignment_tuple))
        checks += 1
        if best_value is None or value < best_value:
            best_value = value
            best_assignment = assignment_tuple
    if best_value is None or best_assignment is None:
        raise AssertionError("finite choice cube unexpectedly empty")
    return MinimumWitness(best_value, best_assignment, checks)


@dataclass(frozen=True)
class AffineMinimumCertificate:
    manifest_root: str
    polynomial_root: str
    minimum: int
    assignment: tuple[tuple[str, int], ...]

    def __post_init__(self) -> None:
        _require_digest(self.manifest_root, "INVALID_AFFINE_CERTIFICATE")
        _require_digest(self.polynomial_root, "INVALID_AFFINE_CERTIFICATE")
        if type(self.minimum) is not int:
            raise ChoiceFiberError("INVALID_AFFINE_CERTIFICATE")
        _require_assignment(self.assignment, "INVALID_AFFINE_CERTIFICATE")


def create_affine_certificate(
    polynomial: ChoiceFiberPolynomial,
) -> AffineMinimumCertificate:
    polynomial = _owned_polynomial_snapshot(polynomial)
    if polynomial.degree > 1:
        raise ChoiceFiberError("NONAFFINE_POLYNOMIAL")
    coefficients = polynomial.coefficient_map
    constant = coefficients.get((), 0)
    assignment: list[tuple[str, int]] = []
    minimum = constant
    for choice_id in polynomial.manifest.choice_ids:
        coefficient = coefficients.get((choice_id,), 0)
        sign = -1 if coefficient >= 0 else 1
        assignment.append((choice_id, sign))
        minimum -= abs(coefficient)
    return AffineMinimumCertificate(
        polynomial.manifest.root,
        polynomial.root,
        minimum,
        tuple(assignment),
    )


def verify_affine_certificate(
    polynomial: ChoiceFiberPolynomial,
    certificate: AffineMinimumCertificate,
) -> bool:
    if (
        type(polynomial) is not ChoiceFiberPolynomial
        or type(certificate) is not AffineMinimumCertificate
    ):
        return False
    try:
        owned_polynomial = _owned_polynomial_snapshot(polynomial)
        owned_certificate = AffineMinimumCertificate(
            certificate.manifest_root,
            certificate.polynomial_root,
            certificate.minimum,
            certificate.assignment,
        )
        expected = create_affine_certificate(owned_polynomial)
    except (AttributeError, TypeError, ValueError):
        return False
    return owned_certificate == expected


@dataclass(frozen=True, order=True)
class ForestDpRow:
    choice_id: str
    parent_id: str
    value_if_minus: int
    value_if_plus: int

    def __post_init__(self) -> None:
        _require_text(self.choice_id, "INVALID_FOREST_DP_ROW")
        if type(self.parent_id) is not str:
            raise ChoiceFiberError("INVALID_FOREST_DP_ROW")
        if type(self.value_if_minus) is not int or type(self.value_if_plus) is not int:
            raise ChoiceFiberError("INVALID_FOREST_DP_ROW")


@dataclass(frozen=True)
class ForestMinimumCertificate:
    manifest_root: str
    polynomial_root: str
    minimum: int
    assignment: tuple[tuple[str, int], ...]
    rows: tuple[ForestDpRow, ...]
    roots: tuple[str, ...]

    def __post_init__(self) -> None:
        _require_digest(self.manifest_root, "INVALID_FOREST_CERTIFICATE")
        _require_digest(self.polynomial_root, "INVALID_FOREST_CERTIFICATE")
        if type(self.minimum) is not int:
            raise ChoiceFiberError("INVALID_FOREST_CERTIFICATE")
        _require_assignment(self.assignment, "INVALID_FOREST_CERTIFICATE")
        if type(self.rows) is not tuple or any(type(row) is not ForestDpRow for row in self.rows):
            raise ChoiceFiberError("INVALID_FOREST_CERTIFICATE")
        if type(self.roots) is not tuple or any(
            type(root) is not str or not root for root in self.roots
        ):
            raise ChoiceFiberError("INVALID_FOREST_CERTIFICATE")


def _pairwise_forest(
    polynomial: ChoiceFiberPolynomial,
) -> tuple[
    dict[str, int],
    dict[tuple[str, str], int],
    dict[str, tuple[str, ...]],
    tuple[str, ...],
]:
    if polynomial.degree > 2:
        raise ChoiceFiberError("HIGHER_ORDER_POLYNOMIAL")
    unary = {choice_id: 0 for choice_id in polynomial.manifest.choice_ids}
    edges: dict[tuple[str, str], int] = {}
    for choices, coefficient in polynomial.coefficient_map.items():
        if len(choices) == 1:
            unary[choices[0]] = coefficient
        elif len(choices) == 2:
            left, right = choices
            edge = (left, right)
            edges[edge] = coefficient

    adjacency_lists: dict[str, list[str]] = {
        choice_id: [] for choice_id in polynomial.manifest.choice_ids
    }
    for left, right in edges:
        adjacency_lists[left].append(right)
        adjacency_lists[right].append(left)
    adjacency = {
        choice_id: tuple(sorted(neighbors)) for choice_id, neighbors in adjacency_lists.items()
    }

    visited: set[str] = set()
    roots: list[str] = []
    for candidate in polynomial.manifest.choice_ids:
        if candidate in visited:
            continue
        roots.append(candidate)
        stack = [(candidate, "")]
        while stack:
            node, parent = stack.pop()
            if node in visited:
                raise ChoiceFiberError("INTERACTION_GRAPH_NOT_FOREST")
            visited.add(node)
            for neighbor in reversed(adjacency[node]):
                if neighbor == parent:
                    continue
                if neighbor in visited:
                    raise ChoiceFiberError("INTERACTION_GRAPH_NOT_FOREST")
                stack.append((neighbor, node))
    return unary, edges, adjacency, tuple(roots)


def create_forest_certificate(
    polynomial: ChoiceFiberPolynomial,
) -> ForestMinimumCertificate:
    polynomial = _owned_polynomial_snapshot(polynomial)
    unary, edges, adjacency, roots = _pairwise_forest(polynomial)
    rows: dict[str, ForestDpRow] = {}
    choices: dict[str, dict[int, dict[str, int]]] = {}

    def visit(node: str, parent: str) -> dict[int, int]:
        child_ids = tuple(item for item in adjacency[node] if item != parent)
        child_dp = {child: visit(child, node) for child in child_ids}
        values: dict[int, int] = {}
        choices[node] = {}
        for sign in (-1, 1):
            subtotal = unary[node] * sign
            choices[node][sign] = {}
            for child in child_ids:
                edge = (node, child) if node < child else (child, node)
                candidates = [
                    (
                        child_dp[child][child_sign] + edges[edge] * sign * child_sign,
                        child_sign,
                    )
                    for child_sign in (-1, 1)
                ]
                best_value, best_sign = min(candidates)
                subtotal += best_value
                choices[node][sign][child] = best_sign
            values[sign] = subtotal
        rows[node] = ForestDpRow(node, parent, values[-1], values[1])
        return values

    root_values = {root: visit(root, "") for root in roots}
    assignment: dict[str, int] = {}
    nonconstant_minimum = 0

    def recover(node: str, parent: str, sign: int) -> None:
        assignment[node] = sign
        for child in tuple(item for item in adjacency[node] if item != parent):
            recover(child, node, choices[node][sign][child])

    for root in roots:
        value, sign = min((root_values[root][candidate], candidate) for candidate in (-1, 1))
        nonconstant_minimum += value
        recover(root, "", sign)

    constant = polynomial.coefficient_map.get((), 0)
    minimum = constant + nonconstant_minimum
    assignment_tuple = tuple(sorted(assignment.items()))
    if polynomial.evaluate(dict(assignment_tuple)) != minimum:
        raise AssertionError("forest witness does not attain dynamic-programming minimum")
    return ForestMinimumCertificate(
        polynomial.manifest.root,
        polynomial.root,
        minimum,
        assignment_tuple,
        tuple(sorted(rows.values())),
        roots,
    )


def verify_forest_certificate(
    polynomial: ChoiceFiberPolynomial,
    certificate: ForestMinimumCertificate,
) -> bool:
    if (
        type(polynomial) is not ChoiceFiberPolynomial
        or type(certificate) is not ForestMinimumCertificate
    ):
        return False
    try:
        owned_polynomial = _owned_polynomial_snapshot(polynomial)
        row_source = _bounded_tuple(
            certificate.rows,
            MAX_CHOICE_COUNT,
            "INVALID_FOREST_CERTIFICATE",
        )
        owned_rows = tuple(
            ForestDpRow(
                row.choice_id,
                row.parent_id,
                row.value_if_minus,
                row.value_if_plus,
            )
            for row in row_source
            if type(row) is ForestDpRow
        )
        if len(owned_rows) != len(row_source):
            return False
        owned_certificate = ForestMinimumCertificate(
            certificate.manifest_root,
            certificate.polynomial_root,
            certificate.minimum,
            certificate.assignment,
            owned_rows,
            certificate.roots,
        )
        expected = create_forest_certificate(owned_polynomial)
    except (AttributeError, TypeError, ValueError):
        return False
    return owned_certificate == expected


@dataclass(frozen=True, order=True)
class ComponentMinimum:
    choices: tuple[str, ...]
    minimum: int
    assignment: tuple[tuple[str, int], ...]
    assignments_checked: int

    def __post_init__(self) -> None:
        if (
            type(self.choices) is not tuple
            or any(type(choice) is not str or not choice for choice in self.choices)
            or tuple(sorted(self.choices)) != self.choices
            or len(set(self.choices)) != len(self.choices)
            or type(self.minimum) is not int
            or type(self.assignments_checked) is not int
        ):
            raise ChoiceFiberError("INVALID_COMPONENT_MINIMUM")
        _require_assignment(self.assignment, "INVALID_COMPONENT_MINIMUM")


@dataclass(frozen=True)
class ComponentMinimumCertificate:
    manifest_root: str
    polynomial_root: str
    minimum: int
    components: tuple[ComponentMinimum, ...]

    def __post_init__(self) -> None:
        _require_digest(self.manifest_root, "INVALID_COMPONENT_CERTIFICATE")
        _require_digest(self.polynomial_root, "INVALID_COMPONENT_CERTIFICATE")
        if type(self.minimum) is not int:
            raise ChoiceFiberError("INVALID_COMPONENT_CERTIFICATE")
        if type(self.components) is not tuple or any(
            type(component) is not ComponentMinimum for component in self.components
        ):
            raise ChoiceFiberError("INVALID_COMPONENT_CERTIFICATE")


def _interaction_components(
    polynomial: ChoiceFiberPolynomial,
) -> tuple[tuple[str, ...], ...]:
    adjacency: dict[str, set[str]] = {
        choice_id: set() for choice_id in polynomial.manifest.choice_ids
    }
    for term in polynomial.terms:
        if not term.choices:
            continue
        anchor = term.choices[0]
        for choice_id in term.choices[1:]:
            adjacency[anchor].add(choice_id)
            adjacency[choice_id].add(anchor)
    visited: set[str] = set()
    components: list[tuple[str, ...]] = []
    for start in polynomial.manifest.choice_ids:
        if start in visited:
            continue
        pending = [start]
        current: list[str] = []
        while pending:
            node = pending.pop()
            if node in visited:
                continue
            visited.add(node)
            current.append(node)
            pending.extend(sorted(adjacency[node] - visited, reverse=True))
        components.append(tuple(sorted(current)))
    return tuple(components)


def create_component_certificate(
    polynomial: ChoiceFiberPolynomial,
) -> ComponentMinimumCertificate:
    polynomial = _owned_polynomial_snapshot(polynomial)
    constant = polynomial.coefficient_map.get((), 0)
    component_records: list[ComponentMinimum] = []
    total = constant
    cumulative_work = 0
    for component in _interaction_components(polynomial):
        if len(component) > MAX_EXHAUSTIVE_CHOICES:
            raise ChoiceFiberError("COMPONENT_CAPACITY_EXCEEDED")
        component_set = set(component)
        terms = tuple(
            term
            for term in polynomial.terms
            if term.choices and set(term.choices).issubset(component_set)
        )
        component_term_work = max(
            1,
            sum(max(1, len(term.choices)) for term in terms),
        )
        cumulative_work += (1 << len(component)) * component_term_work
        if cumulative_work > MAX_EXHAUSTIVE_WORK:
            raise ChoiceFiberError("EXHAUSTIVE_WORK_CAPACITY_EXCEEDED")
        best_value: int | None = None
        best_assignment: tuple[tuple[str, int], ...] | None = None
        checks = 0
        for signs in product((-1, 1), repeat=len(component)):
            assignment = tuple(zip(component, signs, strict=True))
            assignment_map = dict(assignment)
            value = 0
            for term in terms:
                term_value = term.coefficient
                for choice_id in term.choices:
                    term_value *= assignment_map[choice_id]
                value += term_value
            checks += 1
            if best_value is None or value < best_value:
                best_value = value
                best_assignment = assignment
        if best_value is None or best_assignment is None:
            raise AssertionError("interaction component unexpectedly empty")
        total += best_value
        component_records.append(ComponentMinimum(component, best_value, best_assignment, checks))
    return ComponentMinimumCertificate(
        polynomial.manifest.root,
        polynomial.root,
        total,
        tuple(component_records),
    )


def verify_component_certificate(
    polynomial: ChoiceFiberPolynomial,
    certificate: ComponentMinimumCertificate,
) -> bool:
    if (
        type(polynomial) is not ChoiceFiberPolynomial
        or type(certificate) is not ComponentMinimumCertificate
    ):
        return False
    try:
        owned_polynomial = _owned_polynomial_snapshot(polynomial)
        component_source = _bounded_tuple(
            certificate.components,
            MAX_CHOICE_COUNT,
            "INVALID_COMPONENT_CERTIFICATE",
        )
        owned_components = tuple(
            ComponentMinimum(
                component.choices,
                component.minimum,
                component.assignment,
                component.assignments_checked,
            )
            for component in component_source
            if type(component) is ComponentMinimum
        )
        if len(owned_components) != len(component_source):
            return False
        owned_certificate = ComponentMinimumCertificate(
            certificate.manifest_root,
            certificate.polynomial_root,
            certificate.minimum,
            owned_components,
        )
        expected = create_component_certificate(owned_polynomial)
    except (AttributeError, TypeError, ValueError):
        return False
    return expected == owned_certificate


def certificate_size_bytes(certificate: object) -> int:
    if hasattr(certificate, "__dict__"):
        value = _dataclass_to_value(certificate)
    else:
        value = certificate
    return len(_framed("zenodex.choice-fiber-certificate.v1", value))


def _dataclass_to_value(value: object) -> object:
    if hasattr(value, "__dataclass_fields__"):
        return {key: _dataclass_to_value(getattr(value, key)) for key in value.__dataclass_fields__}
    if isinstance(value, tuple):
        return [_dataclass_to_value(item) for item in value]
    return value
