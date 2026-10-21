import Mathlib.Tactic

/-!
# Typed deterministic parser boundary

A consensus parser should not return a set of possible parses.  It should return
at most one typed value and one unconsumed suffix.  This file records the small,
implementation-independent theorems used by the ZenoDEX authority boundary:

* successful parses are unique;
* deterministic parsing is closed under typed sequential composition;
* disjoint FIRST predicates exclude branch ambiguity; and
* an exact full-consumption decode/encode round trip makes the encoder injective.

The concrete byte decoder remains outside this theorem.  Runtime evidence must
establish the round-trip premise for the actual canonical codec.
-/

namespace ZenoDEX.TypedDeterministicParser

/-- One typed parse result and the unconsumed token suffix. -/
structure ParseResult (Token Output : Type*) where
  value : Output
  rest : List Token
deriving DecidableEq, Repr

/-- A deterministic parser is a partial function, not a relation or parse forest. -/
abbrev Parser (Token Output : Type*) :=
  List Token → Option (ParseResult Token Output)

/-- A parser that consumes nothing and returns one typed value. -/
def pure {Token Output : Type*} (value : Output) : Parser Token Output :=
  fun input => some ⟨value, input⟩

/-- A parser that rejects every input. -/
def fail {Token Output : Type*} : Parser Token Output :=
  fun _ => none

/-- Typed sequential composition. -/
def bind {Token A B : Type*}
    (parser : Parser Token A)
    (next : A → Parser Token B) : Parser Token B :=
  fun input =>
    match parser input with
    | none => none
    | some result => next result.value result.rest

/-- Map a pure typed function over a deterministic parser. -/
def map {Token A B : Type*}
    (transform : A → B)
    (parser : Parser Token A) : Parser Token B :=
  bind parser (fun value => pure (transform value))

/-- Relational spelling of one successful parse, useful in specifications. -/
def Accepts {Token Output : Type*}
    (parser : Parser Token Output)
    (input : List Token)
    (value : Output)
    (rest : List Token) : Prop :=
  parser input = some ⟨value, rest⟩

/-- A successful authority parse must consume the complete transport. -/
def AcceptsAll {Token Output : Type*}
    (parser : Parser Token Output)
    (input : List Token)
    (value : Output) : Prop :=
  Accepts parser input value []

/-- One deterministic parser invocation cannot produce two different results. -/
theorem accepts_unique
    {Token Output : Type*}
    {parser : Parser Token Output}
    {input : List Token}
    {value₁ value₂ : Output}
    {rest₁ rest₂ : List Token}
    (h₁ : Accepts parser input value₁ rest₁)
    (h₂ : Accepts parser input value₂ rest₂) :
    value₁ = value₂ ∧ rest₁ = rest₂ := by
  have hresult :
      (ParseResult.mk value₁ rest₁ : ParseResult Token Output) =
        ParseResult.mk value₂ rest₂ :=
    Option.some.inj (h₁.symm.trans h₂)
  cases hresult
  exact ⟨rfl, rfl⟩

/-- Complete parses are unique at the typed value level. -/
theorem acceptsAll_unique
    {Token Output : Type*}
    {parser : Parser Token Output}
    {input : List Token}
    {value₁ value₂ : Output}
    (h₁ : AcceptsAll parser input value₁)
    (h₂ : AcceptsAll parser input value₂) :
    value₁ = value₂ :=
  (accepts_unique h₁ h₂).1

/-- The relational semantics of typed sequential parser composition. -/
theorem accepts_bind_iff
    {Token A B : Type*}
    {parser : Parser Token A}
    {next : A → Parser Token B}
    {input : List Token}
    {output : B}
    {rest : List Token} :
    Accepts (bind parser next) input output rest ↔
      ∃ intermediate middle,
        Accepts parser input intermediate middle ∧
          Accepts (next intermediate) middle output rest := by
  cases hparse : parser input with
  | none =>
      simp [Accepts, bind, hparse]
  | some result =>
      rcases result with ⟨intermediate, middle⟩
      simp [Accepts, bind, hparse]

/-- The pure parser has exactly the supplied value and unchanged suffix. -/
@[simp] theorem accepts_pure_iff
    {Token Output : Type*}
    {value parsed : Output}
    {input rest : List Token} :
    Accepts (pure value : Parser Token Output) input parsed rest ↔
      parsed = value ∧ rest = input := by
  simp [Accepts, pure, eq_comm]

/-- Two branch recognizers have disjoint FIRST sets. -/
def FirstDisjoint {Token : Type*}
    (left right : Token → Prop) : Prop :=
  ∀ token, left token → right token → False

/-- FIRST-set disjointness is symmetric. -/
theorem firstDisjoint_symm
    {Token : Type*}
    {left right : Token → Prop}
    (h : FirstDisjoint left right) :
    FirstDisjoint right left := by
  intro token hright hleft
  exact h token hleft hright

/-- A token cannot activate both alternatives of a disjoint typed choice. -/
theorem firstDisjoint_no_ambiguity
    {Token : Type*}
    {left right : Token → Prop}
    (h : FirstDisjoint left right)
    (token : Token) :
    ¬ (left token ∧ right token) := by
  rintro ⟨hleft, hright⟩
  exact h token hleft hright

/-- Canonical acceptance couples full parsing with exact re-encoding. -/
def CanonicallyAccepts {Token Output : Type*}
    (encode : Output → List Token)
    (parser : Parser Token Output)
    (input : List Token)
    (value : Output) : Prop :=
  AcceptsAll parser input value ∧ encode value = input

/-- One accepted canonical transport has at most one typed interpretation. -/
theorem canonicalAcceptance_unique
    {Token Output : Type*}
    {encode : Output → List Token}
    {parser : Parser Token Output}
    {input : List Token}
    {value₁ value₂ : Output}
    (h₁ : CanonicallyAccepts encode parser input value₁)
    (h₂ : CanonicallyAccepts encode parser input value₂) :
    value₁ = value₂ :=
  acceptsAll_unique h₁.1 h₂.1

/--
If decoding the output of the encoder returns the original typed value and
consumes all bytes, then the encoder is injective.
-/
theorem encode_injective_of_roundtrip
    {Token Output : Type*}
    (encode : Output → List Token)
    (decode : Parser Token Output)
    (hroundtrip : ∀ value, AcceptsAll decode (encode value) value) :
    Function.Injective encode := by
  intro left right hencoded
  have hleft : AcceptsAll decode (encode right) left := by
    simpa [hencoded] using hroundtrip left
  exact acceptsAll_unique hleft (hroundtrip right)

end ZenoDEX.TypedDeterministicParser
