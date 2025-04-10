# Representing a Well-Scoped Dependent Syntax with Inductive-Inductive Types and Small Induction-Recursion

This is the code artifact for the paper.

- `Syntax`
  Definition of the syntax, using induction-induction.
  This contains the definition of `Con`, `Ty`, `Var`, `Tm`.
- `Wkn`
  Definition of `Wkn`, using induction-recursion.
- `Sub`
  Definition of `Sub`, using induction-recursion.
- `Lemmas`
  Five syntactic "soundness lemmas".
  Uses extensions of contexts.
  - `Extension`

  Uses "indexed equalities" together with appropriate constructors for such
  equalities.
  - `IdxEq`
  - `MapHeq`

  The lemmas are
  - `UpSub`
  - `UpWkn`
  - `WknSub`
  - `SubSub`
  - `SubWkn`
- `DefEq`
  A notion of definitional equality. Note, howerver, that this is actually a
  notion of reduction and it is not transitive. This is not a problem in the
  end, as the conversion (cast) rule allows to chain such equalities.

  This module also contains a proof of admissibility of substitutions with
  respect to this notion of definitional equality (`defeq-map-wkn-*` and
  `defeq-map-sub-*`).
- `Typing`
  Definition of typing constraints: `_⊢`, `_⊢_`, `_⊢_∈v_`, `_⊢_∈_`.

  This module also contains a proof of admissibility of substitutions:
  `map-wkn-*` and `map-sub-*`.

