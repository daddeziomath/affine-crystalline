/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.Universal

/-!
# Independence of the choice of a divided power envelope

Let `(A, I, γ)` be a divided power ring, `P` an `A`-algebra and `J ⊆ P` an ideal.
A `DPEnvelopeChoice γ J` bundles an `A`-algebra `D`, a map `φ : P → D`, an ideal
`K ⊇ J D + I D` and divided powers `δ` on `K` satisfying the universal property
`IsDPEnvelope`. These structures, the existence class `HasDPEnvelope` and the
chosen envelope `dpEnvelope` are defined in `AffineCrystalline.PDDifferentials`.

In this file we show that any two choices are related by a unique isomorphism
compatible with the structure maps and the divided powers, so that every
construction depending only on the universal property is independent of the
choice.

## Main definitions

* `DPEnvelopeChoice.comparison`: the unique divided power `A`-algebra map
  `E → F` between two envelope choices lying over `P`.

## Main results

* `DPEnvelopeChoice.comparison_spec`: the comparison map lies over `P` and is a
  divided power morphism.
* `DPEnvelopeChoice.eq_comparison`, `DPEnvelopeChoice.hom_ext`: uniqueness of
  compatible maps between two choices.
* `DPEnvelopeChoice.comparison_comp_comparison_left`,
  `DPEnvelopeChoice.comparison_comp_comparison_right`: the comparison maps are
  mutually inverse.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
-/

open DividedPowers

universe u

/-! ## Comparison maps between choices -/

namespace DPEnvelopeChoice

/--
The unique divided power `A`-algebra map from one envelope choice to another
lying over `P`, provided by the universal property of the source.
-/
noncomputable def comparison {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {P : Type u} [CommRing P] [Algebra A P] (J : Ideal P)
    (E F : DPEnvelopeChoice γ J) :
    @AlgHom A E.carrier F.carrier _ E.commRing.toSemiring F.commRing.toSemiring
      E.algebra F.algebra := by
  letI := E.commRing
  letI := E.algebra
  letI := F.commRing
  letI := F.algebra
  exact IsDPEnvelope.comparison γ J E.map E.dividedPowers E.isEnvelope
    F.map F.dividedPowers F.isEnvelope.le F.isEnvelope.compat

/-- The comparison map lies over the two presentation maps and is a DP map. -/
theorem comparison_spec {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {P : Type u} [CommRing P] [Algebra A P] (J : Ideal P)
    (E F : DPEnvelopeChoice γ J) :
    letI := E.commRing
    letI := E.algebra
    letI := F.commRing
    letI := F.algebra
    (comparison γ J E F).comp E.map = F.map ∧
      IsDPMorphism E.dividedPowers F.dividedPowers
        (comparison γ J E F).toRingHom := by
  letI := E.commRing
  letI := E.algebra
  letI := F.commRing
  letI := F.algebra
  exact IsDPEnvelope.comparison_spec γ J E.map E.dividedPowers E.isEnvelope
    F.map F.dividedPowers F.isEnvelope.le F.isEnvelope.compat

/-- Any compatible map between two choices is the comparison map. -/
theorem eq_comparison {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {P : Type u} [CommRing P] [Algebra A P] (J : Ideal P)
    (E F : DPEnvelopeChoice γ J)
    (ψ : @AlgHom A E.carrier F.carrier _ E.commRing.toSemiring F.commRing.toSemiring
      E.algebra F.algebra)
    (hψ :
      letI := E.commRing
      letI := E.algebra
      letI := F.commRing
      letI := F.algebra
      ψ.comp E.map = F.map ∧
        IsDPMorphism E.dividedPowers F.dividedPowers ψ.toRingHom) :
    ψ = comparison γ J E F := by
  letI := E.commRing
  letI := E.algebra
  letI := F.commRing
  letI := F.algebra
  exact IsDPEnvelope.eq_comparison γ J E.map E.dividedPowers E.isEnvelope
    F.map F.dividedPowers F.isEnvelope.le F.isEnvelope.compat ψ hψ

/-- Two compatible maps between two choices are equal. -/
theorem hom_ext {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {P : Type u} [CommRing P] [Algebra A P] (J : Ideal P)
    (E F : DPEnvelopeChoice γ J)
    (ψ₁ ψ₂ : @AlgHom A E.carrier F.carrier _ E.commRing.toSemiring F.commRing.toSemiring
      E.algebra F.algebra)
    (hψ₁ :
      letI := E.commRing
      letI := E.algebra
      letI := F.commRing
      letI := F.algebra
      ψ₁.comp E.map = F.map ∧
        IsDPMorphism E.dividedPowers F.dividedPowers ψ₁.toRingHom)
    (hψ₂ :
      letI := E.commRing
      letI := E.algebra
      letI := F.commRing
      letI := F.algebra
      (ψ₂.comp E.map = F.map ∧
        IsDPMorphism E.dividedPowers F.dividedPowers ψ₂.toRingHom)) :
    ψ₁ = ψ₂ := by
  letI := E.commRing
  letI := E.algebra
  letI := F.commRing
  letI := F.algebra
  exact IsDPEnvelope.eq_of_comparison γ J E.map E.dividedPowers E.isEnvelope
    F.map F.dividedPowers F.isEnvelope.le F.isEnvelope.compat ψ₁ ψ₂ hψ₁ hψ₂

/-! ## The two choices are uniquely related in both directions -/

/-- The comparison maps compose to the identity on the source choice. -/
theorem comparison_comp_comparison_left {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {P : Type u} [CommRing P] [Algebra A P] (J : Ideal P)
    (E F : DPEnvelopeChoice γ J) :
    letI := E.commRing
    letI := E.algebra
    letI := F.commRing
    letI := F.algebra
    (comparison γ J F E).comp (comparison γ J E F) = AlgHom.id A E.carrier := by
  letI := E.commRing
  letI := E.algebra
  letI := F.commRing
  letI := F.algebra
  apply IsDPEnvelope.eq_of_comparison γ J E.map E.dividedPowers E.isEnvelope
    E.map E.dividedPowers E.isEnvelope.le E.isEnvelope.compat
  · exact IsDPEnvelope.comp_spec E.map E.dividedPowers F.map F.dividedPowers
      E.map E.dividedPowers (comparison γ J E F) (comparison γ J F E)
      (comparison_spec γ J E F) (comparison_spec γ J F E)
  · exact IsDPEnvelope.identity_spec E.map E.dividedPowers

/-- The comparison maps compose to the identity on the target choice. -/
theorem comparison_comp_comparison_right {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) {P : Type u} [CommRing P] [Algebra A P] (J : Ideal P)
    (E F : DPEnvelopeChoice γ J) :
    letI := E.commRing
    letI := E.algebra
    letI := F.commRing
    letI := F.algebra
    (comparison γ J E F).comp (comparison γ J F E) = AlgHom.id A F.carrier := by
  letI := E.commRing
  letI := E.algebra
  letI := F.commRing
  letI := F.algebra
  apply IsDPEnvelope.eq_of_comparison γ J F.map F.dividedPowers F.isEnvelope
    F.map F.dividedPowers F.isEnvelope.le F.isEnvelope.compat
  · exact IsDPEnvelope.comp_spec F.map F.dividedPowers E.map E.dividedPowers
      F.map F.dividedPowers (comparison γ J F E) (comparison γ J E F)
      (comparison_spec γ J F E) (comparison_spec γ J E F)
  · exact IsDPEnvelope.identity_spec F.map F.dividedPowers

end DPEnvelopeChoice
