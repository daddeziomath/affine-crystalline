/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.Existence

/-!
# The divided power envelope of the zero ideal

Let `(A, I, γ)` be a divided power ring. The divided power envelope of the zero
ideal of `P = A` is `A` itself, with the divided powers `γ`: an `A`-algebra map
out of `A` is unique, and the structure map of a divided power `A`-algebra is
compatible with `γ` by assumption. In particular `HasDPEnvelope γ ⊥` holds.

## Main definitions

* `identityDPEnvelopeChoice`: `(A, id, I, γ)` as a `DPEnvelopeChoice γ ⊥`.

## Main results

* `identity_presentation_ideal`: for the identity of `A`, `⊥ · A + I · A = I`.
* `identity_isDPEnvelope`: `(A, id, I, γ)` is a divided power envelope of `(A, ⊥)`.
* `identity_hasDPEnvelope`: the envelope of `(A, ⊥)` exists.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
-/

open DividedPowers

universe u

/-- For the identity `A → A`, the ideal `⊥ · A + I · A` is `I`. -/
theorem identity_presentation_ideal {A : Type u} [CommRing A] {I : Ideal A} :
    (⊥ : Ideal A).map (AlgHom.id A A).toRingHom ⊔ I.map (algebraMap A A) = I := by
  simp

/-- The ring `A`, with the identity map, the ideal `I` and the divided powers `γ`,
is the divided power envelope of the zero ideal of `A`. In the initiality clause,
the only `A`-algebra map out of `A` is `Algebra.ofId A D'`. -/
theorem identity_isDPEnvelope {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) :
    @IsDPEnvelope A _ I γ A _ _ (⊥ : Ideal A) A _ _ (AlgHom.id A A) I γ := by
  refine
    { le := (identity_presentation_ideal (A := A) (I := I)).le
      compat := ?_
      isInitial := ?_ }
  · simpa [DividedPowers.DPMorphism.id] using
      (DividedPowers.DPMorphism.id γ).isDPMorphism
  · intro D' _ _ K' φ' δ' _hcontain hφ'
    refine ⟨Algebra.ofId A D', ⟨Subsingleton.elim _ _, hφ'⟩, ?_⟩
    intro ψ _hψ
    exact Subsingleton.elim ψ (Algebra.ofId A D')

/-! ### Packaging the identity case -/

/-- The envelope `(A, id, I, γ)` of the zero ideal, as a `DPEnvelopeChoice`. -/
noncomputable def identityDPEnvelopeChoice {A : Type u} [CommRing A]
    {I : Ideal A} (γ : DividedPowers I) : DPEnvelopeChoice γ (⊥ : Ideal A) where
  carrier := A
  commRing := inferInstance
  algebra := inferInstance
  map := AlgHom.id A A
  pdIdeal := I
  dividedPowers := γ
  isEnvelope := identity_isDPEnvelope γ

/-- The divided power envelope of the zero ideal of `A` exists. -/
theorem identity_hasDPEnvelope {A : Type u} [CommRing A] {I : Ideal A}
    (γ : DividedPowers I) : HasDPEnvelope γ (⊥ : Ideal A) :=
  ⟨⟨identityDPEnvelopeChoice γ⟩⟩
