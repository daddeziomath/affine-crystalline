/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.PDDifferentials
import AffineCrystalline.Envelope.Universal

/-!
# The comparison of divided power differentials as a linear equivalence

Let `A → B → D` be ring maps and `δ` divided powers on an ideal of `D`. The
canonical `D`-linear map `D ⊗_B Ω_{B/A} → Ω_{D/A,δ}`, defined in
`AffineCrystalline.PDDifferentials` as `pdKaehlerDpEnvelopeComparison`, is
bijective when `D` is a divided power envelope of `B` (`pdKaehler_dpEnvelope`).
This file packages a bijectivity proof as a linear equivalence and records
the uniqueness of envelopes up to unique isomorphism.

## Main definitions

* `pdKaehlerDpEnvelopeEquiv`: the comparison `D ⊗_B Ω_{B/A} ≃ Ω_{D/A,δ}`, given a
  proof of bijectivity.
* `pdKaehlerDpEnvelopeComparisonInverse`: its inverse as a linear map.
* `IsDPEnvelope.comparisonEquiv`: the `A`-algebra isomorphism between two
  divided power envelopes of the same pair `(P, J)`.

## Main results

* `pdKaehlerDpEnvelopeComparisonInverse_comp_comparison`,
  `pdKaehlerDpEnvelopeComparison_comp_inverse`: the two composites are the
  identity.
* `linearEquiv_inverse_naturality`: inverses of linear equivalences in a
  commutative square again form a commutative square.
* `IsDPEnvelope.comparisonEquiv_apply`: the isomorphism is the comparison map
  given by the universal property.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open scoped TensorProduct
open DividedPowers

universe u

/-! ### The comparison as a linear equivalence -/

/-- The canonical comparison `D ⊗_B Ω_{B/A} → Ω_{D/A,δ}` as a `D`-linear
equivalence, given a proof that it is bijective (for instance
`pdKaehler_dpEnvelope` when `D` is a divided power envelope). -/
noncomputable def pdKaehlerDpEnvelopeEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    {J_D : Ideal D} (δ : DividedPowers J_D)
    (hcomparison :
      Function.Bijective
        (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ)) :
    (D ⊗[B] Ω[B⁄A]) ≃ₗ[D] PDKaehler (A := A) δ :=
  LinearEquiv.ofBijective
    (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ) hcomparison

/-- The bundled equivalence has exactly the canonical comparison as its
underlying linear map. -/
theorem pdKaehlerDpEnvelopeEquiv_spec
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    {J_D : Ideal D} (δ : DividedPowers J_D)
    (hcomparison :
      Function.Bijective
        (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ)) :
    (pdKaehlerDpEnvelopeEquiv δ hcomparison).toLinearMap =
      pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ := by
  rfl

/-- The inverse linear map supplied by the packaged comparison equivalence. -/
noncomputable def pdKaehlerDpEnvelopeComparisonInverse
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    {J_D : Ideal D} (δ : DividedPowers J_D)
    (hcomparison :
      Function.Bijective
        (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ)) :
    PDKaehler (A := A) δ →ₗ[D] (D ⊗[B] Ω[B⁄A]) :=
  (pdKaehlerDpEnvelopeEquiv δ hcomparison).symm.toLinearMap

/-- The comparison composed with its inverse is the identity of `Ω_{D/A,δ}`. -/
theorem pdKaehlerDpEnvelopeComparisonInverse_comp_comparison
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    {J_D : Ideal D} (δ : DividedPowers J_D)
    (hcomparison :
      Function.Bijective
        (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ)) :
    (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ).comp
        (pdKaehlerDpEnvelopeComparisonInverse δ hcomparison) =
      LinearMap.id := by
  apply LinearMap.ext
  intro ω
  exact (pdKaehlerDpEnvelopeEquiv δ hcomparison).apply_symm_apply ω

/-- The inverse composed with the comparison is the identity of
`D ⊗_B Ω_{B/A}`. -/
theorem pdKaehlerDpEnvelopeComparison_comp_inverse
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {D : Type u} [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    {J_D : Ideal D} (δ : DividedPowers J_D)
    (hcomparison :
      Function.Bijective
        (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ)) :
    (pdKaehlerDpEnvelopeComparisonInverse δ hcomparison).comp
        (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro η
  exact (pdKaehlerDpEnvelopeEquiv δ hcomparison).symm_apply_apply η

/-! ### Naturality of inverse equivalences -/

/-- If `g ∘ e = e' ∘ f` for linear equivalences `e`, `e'`, then
`f ∘ e⁻¹ = e'⁻¹ ∘ g`. This is used to compare two instances of the comparison
equivalence related by a change of coefficients. -/
theorem linearEquiv_inverse_naturality
    {R M M' N N' : Type u} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (e : M ≃ₗ[R] N) (e' : M' ≃ₗ[R] N')
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (h : g.comp e.toLinearMap = e'.toLinearMap.comp f) :
    f.comp e.symm.toLinearMap = e'.symm.toLinearMap.comp g := by
  ext y
  apply e'.injective
  simpa [LinearMap.comp_apply] using
    (congrArg (fun k ↦ k (e.symm y)) h).symm

/-! ### Uniqueness of divided power envelopes -/

/-- Two divided power envelopes `(D, φ, K, δ)` and `(D', φ', K', δ')` of the same pair
`(P, J)` are isomorphic as `A`-algebras, via the comparison map given by the
universal property. -/
noncomputable def IsDPEnvelope.comparisonEquiv
    {A P D D' : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    [CommRing P] [Algebra A P] (J : Ideal P)
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    (hD : IsDPEnvelope γ J D φ K δ)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    (hD' : IsDPEnvelope γ J D' φ' K' δ') : D ≃ₐ[A] D' := by
  let ψ := IsDPEnvelope.comparison γ J φ δ hD φ' δ' hD'.le hD'.compat
  let χ := IsDPEnvelope.comparison γ J φ' δ' hD' φ δ hD.le hD.compat
  have hleft : χ.comp ψ = AlgHom.id A D := by
    apply IsDPEnvelope.eq_of_comparison γ J φ δ hD φ δ hD.le hD.compat
    · exact IsDPEnvelope.comp_spec φ δ φ' δ' φ δ ψ χ
        (IsDPEnvelope.comparison_spec γ J φ δ hD φ' δ' hD'.le hD'.compat)
        (IsDPEnvelope.comparison_spec γ J φ' δ' hD' φ δ hD.le hD.compat)
    · exact IsDPEnvelope.identity_spec φ δ
  have hright : ψ.comp χ = AlgHom.id A D' := by
    apply IsDPEnvelope.eq_of_comparison γ J φ' δ' hD' φ' δ' hD'.le hD'.compat
    · exact IsDPEnvelope.comp_spec φ' δ' φ δ φ' δ' χ ψ
        (IsDPEnvelope.comparison_spec γ J φ' δ' hD' φ δ hD.le hD.compat)
        (IsDPEnvelope.comparison_spec γ J φ δ hD φ' δ' hD'.le hD'.compat)
    · exact IsDPEnvelope.identity_spec φ' δ'
  apply AlgEquiv.ofBijective ψ
  rw [Function.bijective_iff_has_inverse]
  refine ⟨χ, ?_, ?_⟩
  · intro x
    exact congrArg (fun k : D →ₐ[A] D ↦ k x) hleft
  · intro y
    exact congrArg (fun k : D' →ₐ[A] D' ↦ k y) hright

/-- The isomorphism `IsDPEnvelope.comparisonEquiv` agrees with the comparison
map `IsDPEnvelope.comparison`. -/
theorem IsDPEnvelope.comparisonEquiv_apply
    {A P D D' : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    [CommRing P] [Algebra A P] (J : Ideal P)
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    (hD : IsDPEnvelope γ J D φ K δ)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    (hD' : IsDPEnvelope γ J D' φ' K' δ') (x : D) :
    IsDPEnvelope.comparisonEquiv γ J φ δ hD φ' δ' hD' x =
      IsDPEnvelope.comparison γ J φ δ hD φ' δ' hD'.le hD'.compat x := by
  rfl
