/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.PDDifferentials

/-!
# PD derivations out of a PD envelope

Let `φ : B → (D, K, δ)` have the universal property of the PD envelope of
`(B, J)` compatible with `γ`: it is initial among `A`-algebra maps to PD
algebras `(D', K', δ')` sending `J` into `K'` compatibly with `γ`.  Then every
`A`-linear map `v : B → M` to a `D`-module `M` which satisfies the Leibniz rule
along `φ` extends uniquely to a PD derivation `θ : D → M` with `θ ∘ φ = v`.

This is `existsUnique_pdDerivation_extension`, restated without assuming that
`B → D` is an algebra structure nor that `M` is a `B`-module.  It applies for
instance to `D(n) = Ocris(X^{(e)}(n))`, which is constructed as the envelope of a
truncation but has the universal property of the envelope of the polynomial
presentation `A[x_{i,c}] → C`.

## Main results

* `existsUnique_pdDerivation_of_initial`: existence and uniqueness of the PD
  derivation extending `v`.

## References

* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
-/

open DividedPowers

universe u

namespace AffineCrystalline

/-- If `φ : B → (D, K, δ)` has the universal property of the PD envelope of
`(B, J)` compatible with `γ` (`hUP`), then every `A`-linear `v : B → M`
satisfying the Leibniz rule along `φ` extends uniquely to a PD derivation
`θ : D → M` with `θ ∘ φ = v`. -/
theorem existsUnique_pdDerivation_of_initial
    {A B D M : Type u} [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    [AddCommGroup M] [Module D M] [Module A M] [IsScalarTower A D M]
    {I : Ideal A} {γ : DividedPowers I} (φ : B →ₐ[A] D) (J : Ideal B) {K : Ideal D}
    (δ : DividedPowers K)
    (hcontain : J.map φ.toRingHom ⊔ I.map (algebraMap A D) ≤ K)
    (hcompat : IsDPMorphism γ δ (algebraMap A D))
    (hUP : ∀ {D' : Type u} [CommRing D'] [Algebra A D'] (K' : Ideal D') (φ' : B →ₐ[A] D')
      (δ' : DividedPowers K'), J.map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K' →
        IsDPMorphism γ δ' (algebraMap A D') →
          ∃! ψ : D →ₐ[A] D', ψ.comp φ = φ' ∧ IsDPMorphism δ δ' ψ.toRingHom)
    (v : B →ₗ[A] M) (hv : ∀ b b' : B, v (b * b') = φ b • v b' + φ b' • v b) :
    ∃! θ : D →ₗ[A] M, IsPDDerivation δ M θ ∧ θ.comp φ.toLinearMap = v := by
  letI : Module Dᵐᵒᵖ M :=
    Module.compHom M ((RingEquiv.toOpposite D).symm : Dᵐᵒᵖ ≃+* D).toRingHom
  haveI : IsCentralScalar D M := ⟨fun _ _ ↦ rfl⟩
  letI : Algebra B D := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  letI : Module B M := Module.compHom M φ.toRingHom
  haveI : IsScalarTower B D M := ⟨fun b d m ↦ mul_smul (φ b) d m⟩
  haveI : IsScalarTower A B M := ⟨fun a b m ↦ by
    change φ (a • b) • m = a • (φ b • m)
    rw [map_smul, smul_assoc]⟩
  exact existsUnique_pdDerivation_extension (M := M) ⟨hcontain, hcompat, hUP⟩
    { toLinearMap := v
      map_one_eq_zero' := by simpa using hv 1 1
      leibniz' := hv }

end AffineCrystalline
