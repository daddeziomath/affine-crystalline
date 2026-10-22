/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.PDDifferentials

/-!
# Representability of divided power derivations

The universal property of `Ω_{B,δ}` (`PDKaehler.lift`, `PDKaehler.lift_comp`,
`PDKaehler.lift_unique`) is repackaged as a natural bijection: for every
`B`-module `M`, precomposition with the universal derivation `pdD` gives an
equivalence between `B`-linear maps `Ω_{B,δ} → M` and divided power
`A`-derivations `B → M`. In other words, `Ω_{B,δ}` represents the functor of
divided power derivations.

## Main definitions

* `PDDifferentials.pdKaehlerDerivationEquiv`: the equivalence
  `(Ω_{B,δ} →ₗ[B] M) ≃ {θ : B →ₗ[A] M // IsPDDerivation δ M θ}`.

## Main results

* `PDDifferentials.isPDDerivation_comp_pdD`: `g ∘ pdD` is a divided power derivation
  for every `B`-linear map `g` out of `Ω_{B,δ}`.

## References

* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
-/

universe u

namespace PDDifferentials

open DividedPowers

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)
variable (M : Type u) [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M]

/-- For a `B`-linear map `g : Ω_{B,δ} → M`, the composition `g ∘ pdD` is a divided
power derivation. -/
theorem isPDDerivation_comp_pdD
    (g : PDKaehler (A := A) δ →ₗ[B] M) :
    IsPDDerivation δ M ((g.restrictScalars A) ∘ₗ pdD δ) := by
  constructor
  · intro b b'
    change g (pdD δ (b * b')) =
      b • g (pdD δ b') + b' • g (pdD δ b)
    rw [(pdD_isPDDerivation δ).leibniz, map_add, g.map_smul, g.map_smul]
  · intro n hn x hx
    change g (pdD δ (δ.dpow n x)) =
      δ.dpow (n - 1) x • g (pdD δ x)
    rw [(pdD_isPDDerivation δ).dpow n hn x hx, g.map_smul]

/-- `Ω_{B,δ}` represents divided power derivations: `g ↦ g ∘ pdD` is an
equivalence between `B`-linear maps `Ω_{B,δ} → M` and divided power derivations
`B → M`, with inverse `PDKaehler.lift`. -/
noncomputable def pdKaehlerDerivationEquiv :
    (PDKaehler (A := A) δ →ₗ[B] M) ≃
      { θ : B →ₗ[A] M // IsPDDerivation δ M θ } where
  toFun g :=
    ⟨(g.restrictScalars A) ∘ₗ pdD δ, isPDDerivation_comp_pdD δ M g⟩
  invFun θ := PDKaehler.lift δ M θ.1 θ.2
  left_inv g := by
    symm
    exact PDKaehler.lift_unique δ M
      ((g.restrictScalars A) ∘ₗ pdD δ)
      (isPDDerivation_comp_pdD δ M g) g rfl
  right_inv θ := by
    apply Subtype.ext
    exact PDKaehler.lift_comp δ M θ.1 θ.2

@[simp]
theorem pdKaehlerDerivationEquiv_apply
    (g : PDKaehler (A := A) δ →ₗ[B] M) :
    pdKaehlerDerivationEquiv δ M g =
      ⟨(g.restrictScalars A) ∘ₗ pdD δ, isPDDerivation_comp_pdD δ M g⟩ :=
  rfl

@[simp]
theorem pdKaehlerDerivationEquiv_symm_apply
    (θ : { θ : B →ₗ[A] M // IsPDDerivation δ M θ }) :
    (pdKaehlerDerivationEquiv δ M).symm θ =
      PDKaehler.lift δ M θ.1 θ.2 :=
  rfl

theorem pdKaehlerDerivationEquiv_comp_pdD
    (g : PDKaehler (A := A) δ →ₗ[B] M) :
    ((pdKaehlerDerivationEquiv δ M g).1) =
      (g.restrictScalars A) ∘ₗ pdD δ :=
  rfl

theorem pdKaehlerDerivationEquiv_symm_comp_pdD
    (θ : { θ : B →ₗ[A] M // IsPDDerivation δ M θ }) :
    ((pdKaehlerDerivationEquiv δ M).symm θ).restrictScalars A ∘ₗ pdD δ =
      θ.1 :=
  PDKaehler.lift_comp δ M θ.1 θ.2

end PDDifferentials
