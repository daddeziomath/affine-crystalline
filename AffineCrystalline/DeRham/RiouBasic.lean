/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.Abstract
import AffineCrystalline.PDDifferentials
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Graded terms and the degree-zero differential

In Riou's approach, the algebraic de Rham complex of an `A`-algebra `B` is a
complex of `A`-modules whose `n`-th term is an exterior power `⋀[B]^n M` over
`B` of a `B`-module `M` of differentials (here `M = Ω[B⁄A]` or
`M = PDKaehler δ`), with scalars restricted to `A`.

This file sets up these graded terms for an arbitrary `B`-module `M`, the
canonical identifications `⋀[B]^0 M ≃ B` and `⋀[B]^1 M ≃ M`, and the
degree-zero differential `B → ⋀[B]^1 M` attached to an `A`-derivation
`B → M`. We specialise it to the universal derivation `d : B → Ω[B⁄A]` and to
the universal divided-power derivation `pdD δ : B → PDKaehler δ`.

## Main definitions

* `Forms M n`, `formsOverBase M n`: the term `⋀[B]^n M`, as a type and as an
  object of `ModuleCat A`.
* `zeroFormsEquiv M`, `oneFormsEquiv M`: the `A`-linear equivalences
  `⋀[B]^0 M ≃ B` and `⋀[B]^1 M ≃ M`.
* `derivationToDegreeOne M der`: the map `B → ⋀[B]^1 M` induced by an
  `A`-derivation `der : B → M`.
* `ordinaryDerivationToDegreeOne`: the degree-zero de Rham differential.
* `pdDerivation δ`, `pdDerivationToDegreeOne δ`: the universal divided-power
  derivation as a `Derivation`, and the induced map to `⋀[B]^1 (PDKaehler δ)`.

## Main results

* `oneFormsEquiv_comp_derivationToDegreeOne`: `derivationToDegreeOne M der`
  recovers `der` under `⋀[B]^1 M ≃ M`.
* `ordinaryDerivationToDegreeOne_spec`,
  `oneFormsEquiv_comp_pdDerivationToDegreeOne`: the two special cases.

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.
-/

open scoped CategoryTheory

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## Graded terms -/

/-- The `n`-th exterior-power term attached to a `B`-module `M`. -/
abbrev Forms (M : Type u) [AddCommGroup M] [Module B M] (n : ℕ) : Type u :=
  ⋀[B]^n M

/-- The term `⋀[B]^n M`, regarded as an object of `ModuleCat A`. -/
noncomputable def formsOverBase (M : Type u) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (Forms (B := B) M n)

@[simp]
theorem formsOverBase_obj (M : Type u) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] (n : ℕ) :
    formsOverBase (A := A) (B := B) M n =
      ModuleCat.of A (⋀[B]^n M) :=
  rfl

/-! ## The degree-zero and degree-one identifications -/

/-- The `A`-linear identification `⋀[B]^0 M ≃ B`. -/
noncomputable def zeroFormsEquiv (M : Type u) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] :
    Forms (B := B) M 0 ≃ₗ[A] B :=
  (exteriorPower.zeroEquiv B M).restrictScalars A

@[simp]
theorem zeroFormsEquiv_apply_ιMulti (M : Type u) [AddCommGroup M]
    [Module A M] [Module B M] [IsScalarTower A B M] (f : Fin 0 → M) :
    zeroFormsEquiv (A := A) (B := B) M (exteriorPower.ιMulti B 0 f) = 1 :=
  exteriorPower.zeroEquiv_ιMulti f

/-- The `A`-linear identification `⋀[B]^1 M ≃ M`. -/
noncomputable def oneFormsEquiv (M : Type u) [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] :
    Forms (B := B) M 1 ≃ₗ[A] M :=
  (exteriorPower.oneEquiv B M).restrictScalars A

@[simp]
theorem oneFormsEquiv_apply_ιMulti (M : Type u) [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] (f : Fin 1 → M) :
    oneFormsEquiv (A := A) (B := B) M (exteriorPower.ιMulti B 1 f) = f 0 :=
  exteriorPower.oneEquiv_ιMulti f

/-! ## Derivations and the degree-zero differential -/

/-- The `A`-linear map underlying an `A`-derivation. -/
abbrev derivationLinearMap (M : Type u) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] (der : Derivation A B M) : B →ₗ[A] M :=
  der.toLinearMap

/-- The `A`-linear map `B → ⋀[B]^1 M` induced by an `A`-derivation
`der : B → M`. -/
noncomputable def derivationToDegreeOne (M : Type u) [AddCommGroup M]
    [Module A M] [Module B M] [IsScalarTower A B M]
    (der : Derivation A B M) :
    ModuleCat.of A B ⟶ formsOverBase (A := A) (B := B) M 1 :=
  ModuleCat.ofHom <|
    (exteriorPower.oneEquiv B M).symm.toLinearMap.restrictScalars A ∘ₗ
      der.toLinearMap

/-- After the one-form identification, `derivationToDegreeOne` recovers the
original derivation. -/
@[simp]
theorem oneFormsEquiv_comp_derivationToDegreeOne (M : Type u)
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (der : Derivation A B M) :
    (oneFormsEquiv (A := A) (B := B) M).toLinearMap ∘ₗ
        (derivationToDegreeOne (A := A) (B := B) M der).hom =
      der.toLinearMap := by
  ext b
  simp [derivationToDegreeOne, oneFormsEquiv]

/-- The universal derivation `d : B → Ω[B⁄A]`. -/
noncomputable def ordinaryDerivation : Derivation A B Ω[B⁄A] :=
  KaehlerDifferential.D A B

/-- The degree-zero de Rham differential `B → ⋀[B]^1 Ω[B⁄A]`. -/
noncomputable def ordinaryDerivationToDegreeOne :
    ModuleCat.of A B ⟶
      formsOverBase (A := A) (B := B) Ω[B⁄A] 1 :=
  derivationToDegreeOne (A := A) (B := B) Ω[B⁄A]
    (ordinaryDerivation (A := A) (B := B))

/-- Under `⋀[B]^1 Ω[B⁄A] ≃ Ω[B⁄A]`, the degree-zero differential is the
universal derivation. -/
@[simp]
theorem ordinaryDerivationToDegreeOne_spec :
    (oneFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap ∘ₗ
        (ordinaryDerivationToDegreeOne (A := A) (B := B)).hom =
      (KaehlerDifferential.D A B).toLinearMap :=
  oneFormsEquiv_comp_derivationToDegreeOne
    (A := A) (B := B) Ω[B⁄A] (ordinaryDerivation (A := A) (B := B))

/-! ## The divided-power case -/

open DividedPowers

variable {J : Ideal B} (δ : DividedPowers J)

/-- The universal divided-power derivation `pdD δ`, regarded as a
`Derivation`. Its compatibility with the divided powers is
`pdD_isPDDerivation δ`. -/
noncomputable def pdDerivation :
    Derivation A B (PDKaehler (A := A) δ) :=
  (pdD_isPDDerivation δ).toDerivation
    δ (PDKaehler (A := A) δ) (pdD δ)

/-- The degree-zero PD de Rham differential `B → ⋀[B]^1 (PDKaehler δ)`. -/
noncomputable def pdDerivationToDegreeOne :
    ModuleCat.of A B ⟶
      formsOverBase (A := A) (B := B) (PDKaehler (A := A) δ) 1 :=
  derivationToDegreeOne (A := A) (B := B) (PDKaehler (A := A) δ)
    (pdDerivation δ)

/-- Under `⋀[B]^1 (PDKaehler δ) ≃ PDKaehler δ`, the degree-zero PD differential
is `pdD δ`. -/
@[simp]
theorem oneFormsEquiv_comp_pdDerivationToDegreeOne :
    (oneFormsEquiv (A := A) (B := B) (PDKaehler (A := A) δ)).toLinearMap ∘ₗ
        (pdDerivationToDegreeOne δ).hom =
      (pdD δ) :=
  oneFormsEquiv_comp_derivationToDegreeOne
    (A := A) (B := B) (PDKaehler (A := A) δ) (pdDerivation δ)

end AffineCrystalline.DeRham
