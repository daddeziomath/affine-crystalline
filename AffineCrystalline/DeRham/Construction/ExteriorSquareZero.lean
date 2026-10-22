/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.Abstract
import AffineCrystalline.DeRham.PDRelations
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Exterior multiplication on PD differential forms

Let `⋀_B Ω_{B,δ}` be the exterior algebra of the module of divided power Kähler
differentials. For a one-form `ω ∈ Ω_{B,δ}`, left multiplication by `ω` is a
square-zero endomorphism of `⋀_B Ω_{B,δ}`, since `ω ∧ ω = 0`; it therefore defines
a complex in the sense of `AffineCrystalline.DeRham.Abstract`. Moreover, the image
in `Ω_{B,δ}` of a defining relation `d(x^[n]) - x^[n-1] dx` vanishes, hence so do
its exterior generator and the associated multiplication operator.

## Main definitions

* `PDExterior δ`: the exterior algebra `⋀_B Ω_{B,δ}`.
* `exteriorDifferential δ ω`: left multiplication by `ω` on `⋀_B Ω_{B,δ}`.
* `exteriorMultiplicationComplex δ ω`: the corresponding complex.

## Main results

* `exteriorDifferential_comp_self`: `(ω ∧ -) ∘ (ω ∧ -) = 0`.
* `pdRelationGenerator_exteriorDifferential_eq_zero`: multiplication by the class
  of a divided power relation is zero.
-/

open scoped CategoryTheory

universe u

namespace AffineCrystalline.DeRham.Construction

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-- The exterior algebra `⋀_B Ω_{B,δ}`. -/
abbrev PDExterior : Type u :=
  ExteriorAlgebra B (PDKaehler (A := A) δ)

/-- The image of `ω ∈ Ω_{B,δ}` in degree one of `⋀_B Ω_{B,δ}`. -/
noncomputable def exteriorGenerator (ω : PDKaehler (A := A) δ) :
    PDExterior (A := A) δ :=
  ExteriorAlgebra.ι B ω

/-- Left multiplication by `ω ∈ Ω_{B,δ}` on `⋀_B Ω_{B,δ}`, as a morphism of
`B`-modules. -/
noncomputable def exteriorDifferential (ω : PDKaehler (A := A) δ) :
    ModuleCat.of B (PDExterior (A := A) δ) ⟶ ModuleCat.of B (PDExterior (A := A) δ) :=
  ModuleCat.ofHom (LinearMap.mulLeft B (exteriorGenerator δ ω))

/-- Left multiplication by a one-form is square-zero, since `ω ∧ ω = 0`. -/
theorem exteriorDifferential_comp_self (ω : PDKaehler (A := A) δ) :
    exteriorDifferential δ ω ≫ exteriorDifferential δ ω = 0 := by
  simp only [exteriorDifferential]
  rw [← ModuleCat.ofHom_comp, ← LinearMap.mulLeft_mul]
  rw [exteriorGenerator, ExteriorAlgebra.ι_sq_zero]
  rw [LinearMap.mulLeft_zero_eq_zero]
  rfl

/-- The complex `⋀_B Ω_{B,δ} → ⋀_B Ω_{B,δ} → ⋯` whose differentials are all left
multiplication by `ω`. -/
noncomputable def exteriorMultiplicationComplex (ω : PDKaehler (A := A) δ) :
    Abstract B where
  X _ := ModuleCat.of B (PDExterior (A := A) δ)
  d _ := exteriorDifferential δ ω
  d_comp_d _ := exteriorDifferential_comp_self δ ω

@[simp]
theorem exteriorMultiplicationComplex_X (ω : PDKaehler (A := A) δ) (n : ℕ) :
    (exteriorMultiplicationComplex δ ω).X n =
      ModuleCat.of B (PDExterior (A := A) δ) :=
  rfl

@[simp]
theorem exteriorMultiplicationComplex_d (ω : PDKaehler (A := A) δ) (n : ℕ) :
    (exteriorMultiplicationComplex δ ω).d n = exteriorDifferential δ ω :=
  rfl

@[simp]
theorem exteriorMultiplicationComplex_d_square_zero
    (ω : PDKaehler (A := A) δ) (n : ℕ) :
    (exteriorMultiplicationComplex δ ω).d n ≫
        (exteriorMultiplicationComplex δ ω).d (n + 1) = 0 :=
  exteriorDifferential_comp_self δ ω

/-- The image in `⋀_B Ω_{B,δ}` of a relation `d(x^[n]) - x^[n-1] dx` is zero. -/
theorem pdRelationGenerator_exteriorGenerator_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (x : B) (hx : x ∈ J) :
    exteriorGenerator δ
        ((pdRelations (A := A) δ).mkQ (pdRelationGenerator δ n x)) = 0 := by
  rw [mkQ_pdRelationGenerator_eq_zero δ n hn x hx]
  exact map_zero _

/-- Left multiplication by the image of a relation `d(x^[n]) - x^[n-1] dx` is the
zero morphism. -/
theorem pdRelationGenerator_exteriorDifferential_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (x : B) (hx : x ∈ J) :
    exteriorDifferential δ
        ((pdRelations (A := A) δ).mkQ (pdRelationGenerator δ n x)) = 0 := by
  rw [exteriorDifferential,
    pdRelationGenerator_exteriorGenerator_eq_zero δ n hn x hx,
    LinearMap.mulLeft_zero_eq_zero]
  rfl

end AffineCrystalline.DeRham.Construction
