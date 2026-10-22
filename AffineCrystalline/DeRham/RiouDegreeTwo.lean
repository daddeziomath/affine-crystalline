/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.RiouDegreeOne
import AffineCrystalline.DeRham.RiouPresentation
import AffineCrystalline.DeRham.PDDescent
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Riou's generator formula in degree two

In degree two, Riou's generator formula reads
`b₀ db₁ ∧ db₂ ↦ db₀ ∧ db₁ ∧ db₂`. We write it in terms of the triple wedge
`wedge3` and verify, on generators, its compatibility with `d ∘ d = 0`: the
degree-one value `db₀ ∧ db₁` is the generator `1 · db₀ ∧ db₁`, which the
degree-two formula sends to `d1 ∧ db₀ ∧ db₁ = 0`.

The corresponding statement in all degrees is
`RiouRelationInduction.riou_generator_square_zero_step`, and the de Rham
differential in all degrees is `DeRhamComplex.d`.

## Main definitions

* `wedge3 x y z`: the element `x ∧ y ∧ z` of `⋀[B]^3 Ω[B⁄A]`.
* `DegreeTwoGeneratorFormula d`: the predicate that a map
  `⋀[B]^2 Ω[B⁄A] → ⋀[B]^3 Ω[B⁄A]` satisfies Riou's formula.

## Main results

* `targetGenerator_two`: the degree-two formula as a triple wedge.
* `degreeTwo_comp_degreeOne_on_generator`: a map satisfying the degree-two
  formula kills the image of the degree-one generators.
-/

open scoped CategoryTheory

universe u

noncomputable section

namespace AffineCrystalline.DeRham.RiouDegreeTwo

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The module of Kähler differentials `Ω[B⁄A]`. -/
abbrev Ω := Ω[B⁄A]
/-- The third exterior power `⋀[B]^3 Ω[B⁄A]`. -/
abbrev Λ3 := ⋀[B]^3 Ω[B⁄A]

/-! ## The degree-two target generator -/

/-- The triple wedge `x ∧ y ∧ z`. -/
def wedge3 (x y z : Ω (A := A) (B := B)) : Λ3 (A := A) (B := B) :=
  exteriorPower.ιMulti B 3 ![x, y, z]

@[simp]
theorem wedge3_zero_left (y z : Ω (A := A) (B := B)) :
    wedge3 (A := A) (B := B) 0 y z = 0 := by
  change exteriorPower.ιMulti B 3 ![(0 : Ω (A := A) (B := B)), y, z] = 0
  rw [show ![(0 : Ω (A := A) (B := B)), y, z] =
      Function.update ![(0 : Ω (A := A) (B := B)), y, z] 0 0 by
    funext i
    fin_cases i <;> rfl]
  exact (exteriorPower.ιMulti B 3).toMultilinearMap.map_update_zero
    ![(0 : Ω (A := A) (B := B)), y, z] (0 : Fin 3)

/-- The degree-two target generator is `db₀ ∧ dg₀ ∧ dg₁`. -/
theorem targetGenerator_two (b₀ : B) (g : Fin 2 → B) :
    AffineCrystalline.DeRham.RiouPresentation.targetGenerator
        (A := A) (B := B) 2 b₀ g =
      wedge3 (A := A) (B := B)
        (KaehlerDifferential.D A B b₀)
        (KaehlerDifferential.D A B (g 0))
        (KaehlerDifferential.D A B (g 1)) := by
  change exteriorPower.ιMulti B 3
      (KaehlerDifferential.D A B ∘
        AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g) = _
  unfold wedge3
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## The generator-level square-zero calculation -/

/-- The degree-one target generator is the degree-two source generator with
leading coefficient `1`. -/
theorem targetGenerator_one_eq_sourceGenerator_two
    (b₀ : B) (g : Fin 1 → B) :
    AffineCrystalline.DeRham.RiouPresentation.targetGenerator
        (A := A) (B := B) 1 b₀ g =
      AffineCrystalline.DeRham.RiouPresentation.sourceGenerator
        (A := A) (B := B) 2 1
          (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g) := by
  simp only [AffineCrystalline.DeRham.RiouPresentation.targetGenerator,
    AffineCrystalline.DeRham.RiouPresentation.sourceGenerator, one_smul]

/-- Applying the degree-two formula to the degree-one value `db₀ ∧ dg₀`,
viewed as the generator with leading coefficient `1`, gives
`d1 ∧ db₀ ∧ dg₀ = 0`. This is `d ∘ d = 0` on generators. -/
theorem targetGenerator_two_after_targetGenerator_one
    (b₀ : B) (g : Fin 1 → B) :
    AffineCrystalline.DeRham.RiouPresentation.targetGenerator
        (A := A) (B := B) 2 1
          (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g) = 0 := by
  rw [targetGenerator_two]
  simp [AffineCrystalline.DeRham.RiouPresentation.finInsert, Derivation.map_one_eq_zero]

/-! ## Maps satisfying the degree-two formula -/

/-- The map `d : ⋀[B]^2 Ω[B⁄A] → ⋀[B]^3 Ω[B⁄A]` satisfies Riou's generator
formula `b₀ dg₀ ∧ dg₁ ↦ db₀ ∧ dg₀ ∧ dg₁`. -/
def DegreeTwoGeneratorFormula
    (d : (⋀[B]^2 Ω[B⁄A]) →ₗ[A] (⋀[B]^3 Ω[B⁄A])) : Prop :=
  ∀ (b₀ : B) (g : Fin 2 → B),
    d (AffineCrystalline.DeRham.RiouPresentation.sourceGenerator
        (A := A) (B := B) 2 b₀ g) =
      AffineCrystalline.DeRham.RiouPresentation.targetGenerator
        (A := A) (B := B) 2 b₀ g

/-- A map satisfying the degree-two generator formula vanishes on the
degree-one target generators `db₀ ∧ dg₀`. -/
theorem degreeTwo_comp_degreeOne_on_generator
    (d : (⋀[B]^2 Ω[B⁄A]) →ₗ[A] (⋀[B]^3 Ω[B⁄A]))
    (hd : DegreeTwoGeneratorFormula (A := A) (B := B) d)
    (b₀ : B) (g : Fin 1 → B) :
    d (AffineCrystalline.DeRham.RiouPresentation.targetGenerator
        (A := A) (B := B) 1 b₀ g) = 0 := by
  rw [targetGenerator_one_eq_sourceGenerator_two]
  rw [hd]
  exact targetGenerator_two_after_targetGenerator_one
    (A := A) (B := B) b₀ g

end AffineCrystalline.DeRham.RiouDegreeTwo
