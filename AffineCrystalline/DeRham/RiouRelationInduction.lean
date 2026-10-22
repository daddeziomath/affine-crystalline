/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.PDStability
import AffineCrystalline.DeRham.RiouDegreeTwo
import AffineCrystalline.DeRham.HigherDifferential
import AffineCrystalline.Envelope.FreeConstruction.RelationGenerators

/-!
# Generator formulas and relation annihilation, degree by degree

This file contains two degree-wise reduction statements.

* If maps `dₙ` and `dₙ₊₁` both satisfy Riou's generator formula
  `b₀ db₁ ∧ ⋯ ∧ dbₙ ↦ db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ`, then `dₙ₊₁ ∘ dₙ` vanishes on every
  generator `b₀ db₁ ∧ ⋯ ∧ dbₙ` (`riou_generator_square_zero_step`): the image
  `db₀ ∧ ⋯ ∧ dbₙ` is the generator with leading coefficient `1`, which is sent
  to `d1 ∧ db₀ ∧ ⋯ ∧ dbₙ = 0`.
* To show that `pdTermMap δ (n + 1) ∘ d` vanishes on the kernel
  `pdRelationPower δ n` of the PD quotient map, it suffices to check it on a
  family spanning that kernel (`relation_annihilation_of_span`, for the family
  `pdRelationExteriorFamily δ n`). In degree one, the explicit differential
  `RiouDegreeOne.degreeOneDifferential` kills every member of this family
  (`degreeOne_relation_generator_annihilation`).

In all degrees, the kernel of the PD quotient map is spanned by the family
`pdRiouRelationFamily` of Riou generators containing one PD relation
(`quotientTermMap_ker_le_pdRiouSpan`), and the stability of the de Rham
differential is `pdQuotientRelationStable`.

## Main definitions

* `RiouGeneratorFormula n d`: the map `d` satisfies Riou's generator formula in
  degree `n`.

## Main results

* `riou_generator_square_zero_step`
* `relation_annihilation_of_span`
* `degreeOne_relation_generator_annihilation`,
  `degreeOne_relation_annihilation_of_span`

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.
-/

open scoped CategoryTheory
open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham.RiouRelationInduction

open AffineCrystalline.DeRham
open AffineCrystalline.DeRham.RiouPresentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-! ## Consecutive generator formulas -/

/-- The map `d : ⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]` satisfies Riou's
generator formula `b₀ dg₀ ∧ ⋯ ∧ dgₙ₋₁ ↦ db₀ ∧ dg₀ ∧ ⋯ ∧ dgₙ₋₁`. -/
def RiouGeneratorFormula (n : ℕ)
    (d : OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1)) : Prop :=
  ∀ (b₀ : B) (g : Fin n → B),
    d (sourceGenerator (A := A) (B := B) n b₀ g) =
      targetGenerator (A := A) (B := B) n b₀ g

/-- The target generator in degree `n` is the source generator in degree
`n + 1` with leading coefficient `1`. -/
theorem targetGenerator_eq_sourceGenerator_succ
    (n : ℕ) (b₀ : B) (g : Fin n → B) :
    targetGenerator (A := A) (B := B) n b₀ g =
      sourceGenerator (A := A) (B := B) (n + 1) 1
        (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g) := by
  simp only [targetGenerator, sourceGenerator, one_smul]

/-- A target generator with leading entry `1` vanishes, since `d1 = 0`. -/
theorem targetGenerator_succ_eq_zero
    (n : ℕ) (b₀ : B) (g : Fin n → B) :
    targetGenerator (A := A) (B := B) (n + 1) 1
        (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g) = 0 := by
  unfold targetGenerator
  let m : Fin (n + 2) → Ω[B⁄A] :=
    KaehlerDifferential.D A B ∘
      AffineCrystalline.DeRham.RiouPresentation.finInsert 1
        (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g)
  have hm :
      KaehlerDifferential.D A B ∘
          AffineCrystalline.DeRham.RiouPresentation.finInsert 1
            (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g) =
        Function.update m (0 : Fin (n + 2)) 0 := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [m, Derivation.map_one_eq_zero]
    · simp [m, hi]
  rw [hm]
  exact (exteriorPower.ιMulti B (n + 2)).toMultilinearMap.map_update_zero
    m (0 : Fin (n + 2))

/-- If `dₙ` and `d_next` satisfy Riou's generator formula in degrees `n` and
`n + 1`, then `d_next ∘ dₙ` vanishes on the generators `b₀ dg₀ ∧ ⋯ ∧ dgₙ₋₁`. -/
theorem riou_generator_square_zero_step
    (n : ℕ)
    (dₙ : OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (d_next : OrdinaryTerm (A := A) (B := B) (n + 1) →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 2))
    (hₙ : RiouGeneratorFormula (A := A) (B := B) n dₙ)
    (h_next : RiouGeneratorFormula (A := A) (B := B) (n + 1) d_next)
    (b₀ : B) (g : Fin n → B) :
    d_next (dₙ (sourceGenerator (A := A) (B := B) n b₀ g)) = 0 := by
  rw [hₙ b₀ g]
  rw [targetGenerator_eq_sourceGenerator_succ]
  rw [h_next 1
    (AffineCrystalline.DeRham.RiouPresentation.finInsert b₀ g)]
  exact targetGenerator_succ_eq_zero (A := A) (B := B) n b₀ g

/-! ## Relation annihilation from a spanning family -/

/-- If `pdRelationPower δ n` lies in the `A`-span of
`pdRelationExteriorFamily δ n` and `pdTermMap δ (n + 1) ∘ d` kills this family,
then it kills `pdRelationPower δ n`. -/
theorem relation_annihilation_of_span
    (n : ℕ)
    (d : OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (hspan :
      pdRelationPower (A := A) (B := B) δ n ≤
        Submodule.span A (pdRelationExteriorFamily (A := A) (B := B) δ n))
    (hkill : ∀ (ω : OrdinaryTerm (A := A) (B := B) n),
      ω ∈ pdRelationExteriorFamily (A := A) (B := B) δ n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d) ω = 0) :
    ∀ (ω : OrdinaryTerm (A := A) (B := B) n),
      ω ∈ pdRelationPower (A := A) (B := B) δ n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d) ω = 0 := by
  intro ω hω
  have hfamily :
      Submodule.span A (pdRelationExteriorFamily (A := A) (B := B) δ n) ≤
        LinearMap.ker
          (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d) := by
    apply Submodule.span_le.2
    intro η hη
    exact hkill η hη
  exact hfamily (hspan hω)

/-! ## Degree one -/

/-- The degree-one differential sends each defining PD relation into the kernel
of `pdTermMap δ 2`. -/
theorem degreeOne_relation_generator_annihilation
    (r : ℕ) (hr : 1 ≤ r) (x : B) (hx : x ∈ J) :
    (pdTermMap (A := A) (B := B) δ 2 ∘ₗ
      (AffineCrystalline.DeRham.RiouDegreeOne.degreeOneDifferential
        (A := A) (B := B)))
      (exteriorPower.ιMulti B 1
        (fun _ : Fin 1 ↦ pdRelationGenerator δ r x)) = 0 := by
  change pdTermMap (A := A) (B := B) δ 2
      (AffineCrystalline.DeRham.RiouDegreeOne.degreeOneDifferential
        (A := A) (B := B)
        ((oneFormsEquiv (A := A) (B := B) Ω[B⁄A]).symm
          (pdRelationGenerator δ r x))) = 0
  exact pdRelationGenerator_degreeOne_map_eq_zero δ r hr x hx

/-- If `pdRelationPower δ 1` lies in the `A`-span of
`pdRelationExteriorFamily δ 1`, then the degree-one differential maps it into
the kernel of `pdTermMap δ 2`. -/
theorem degreeOne_relation_annihilation_of_span
    (hspan :
      pdRelationPower (A := A) (B := B) δ 1 ≤
        Submodule.span A
          (pdRelationExteriorFamily (A := A) (B := B) δ 1)) :
    ∀ (ω : OrdinaryTerm (A := A) (B := B) 1),
      ω ∈ pdRelationPower (A := A) (B := B) δ 1 →
        (pdTermMap (A := A) (B := B) δ 2 ∘ₗ
          (AffineCrystalline.DeRham.RiouDegreeOne.degreeOneDifferential
            (A := A) (B := B))) ω = 0 := by
  apply relation_annihilation_of_span δ 1
    (AffineCrystalline.DeRham.RiouDegreeOne.degreeOneDifferential
      (A := A) (B := B)) hspan
  intro ω hω
  rcases hω with ⟨i, m, r, hr, x, hx, rfl⟩
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  have hm :
      Function.update m (0 : Fin 1) (pdRelationGenerator δ r x) =
        (fun _ : Fin 1 ↦ pdRelationGenerator δ r x) := by
    funext j
    fin_cases j; rfl
  rw [hm]
  exact degreeOne_relation_generator_annihilation δ r hr x hx

/-- The statement of `relation_annihilation_of_span` for a map `d` satisfying
Riou's generator formula in degree `n`. -/
theorem higher_relation_annihilation_step
    (n : ℕ)
    (d : OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (_hformula : RiouGeneratorFormula (A := A) (B := B) n d)
    (hspan :
      pdRelationPower (A := A) (B := B) δ n ≤
        Submodule.span A (pdRelationExteriorFamily (A := A) (B := B) δ n))
    (hkill : ∀ (ω : OrdinaryTerm (A := A) (B := B) n),
      ω ∈ pdRelationExteriorFamily (A := A) (B := B) δ n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d) ω = 0) :
    ∀ (ω : OrdinaryTerm (A := A) (B := B) n),
      ω ∈ pdRelationPower (A := A) (B := B) δ n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d) ω = 0 :=
  relation_annihilation_of_span δ n d hspan hkill

end AffineCrystalline.DeRham.RiouRelationInduction
