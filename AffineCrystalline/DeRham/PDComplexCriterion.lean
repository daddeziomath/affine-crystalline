/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.PDDescent
import AffineCrystalline.DeRham.RiouComplex
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# A criterion for descending complexes to the PD de Rham terms

Let `δ` be a divided-power structure on an ideal `J ⊆ B`. This file packages a
criterion for descending a complex built on the ordinary terms
`⋀[B]^n Ω[B⁄A]` to the divided-power terms `⋀[B]^n (PDKaehler δ)`: an ordinary
complex in the sense of `ComplexData`, whose differentials satisfy the
stability condition `PDRelationStable δ`. From such data we build a cochain
complex of `A`-modules on the PD terms, and show that the quotient maps
commute with the differentials.

For the de Rham differential `DeRhamComplex.d`, the condition
`PDRelationStable δ` amounts to `QuotientRelationStable (pdRelations δ)`, which
is proved in all degrees as `pdQuotientRelationStable`; the PD de Rham complex
`pdDeRhamComplex` is obtained from it through `deRhamComplexOfQuotient`.

## Main definitions

* `pdTermOverBase δ n`: the PD de Rham term `⋀[B]^n (PDKaehler δ)` as an object
  of `ModuleCat A`.
* `pdTermMapHom δ n`: the quotient map `riouTerm n ⟶ pdTermOverBase δ n`.
* `PDComplexData δ`: an ordinary complex whose differentials satisfy
  `PDRelationStable δ`.
* `PDComplexData.pdDifferential`: the descended differential.
* `PDComplexData.complex`: the resulting cochain complex on the PD terms.

## Main results

* `PDComplexData.complex_d_square_zero`: consecutive differentials
  compose to zero.
* `PDComplexData.pdTermMapHom_naturality`: the quotient maps commute
  with the differentials.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open scoped CategoryTheory

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-- The `n`-th PD de Rham term as an object of `ModuleCat A`. -/
abbrev pdTermOverBase (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (PDTerm (A := A) (B := B) δ n)

/-- The quotient map `⋀[B]^n Ω[B⁄A] → ⋀[B]^n (PDKaehler δ)`, as a morphism in
`ModuleCat A`. -/
noncomputable def pdTermMapHom (n : ℕ) :
    riouTerm (A := A) (B := B) n ⟶ pdTermOverBase (A := A) (B := B) δ n :=
  ModuleCat.ofHom (pdTermMap (A := A) (B := B) δ n)

/-- Data for descending an ordinary complex to the PD de Rham terms: an
ordinary complex on the terms `⋀[B]^n Ω[B⁄A]` whose underlying `A`-linear
differentials satisfy `PDRelationStable δ`, the hypothesis of
`descendedDifferential`. -/
structure PDComplexData where
  /-- The ordinary complex on the terms `⋀[B]^n Ω[B⁄A]`. -/
  ordinary : ComplexData (A := A) (B := B)
  /-- Its differentials preserve the kernels of the PD quotient maps. -/
  pd_stable :
    PDRelationStable (A := A) (B := B) δ
      (fun n ↦ (ordinary.d n).hom)

namespace PDComplexData

/-- The descended differential, packaged as a morphism in `ModuleCat A`. -/
noncomputable def pdDifferential (c : PDComplexData (A := A) (B := B) δ)
    (n : ℕ) :
    pdTermOverBase (A := A) (B := B) δ n ⟶
      pdTermOverBase (A := A) (B := B) δ (n + 1) :=
  ModuleCat.ofHom <|
    descendedDifferential (A := A) (B := B) δ
      (fun n ↦ (c.ordinary.d n).hom) c.pd_stable n

private theorem ordinary_square_zero_hom
    (c : PDComplexData (A := A) (B := B) δ) (n : ℕ) :
    (c.ordinary.d (n + 1)).hom ∘ₗ (c.ordinary.d n).hom = 0 := by
  have h := congrArg ModuleCat.Hom.hom (c.ordinary.square_zero n)
  exact h

/-- The cochain complex of `A`-modules on the PD terms `⋀[B]^n (PDKaehler δ)`
with the descended differentials. -/
noncomputable def complex
    (c : PDComplexData (A := A) (B := B) δ) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun n ↦ pdTermOverBase (A := A) (B := B) δ n)
    (c.pdDifferential) (by
      intro n
      apply ModuleCat.hom_ext
      exact descendedDifferential_comp_self (A := A) (B := B) δ
        (fun n ↦ (c.ordinary.d n).hom) c.pd_stable
        (ordinary_square_zero_hom (A := A) (B := B) δ c) n)

/-- The terms of `c.complex` are the PD de Rham terms. -/
@[simp]
theorem complex_X
    (c : PDComplexData (A := A) (B := B) δ) (n : ℕ) :
    c.complex.X n = pdTermOverBase (A := A) (B := B) δ n :=
  rfl

/-- The differential of `c.complex` is the descended differential. -/
theorem complex_d
    (c : PDComplexData (A := A) (B := B) δ) (n : ℕ) :
    c.complex.d n (n + 1) =
      pdDifferential (A := A) (B := B) δ c n :=
  CochainComplex.of_d _ _ n

/-- Consecutive differentials of `c.complex` compose to zero. -/
theorem complex_d_square_zero
    (c : PDComplexData (A := A) (B := B) δ) (n : ℕ) :
    c.complex.d n (n + 1) ≫ c.complex.d (n + 1) (n + 2) = 0 :=
  HomologicalComplex.d_comp_d c.complex n (n + 1) (n + 2)

/-- The quotient maps commute with the differentials: `pdTermMapHom δ` is
compatible with the ordinary and the descended differentials in each
degree. -/
theorem pdTermMapHom_naturality
    (c : PDComplexData (A := A) (B := B) δ) (n : ℕ) :
    pdTermMapHom (A := A) (B := B) δ n ≫
        pdDifferential (A := A) (B := B) δ c n =
      c.ordinary.d n ≫ pdTermMapHom (A := A) (B := B) δ (n + 1) := by
  apply ModuleCat.hom_ext
  exact descendedDifferential_comp_pdTermMap (A := A) (B := B) δ
    (fun n ↦ (c.ordinary.d n).hom) c.pd_stable n

end PDComplexData

end AffineCrystalline.DeRham
