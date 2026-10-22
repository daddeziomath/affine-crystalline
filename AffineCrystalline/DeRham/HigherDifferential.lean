/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.PDComplexCriterion
import AffineCrystalline.DeRham.RiouPresentation
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Presentation data for the higher de Rham differentials and their PD descent

The term `⋀[B]^n Ω[B⁄A]` carries the tautological `A`-linear presentation
`aLinearExteriorPresentation n`, so that `A`-linear maps out of it correspond
to solutions of the presentation relations. The structure `DifferentialData δ`
packages a choice of such solutions in all degrees together with the
properties needed to obtain both an ordinary de Rham complex and its descent
to the divided-power terms `⋀[B]^n (PDKaehler δ)`:

* Riou's generator formula `b₀ db₁ ∧ ⋯ ∧ dbₙ ↦ db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ`;
* agreement with the universal derivation in degree zero;
* annihilation of the kernel of the PD quotient map in every degree;
* a PD differential compatible with the quotient maps;
* vanishing of consecutive composites.

From these data we derive the criteria `ComplexData` and
`PDComplexData`, and identify the given PD differential with the
descended one.

The PD de Rham complex `pdDeRhamComplex` itself is constructed directly from
the de Rham differential `DeRhamComplex.d` and `pdQuotientRelationStable`.

## Main definitions

* `ordinaryMap n s`: the `A`-linear map `⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]`
  determined by a presentation solution `s`.
* `DifferentialData δ`: the data described above.
* `ordinaryDifferentialData δ c`, `pdComplexData δ c`: the associated
  `ComplexData` and `PDComplexData`.

## Main results

* `pdRelationStable`: the maps `ordinaryMap n (c.relationSolution n)` are
  PD-stable.
* `generator_formula`: their values on Riou's generators.
* `pdDifferential_eq_descendedDifferential`, `pdComplexData_pdDifferential_eq`: the
  given PD differential is the descended differential.

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open scoped CategoryTheory

universe u

noncomputable section

namespace AffineCrystalline.DeRham.HigherDifferential

open AffineCrystalline.DeRham
open AffineCrystalline.DeRham.RiouPresentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-! ## Maps defined by presentation solutions -/

/-- The ordinary de Rham term `⋀[B]^n Ω[B⁄A]`. -/
abbrev OrdinaryTermAt (n : ℕ) : Type u :=
  AffineCrystalline.DeRham.OrdinaryTerm (A := A) (B := B) n

/-- The PD de Rham term `⋀[B]^n (PDKaehler δ)`. -/
abbrev PDTermAt (n : ℕ) : Type u :=
  AffineCrystalline.DeRham.PDTerm (A := A) (B := B) δ n

/-- Solutions in `⋀[B]^(n + 1) Ω[B⁄A]` of the relations of the tautological
`A`-linear presentation of `⋀[B]^n Ω[B⁄A]`. -/
abbrev PresentationSolution (n : ℕ) :=
  (aLinearExteriorPresentation (A := A) (B := B) n).toRelations.Solution
    (⋀[B]^(n + 1) Ω[B⁄A])

/-- The `A`-linear map determined by a presentation solution `s`. -/
noncomputable def ordinaryMap (n : ℕ) (s : PresentationSolution (A := A) (B := B) n) :
    OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1) :=
  (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc s

/-- The value of `ordinaryMap n s` on a presentation generator. -/
@[simp]
theorem ordinaryMap_var
    (n : ℕ) (s : PresentationSolution (A := A) (B := B) n)
    (x : (aLinearExteriorPresentation (A := A) (B := B) n).G) :
    ordinaryMap (A := A) (B := B) n s
        ((aLinearExteriorPresentation (A := A) (B := B) n).var x) =
      s.var x :=
  (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc_var s x

/-- Since the presentation is tautological, `ordinaryMap n s` agrees with
`s.var` on every element. -/
theorem ordinaryMap_apply
    (n : ℕ) (s : PresentationSolution (A := A) (B := B) n)
    (x : OrdinaryTermAt (A := A) (B := B) n) :
    ordinaryMap (A := A) (B := B) n s x = s.var x := by
  change (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc s
      ((aLinearExteriorPresentation (A := A) (B := B) n).var x) = s.var x
  exact (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc_var s x

/-! ## Presentation data in all degrees -/

/--
Presentation data for the de Rham differentials and their PD descent.

* `relationSolution` gives, in every degree, a solution of the presentation
  relations, hence a map `ordinaryMap n (relationSolution n)`;
* `generator_formula` is Riou's formula on the generators `b₀ db₁ ∧ ⋯ ∧ dbₙ`;
* `degree_zero` identifies the degree-zero map with `degreeZeroMap`;
* `relation_annihilation` states that each map sends the kernel of the PD
  quotient map in degree `n` into the kernel in degree `n + 1`;
* `pdDifferential` is a family of maps on the PD terms, compatible with the
  quotient maps by `differential_commutation`;
* `square_zero` states that consecutive maps compose to zero.
-/
structure DifferentialData where
  /-- In every degree, a solution of the presentation relations. -/
  relationSolution : ∀ n : ℕ, PresentationSolution (A := A) (B := B) n
  /-- Riou's formula on the generators `b₀ db₁ ∧ ⋯ ∧ dbₙ`. -/
  generator_formula :
    ∀ (n : ℕ) (b₀ : B) (g : Fin n → B),
      (relationSolution n).var
          (sourceGenerator (A := A) (B := B) n b₀ g) =
        targetGenerator (A := A) (B := B) n b₀ g
  /-- In degree zero, the map is `degreeZeroMap`. -/
  degree_zero :
    ordinaryMap (A := A) (B := B) 0 (relationSolution 0) =
      (degreeZeroMap (A := A) (B := B)).hom
  /-- The kernel of the PD quotient map is sent into the kernel in the next degree. -/
  relation_annihilation :
    ∀ (n : ℕ) (ω : OrdinaryTermAt (A := A) (B := B) n),
      ω ∈ pdRelationPower (A := A) (B := B) δ n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ
          ordinaryMap (A := A) (B := B) n (relationSolution n)) ω = 0
  /-- The differentials on the PD terms. -/
  pdDifferential :
    ∀ n : ℕ, PDTermAt (A := A) (B := B) δ n →ₗ[A]
      PDTermAt (A := A) (B := B) δ (n + 1)
  /-- The PD differentials are compatible with the quotient maps. -/
  differential_commutation :
    ∀ n : ℕ,
      pdDifferential n ∘ₗ pdTermMap (A := A) (B := B) δ n =
        pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ
          ordinaryMap (A := A) (B := B) n (relationSolution n)
  /-- Consecutive maps compose to zero. -/
  square_zero :
    ∀ n : ℕ,
      ordinaryMap (A := A) (B := B) (n + 1) (relationSolution (n + 1)) ∘ₗ
          ordinaryMap (A := A) (B := B) n (relationSolution n) = 0

/-! ## Consequences -/

/-- The maps defined by the data are PD-stable. -/
theorem pdRelationStable (c : DifferentialData (A := A) (B := B) δ) :
    PDRelationStable (A := A) (B := B) δ
      (fun n ↦ ordinaryMap (A := A) (B := B) n (c.relationSolution n)) := by
  intro n ω hω
  exact c.relation_annihilation n ω hω

/-- Riou's generator formula for the maps defined by the data. -/
theorem generator_formula (c : DifferentialData (A := A) (B := B) δ)
    (n : ℕ) (b₀ : B) (g : Fin n → B) :
    ordinaryMap (A := A) (B := B) n (c.relationSolution n)
        (sourceGenerator (A := A) (B := B) n b₀ g) =
      targetGenerator (A := A) (B := B) n b₀ g := by
  rw [← aLinearExteriorPresentation_var (A := A) (B := B) n
    (sourceGenerator (A := A) (B := B) n b₀ g)]
  rw [ordinaryMap_apply]
  exact c.generator_formula n b₀ g

/-- The ordinary complex defined by the data. -/
noncomputable def ordinaryDifferentialData (c : DifferentialData (A := A) (B := B) δ) :
    ComplexData (A := A) (B := B) where
  d n := ModuleCat.ofHom
    (ordinaryMap (A := A) (B := B) n (c.relationSolution n))
  degree_zero := by
    apply ModuleCat.hom_ext
    exact c.degree_zero
  square_zero n := by
    apply ModuleCat.hom_ext
    exact c.square_zero n

/-- The data for descending the ordinary complex to the PD terms. -/
noncomputable def pdComplexData (c : DifferentialData (A := A) (B := B) δ) :
    PDComplexData (A := A) (B := B) δ where
  ordinary := ordinaryDifferentialData (A := A) (B := B) δ c
  pd_stable := pdRelationStable (A := A) (B := B) δ c

/-- The differentials of `ordinaryDifferentialData δ c` are the maps
`ordinaryMap n (c.relationSolution n)`. -/
theorem ordinaryDifferentialData_d (c : DifferentialData (A := A) (B := B) δ) (n : ℕ) :
    ((ordinaryDifferentialData (A := A) (B := B) δ c).d n).hom =
      ordinaryMap (A := A) (B := B) n (c.relationSolution n) :=
  rfl

/-- The given PD differential is the descended differential. -/
theorem pdDifferential_eq_descendedDifferential
    (c : DifferentialData (A := A) (B := B) δ) (n : ℕ) :
    c.pdDifferential n =
      descendedDifferential (A := A) (B := B) δ
        (fun n ↦ ordinaryMap (A := A) (B := B) n (c.relationSolution n))
        (pdRelationStable (A := A) (B := B) δ c) n := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := pdTermMap_surjective (A := A) (B := B) δ n y
  have hgiven := congrArg (fun F ↦ F x) (c.differential_commutation n)
  have hcanonical := congrArg (fun F ↦ F x)
      (descendedDifferential_comp_pdTermMap (A := A) (B := B) δ
      (fun n ↦ ordinaryMap (A := A) (B := B) n (c.relationSolution n))
      (pdRelationStable (A := A) (B := B) δ c) n)
  simpa [LinearMap.comp_apply] using hgiven.trans hcanonical.symm

/-- The differential of the descended complex is the given PD differential. -/
theorem pdComplexData_pdDifferential_eq
    (c : DifferentialData (A := A) (B := B) δ) (n : ℕ) :
    (AffineCrystalline.DeRham.PDComplexData.pdDifferential
      (A := A) (B := B) δ
      (pdComplexData (A := A) (B := B) δ c) n).hom =
      c.pdDifferential n := by
  rw [AffineCrystalline.DeRham.PDComplexData.pdDifferential]
  exact (pdDifferential_eq_descendedDifferential (A := A) (B := B) δ c n).symm

end AffineCrystalline.DeRham.HigherDifferential
