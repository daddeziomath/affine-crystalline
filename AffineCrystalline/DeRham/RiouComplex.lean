/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.RiouBasic
import AffineCrystalline.DeRham.RiouPresentation
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The ordinary de Rham terms and complexes from explicit differentials

The `n`-th term of the algebraic de Rham complex of `B` over `A` is the
exterior power `⋀[B]^n Ω[B⁄A]`, formed over `B` and regarded as an `A`-module
(`riouTerm n`). This file provides:

* the degree-zero differential `degreeZeroMap`, which is the universal
  derivation `d : B → Ω[B⁄A]` composed with the canonical identifications
  `⋀[B]^0 Ω[B⁄A] ≃ B` and `⋀[B]^1 Ω[B⁄A] ≃ Ω[B⁄A]`;
* the tautological `A`-linear presentation `aLinearExteriorPresentation n` of
  `⋀[B]^n Ω[B⁄A]`, through which `A`-linear maps out of the `n`-th term
  correspond to solutions of its relations (`higherMap`);
* the criterion `ComplexData`: a family of `A`-linear maps between
  consecutive terms, equal to `degreeZeroMap` in degree zero and with vanishing
  consecutive composites, together with the cochain complex it defines.
  `PresentationComplexData` provides the same data in terms of
  presentation solutions in positive degrees.

The de Rham differential in all degrees is `DeRhamComplex.d`, with associated
complex `deRhamComplex`.

## Main definitions

* `riouTerm n`: the term `⋀[B]^n Ω[B⁄A]` as an object of `ModuleCat A`.
* `degreeZeroMap`: the differential `riouTerm 0 ⟶ riouTerm 1`.
* `aLinearExteriorPresentation n`: the tautological `A`-linear presentation of
  `⋀[B]^n Ω[B⁄A]`.
* `higherMap n c`: the map `riouTerm n ⟶ riouTerm (n + 1)` determined by a
  presentation solution.
* `ComplexData`, `PresentationComplexData`: data of a complex on
  the terms `riouTerm n`.
* `ComplexData.toCochainComplex`, `ordinaryComplex`: the associated
  cochain complex of `A`-modules.

## Main results

* `degreeZeroMap_spec`: `degreeZeroMap` is the universal derivation.
* `ComplexData.toCochainComplex_degree_zero`,
  `ordinaryComplex_d_square_zero`.

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
-/

open scoped CategoryTheory

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## The graded terms -/

/-- The `n`-th ordinary de Rham term, formed over `B` and viewed over `A`. -/
abbrev riouTerm (n : ℕ) : ModuleCat.{u} A :=
  formsOverBase (A := A) (B := B) Ω[B⁄A] n

/-! ## The degree-zero differential -/

/-- The degree-zero differential `⋀[B]^0 Ω[B⁄A] → ⋀[B]^1 Ω[B⁄A]`, obtained from
the universal derivation via the identification `⋀[B]^0 Ω[B⁄A] ≃ B`. -/
noncomputable def degreeZeroMap : riouTerm (A := A) (B := B) 0 ⟶
    riouTerm (A := A) (B := B) 1 :=
  ModuleCat.ofHom <|
    RiouPresentation.degreeZeroDifferential (A := A) (B := B) ∘ₗ
      (zeroFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap

@[simp]
theorem degreeZeroMap_hom :
    (degreeZeroMap (A := A) (B := B)).hom =
      RiouPresentation.degreeZeroDifferential (A := A) (B := B) ∘ₗ
        (zeroFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap :=
  rfl

/-- Under the identifications of zero-forms with `B` and of one-forms with
`Ω[B⁄A]`, the map `degreeZeroMap` is the universal derivation. -/
theorem degreeZeroMap_spec :
    (oneFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap ∘ₗ
        (degreeZeroMap (A := A) (B := B)).hom =
      (KaehlerDifferential.D A B).toLinearMap ∘ₗ
        (zeroFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap := by
  ext x
  change (oneFormsEquiv (A := A) (B := B) Ω[B⁄A])
      ((ordinaryDerivationToDegreeOne (A := A) (B := B)).hom
        ((zeroFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap x)) =
    KaehlerDifferential.D A B
      ((zeroFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap x)
  exact congrArg
    (fun f ↦ f ((zeroFormsEquiv (A := A) (B := B) Ω[B⁄A]).toLinearMap x))
    (ordinaryDerivationToDegreeOne_spec (A := A) (B := B))

/-! ## Presentations of the terms -/

/-- The tautological presentation of `⋀[B]^n Ω[B⁄A]` as an `A`-module.

The exterior power is formed over `B`, while the presentation is over `A`, so
that the maps defined through it are `A`-linear. -/
noncomputable def aLinearExteriorPresentation (n : ℕ) :
    Module.Presentation A (⋀[B]^n Ω[B⁄A]) :=
  Module.Presentation.tautological A (⋀[B]^n Ω[B⁄A])

@[simp]
theorem aLinearExteriorPresentation_var (n : ℕ)
    (x : ⋀[B]^n Ω[B⁄A]) :
    (aLinearExteriorPresentation (A := A) (B := B) n).var x = x := by
  rfl

/-- A solution in `⋀[B]^(n + 1) Ω[B⁄A]` of the relations of
`aLinearExteriorPresentation n`; it determines an `A`-linear map from the
`n`-th to the `(n + 1)`-st term (`higherMap`). -/
structure HigherPresentationData (n : ℕ) where
  relationSolution :
    (aLinearExteriorPresentation (A := A) (B := B) n).toRelations.Solution
      (⋀[B]^(n + 1) Ω[B⁄A])

/-- The `A`-linear map `riouTerm n ⟶ riouTerm (n + 1)` determined by a
presentation solution. -/
noncomputable def higherMap (n : ℕ)
    (c : HigherPresentationData (A := A) (B := B) n) :
    riouTerm (A := A) (B := B) n ⟶ riouTerm (A := A) (B := B) (n + 1) :=
  ModuleCat.ofHom <|
    (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc
      c.relationSolution

@[simp]
theorem higherMap_hom (n : ℕ) (c : HigherPresentationData (A := A) (B := B) n) :
    (higherMap n c).hom =
      (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc
        c.relationSolution :=
  rfl

/-- The value of `higherMap n c` on a presentation generator. -/
theorem higherMap_var (n : ℕ)
    (c : HigherPresentationData (A := A) (B := B) n)
    (x : (aLinearExteriorPresentation (A := A) (B := B) n).G) :
    (higherMap n c).hom
        ((aLinearExteriorPresentation (A := A) (B := B) n).var x) =
      c.relationSolution.var x :=
  (aLinearExteriorPresentation (A := A) (B := B) n).toIsPresentation.desc_var
    c.relationSolution x

/-! ## Complexes from explicit differentials -/

/--
Data of a complex on the ordinary de Rham terms: a family `d` of `A`-linear
maps `riouTerm n ⟶ riouTerm (n + 1)` such that `d 0` is the degree-zero
differential `degreeZeroMap` and consecutive maps compose to zero.
-/
structure ComplexData where
  d : ∀ n : ℕ, riouTerm (A := A) (B := B) n ⟶
    riouTerm (A := A) (B := B) (n + 1)
  degree_zero : d 0 = degreeZeroMap (A := A) (B := B)
  square_zero : ∀ n : ℕ, d n ≫ d (n + 1) = 0

/-- Data of a complex on the ordinary de Rham terms in which the differentials
in positive degrees are given by presentation solutions, and the degree-zero
differential is `degreeZeroMap`. The fields `square_zero` and
`higher_square_zero` state that consecutive differentials compose to zero. -/
structure PresentationComplexData where
  higher : ∀ n : ℕ, HigherPresentationData (A := A) (B := B) (n + 1)
  square_zero :
    degreeZeroMap (A := A) (B := B) ≫ higherMap 1 (higher 0) = 0
  higher_square_zero : ∀ n : ℕ,
    higherMap (n + 1) (higher n) ≫ higherMap (n + 2) (higher (n + 1)) = 0

/-- The `ComplexData` defined by a `PresentationComplexData`. -/
noncomputable def PresentationComplexData.toComplexData
    (c : PresentationComplexData (A := A) (B := B)) :
    ComplexData (A := A) (B := B) where
  d n :=
    match n with
    | 0 => degreeZeroMap (A := A) (B := B)
    | n + 1 => higherMap (n + 1) (c.higher n)
  degree_zero := rfl
  square_zero n := by
    cases n with
    | zero => exact c.square_zero
    | succ n => exact c.higher_square_zero n

/-! ## The associated cochain complex -/

/-- The cochain complex of `A`-modules defined by a `ComplexData`. -/
noncomputable def ComplexData.toCochainComplex
    (c : ComplexData (A := A) (B := B)) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun n ↦ riouTerm (A := A) (B := B) n) c.d c.square_zero

@[simp]
theorem ComplexData.toCochainComplex_X
    (c : ComplexData (A := A) (B := B)) (n : ℕ) :
    c.toCochainComplex.X n = riouTerm (A := A) (B := B) n :=
  rfl

@[simp]
theorem ComplexData.toCochainComplex_d
    (c : ComplexData (A := A) (B := B)) (n : ℕ) :
    c.toCochainComplex.d n (n + 1) = c.d n :=
  CochainComplex.of_d _ _ n

/-- The first differential of `c.toCochainComplex` is `degreeZeroMap`. -/
theorem ComplexData.toCochainComplex_degree_zero
    (c : ComplexData (A := A) (B := B)) :
    c.toCochainComplex.d 0 1 = degreeZeroMap (A := A) (B := B) := by
  rw [c.toCochainComplex_d, c.degree_zero]

/-- The cochain complex of `A`-modules defined by `c : ComplexData`. -/
noncomputable def ordinaryComplex (c : ComplexData (A := A) (B := B)) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  c.toCochainComplex

/-- Consecutive differentials of `ordinaryComplex c` compose to zero. -/
theorem ordinaryComplex_d_square_zero (c : ComplexData (A := A) (B := B))
    (n : ℕ) :
    (ordinaryComplex c).d n (n + 1) ≫ (ordinaryComplex c).d (n + 1) (n + 2) = 0 := by
  change c.toCochainComplex.d n (n + 1) ≫ c.toCochainComplex.d (n + 1) (n + 2) = 0
  rw [c.toCochainComplex_d, c.toCochainComplex_d]
  exact c.square_zero n

end AffineCrystalline.DeRham
