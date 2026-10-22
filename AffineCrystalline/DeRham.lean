/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.MvPolynomial.Basic
import AffineCrystalline.DeRham.RiouBasic
import AffineCrystalline.DeRham.RiouDegreeOne
import AffineCrystalline.DeRham.PDStability
import AffineCrystalline.DeRham.RiouFull
import AffineCrystalline.DeRham.QuotientComplex
import AffineCrystalline.DeRham.PDStabilityFull

/-!
# The divided power de Rham complex

Let `A → B` be a ring map and `δ` a divided power structure on an ideal `J ⊆ B`.
We construct the divided power de Rham complex
`Ω^•_{B,δ} : Ω^0_{B,δ} → Ω^1_{B,δ} → Ω^2_{B,δ} → ⋯`, where
`Ω^i_{B,δ} = ⋀^i_B Ω_{B,δ}`, as a cochain complex of `A`-modules.

The ordinary de Rham differential on `⋀^•_B Ω[B⁄A]` is constructed from a
presentation, following J. Riou's construction of the de Rham complex via
presentations. A general criterion (`deRhamComplexOfQuotient`) shows that it
descends to `⋀^•_B (Ω[B⁄A] / N)` whenever the exterior relations coming from the
submodule `N` are stable under the differential. For `N = pdRelations δ` this
stability holds in every degree (`pdQuotientRelationStable`); in degree one it
reduces to the identity `d(x^[n-1]) ∧ dx = x^[n-2] dx ∧ dx = 0`.

## Main definitions

* `pdDeRhamComplex δ`: the divided power de Rham complex `Ω^•_{B,δ}`, as an object
  of `CochainComplex (ModuleCat A) ℕ`.

## Main results

* `pdRelations_wedge_zero`: the de Rham differential of a generator
  `d(x^[n]) - x^[n-1] dx` of `pdRelations δ` vanishes in `Ω^2_{B,δ}`.

## References

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open scoped TensorProduct
open scoped Simplicial
open scoped CategoryTheory
open DividedPowers
open AffineCrystalline.DeRham

universe u

section DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The degree-one de Rham differential of a generator `d(x^[n]) - x^[n-1] dx` of
`pdRelations δ` maps to zero in `Ω^2_{B,δ}`. -/
theorem pdRelations_wedge_zero {J : Ideal B} (δ : DividedPowers J) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (x : B), x ∈ J →
      pdTermMap (A := A) (B := B) δ 2
        (AffineCrystalline.DeRham.RiouDegreeOne.degreeOneDifferential
          (A := A) (B := B)
          ((oneFormsEquiv (A := A) (B := B) Ω[B⁄A]).symm
            (pdRelationGenerator δ n x))) = 0 := by
  intro n hn x hx
  exact pdRelationGenerator_degreeOne_map_eq_zero δ n hn x hx

/-- The divided power de Rham complex `Ω^•_{B,δ}`, as a cochain complex of
`A`-modules, with `Ω^i_{B,δ} = ⋀^i_B Ω_{B,δ}`. The ordinary de Rham differential
descends to it by `pdQuotientRelationStable`. -/
noncomputable def pdDeRhamComplex {J : Ideal B} (δ : DividedPowers J) :
    CochainComplex (ModuleCat A) ℕ :=
  deRhamComplexOfQuotient (A := A) (B := B)
    (pdRelations (A := A) δ) (pdQuotientRelationStable δ)

end DeRham
