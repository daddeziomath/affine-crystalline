/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.RiouFull
import AffineCrystalline.DeRham.PDDescent
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# De Rham complexes of stable quotients

Let `N ⊆ Ω[B⁄A]` be a `B`-submodule. The quotient map `Ω[B⁄A] → Ω[B⁄A] ⧸ N`
induces surjective `A`-linear maps
`⋀[B]^n Ω[B⁄A] → ⋀[B]^n (Ω[B⁄A] ⧸ N)` in every degree. If the de Rham
differential `DeRhamComplex.d` maps the kernel of each of these maps into the
kernel of the next one, it descends to a differential on the quotient terms,
which again squares to zero; this produces a de Rham complex attached to the
quotient `Ω[B⁄A] ⧸ N`. The construction does not depend on the nature of `N`.

For the divided-power relations `N = pdRelations δ`, the stability condition
is `pdQuotientRelationStable`, and the resulting complex is the PD de Rham
complex `pdDeRhamComplex` (Stacks Project, Tag 07HZ).

## Main definitions

* `QuotientTerm N n`: the module `⋀[B]^n (Ω[B⁄A] ⧸ N)`.
* `quotientTermMap N n`: the `A`-linear map `⋀[B]^n Ω[B⁄A] → QuotientTerm N n`.
* `QuotientRelationStable N`: in every degree, the de Rham differential maps
  `ker (quotientTermMap N n)` into `ker (quotientTermMap N (n + 1))`.
* `quotientDifferential N hstable n`: the descended differential.
* `deRhamComplexOfQuotient N hstable`: the resulting cochain complex of
  `A`-modules.

## Main results

* `quotientTermMap_surjective`: the quotient maps are surjective.
* `quotientDifferential_comp_self`: the descended differential squares to zero.

## References

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The degree-`n` exterior power of a quotient of Kähler differentials. -/
abbrev QuotientTerm (N : Submodule B (Ω[B⁄A])) (n : ℕ) : Type u :=
  ⋀[B]^n (Ω[B⁄A] ⧸ N)

/-- The exterior-power map induced by the quotient `Ω[B⁄A] ⟶ Ω[B⁄A] ⧸ N`. -/
noncomputable def quotientTermMap (N : Submodule B (Ω[B⁄A])) (n : ℕ) :
    (⋀[B]^n Ω[B⁄A]) →ₗ[A] QuotientTerm N n :=
  (exteriorPower.map n N.mkQ).restrictScalars A

/-- The map `quotientTermMap N n` is surjective. -/
theorem quotientTermMap_surjective (N : Submodule B (Ω[B⁄A])) (n : ℕ) :
    Function.Surjective (quotientTermMap (A := A) N n) :=
  exteriorPower.map_surjective (Submodule.mkQ_surjective N)

/-- The condition under which the de Rham differential descends through the
quotient `Ω[B⁄A] → Ω[B⁄A] ⧸ N`: in every degree `n`, the differential maps the
kernel of `quotientTermMap N n` into the kernel of `quotientTermMap N (n + 1)`.
For `N = pdRelations δ` it holds by `pdQuotientRelationStable`. -/
def QuotientRelationStable (N : Submodule B (Ω[B⁄A])) : Prop :=
  ∀ n : ℕ, LinearMap.ker (quotientTermMap (A := A) N n) ≤
    LinearMap.ker
      (quotientTermMap (A := A) N (n + 1) ∘ₗ DeRhamComplex.d A B n)

/-- The differential on the exterior powers of a stable quotient, characterised
by `quotientDifferential N hstable n ∘ quotientTermMap N n =
quotientTermMap N (n + 1) ∘ DeRhamComplex.d A B n`. -/
noncomputable def quotientDifferential (N : Submodule B (Ω[B⁄A]))
    (hstable : QuotientRelationStable (A := A) N) (n : ℕ) :
    QuotientTerm N n →ₗ[A] QuotientTerm N (n + 1) :=
  descendLinearMap
    (quotientTermMap (A := A) N n)
    (quotientTermMap (A := A) N (n + 1) ∘ₗ DeRhamComplex.d A B n)
    (quotientTermMap_surjective (A := A) N n) (hstable n)

/-- The descended differential squares to zero. -/
theorem quotientDifferential_comp_self (N : Submodule B (Ω[B⁄A]))
    (hstable : QuotientRelationStable (A := A) N) (n : ℕ) :
    quotientDifferential (A := A) N hstable (n + 1) ∘ₗ
      quotientDifferential (A := A) N hstable n = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := quotientTermMap_surjective (A := A) N n y
  have hcomp :
      (quotientDifferential (A := A) N hstable (n + 1) ∘ₗ
        quotientDifferential (A := A) N hstable n) ∘ₗ
          quotientTermMap (A := A) N n = 0 := by
    simp only [quotientDifferential]
    rw [LinearMap.comp_assoc]
    rw [descendLinearMap_comp]
    rw [← LinearMap.comp_assoc]
    rw [descendLinearMap_comp]
    rw [LinearMap.comp_assoc, DeRhamComplex.d_d, LinearMap.comp_zero]
  simpa [LinearMap.comp_apply] using congrArg (fun F ↦ F x) hcomp

/-- The de Rham complex `⋀[B]^• (Ω[B⁄A] ⧸ N)` of a stable quotient of `Ω[B⁄A]`,
as a cochain complex of `A`-modules. -/
noncomputable def deRhamComplexOfQuotient
    (N : Submodule B (Ω[B⁄A]))
    (hstable : QuotientRelationStable (A := A) N) :
    CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (QuotientTerm N n))
    (fun n ↦ ModuleCat.ofHom (quotientDifferential (A := A) N hstable n))
    (fun n ↦ by
      apply ModuleCat.hom_ext
      exact quotientDifferential_comp_self (A := A) N hstable n)

end AffineCrystalline.DeRham
