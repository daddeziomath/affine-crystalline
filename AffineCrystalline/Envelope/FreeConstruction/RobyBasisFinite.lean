/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Envelope.FreeConstruction.RobyDpowConstruction
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The degree zero part of the divided power algebra

Let `M` be a free `R`-module with basis `b`. The only exponent of degree `0` is
`d = 0`, whose Roby monomial is `1`. Hence the degree zero part `robyGrade b 0`
of `Γ_R(M)` is `R · 1`, and it is free with basis `{1}`; the coordinate of an
element on this basis is its augmentation.

## Main definitions

* `robyGradeZeroBasis`: the basis `{1}` of `robyGrade b 0`.

## Main results

* `robyDegree_eq_zero_iff`: an exponent has degree `0` if and only if it is `0`.
* `robyGrade_zero_eq_span_one`: `robyGrade b 0 = R · 1`.
* `robyGradeZeroBasis_repr`: the coordinate of `x` on `1` is `ε(x)`.

## References

* N. Roby, *Les algèbres à puissances divisées*, Bull. Sci. Math. (2) 89 (1965),
  75–91.
-/

open DividedPowers
open Module
open scoped BigOperators

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section DegreeZero

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

theorem robyDegree_eq_zero_iff (d : ι →₀ ℕ) :
    robyDegree d = 0 ↔ d = 0 := by
  have hdegree : robyDegree d = Finsupp.degree d := by
    rfl
  rw [hdegree]
  exact Finsupp.degree_eq_zero_iff d

@[simp]
theorem robyMonomial_zero (b : Basis ι R M) :
    robyMonomial b 0 = (1 : Γ) := by
  simp [robyMonomial]

theorem robyGrade_zero_eq_span_one (b : Basis ι R M) :
    robyGrade b 0 = Submodule.span R ({(1 : Γ)} : Set Γ) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro x ⟨d, hd, rfl⟩
    rw [robyDegree_eq_zero_iff] at hd
    subst d
    rw [robyMonomial_zero]
    exact Submodule.subset_span (Set.mem_singleton (1 : Γ))
  · refine Submodule.span_le.2 ?_
    rintro x rfl
    apply Submodule.subset_span
    exact ⟨0, rfl, by simp [robyMonomial]⟩

private theorem robyGrade_zero_one_mem (b : Basis ι R M) :
    (1 : Γ) ∈ robyGrade b 0 := by
  rw [robyGrade_zero_eq_span_one b]
  exact Submodule.subset_span (Set.mem_singleton (1 : Γ))

private theorem robyGrade_zero_singleton_linearIndependent (b : Basis ι R M) :
    LinearIndependent R (fun _ : Unit ↦
      (⟨(1 : Γ), robyGrade_zero_one_mem b⟩ : robyGrade b 0)) := by
  rw [linearIndependent_iffₛ]
  intro l₁ l₂ h
  apply Finsupp.unique_ext
  have h' : l₁ default •
      (⟨(1 : Γ), robyGrade_zero_one_mem b⟩ : robyGrade b 0) =
      l₂ default •
        (⟨(1 : Γ), robyGrade_zero_one_mem b⟩ : robyGrade b 0) := by
    simpa [Finsupp.linearCombination_unique] using h
  have h'' := congrArg Subtype.val h'
  have h''' := congrArg (augmentation (R := R) (M := M)) h''
  simpa [smul_eq_mul] using h'''

private theorem robyGrade_zero_singleton_span (b : Basis ι R M) :
    (⊤ : Submodule R (robyGrade b 0)) ≤
      Submodule.span R (Set.range (fun _ : Unit ↦
        (⟨(1 : Γ), robyGrade_zero_one_mem b⟩ : robyGrade b 0)) ) := by
  intro x hx
  have hx' : x.1 ∈ Submodule.span R ({(1 : Γ)} : Set Γ) := by
    rw [← robyGrade_zero_eq_span_one b]
    exact x.2
  rcases (Submodule.mem_span_singleton.mp hx') with ⟨r, hr⟩
  have hxr : x = r • (⟨(1 : Γ), robyGrade_zero_one_mem b⟩ : robyGrade b 0) := by
    apply Subtype.ext
    exact hr.symm
  rw [hxr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)

/-- The basis `{1}` of the degree zero part `robyGrade b 0 = R · 1`. -/
noncomputable def robyGradeZeroBasis (b : Basis ι R M) :
    Basis Unit R (robyGrade b 0) :=
  Module.Basis.mk
    (robyGrade_zero_singleton_linearIndependent b)
    (robyGrade_zero_singleton_span b)

@[simp]
theorem robyGradeZeroBasis_apply (b : Basis ι R M) (i : Unit) :
    robyGradeZeroBasis b i =
      (⟨(1 : Γ), robyGrade_zero_one_mem b⟩ : robyGrade b 0) := by
  rw [robyGradeZeroBasis]
  exact Module.Basis.mk_apply _ _ _

theorem robyGradeZeroBasis_apply_val (b : Basis ι R M) (i : Unit) :
    (robyGradeZeroBasis b i).1 = (1 : Γ) := by
  rw [robyGradeZeroBasis_apply]

/-- The coordinate of `x ∈ robyGrade b 0` on the basis `{1}` is `ε(x)`. -/
theorem robyGradeZeroBasis_repr (b : Basis ι R M) (x : robyGrade b 0) :
    (robyGradeZeroBasis b).repr x () =
      augmentation (R := R) (M := M) x.1 := by
  have hx' : x.1 ∈ Submodule.span R ({(1 : Γ)} : Set Γ) := by
    rw [← robyGrade_zero_eq_span_one b]
    exact x.2
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx'
  have hx : x = r • robyGradeZeroBasis b () := by
    rw [robyGradeZeroBasis_apply]
    exact Subtype.ext hr.symm
  rw [hx, LinearEquiv.map_smul, Basis.repr_self, Submodule.coe_smul,
    robyGradeZeroBasis_apply_val]
  simp

end DegreeZero

end FreeConstruction
end Envelope
end AffineCrystalline
