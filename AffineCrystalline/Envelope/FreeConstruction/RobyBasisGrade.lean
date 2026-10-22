/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.RobyIndependence

/-!
# Bases of the graded pieces of the divided power algebra

Let `M` be a free `R`-module with basis `b`. The Roby monomials of degree `n`
span the degree `n` part `robyGrade b n` of `Γ_R(M)`; when they are linearly
independent, they form a basis of it. Linear independence holds in degree `0`
(`robyGradeZero_linearIndependent`), so a family of such bases reduces to linear
independence in positive degrees. Together with a basis of `Γ_R(M)` by Roby
monomials, these bases yield a `RobyBasisData`.

## Main definitions

* `RobyGradeIndependenceData`: the absence of nontrivial finite linear
  relations among the Roby monomials of degree `n`.
* `robyGradeBasisOfIndependenceData`: the resulting basis of `robyGrade b n`.
* `RobyPositiveGradeBasisFamilyData`, `RobyGradeBasisFamilyData`:
  such data in all positive degrees, resp. in all degrees.
* `RobyGradeTotalBasisData`: a family of graded bases together with a
  basis of `Γ_R(M)` by Roby monomials and the description of `Γ⁺` in
  coordinates.

## Main results

* `robyGradeMonomial_span_eq_top`: the Roby monomials of degree `n` span
  `robyGrade b n`.
* `robyGradeIndependenceData_zero`: the independence data in degree `0`.
* `RobyPositiveGradeBasisFamilyData.toRobyGradeBasisFamilyData`:
  independence data in positive degrees extend to all degrees.
* `RobyGradeTotalBasisData.toRobyBasisData`: the associated
  `RobyBasisData`.

## References

* N. Roby, *Lois polynômes et lois formelles en théorie des modules*,
  Ann. Sci. École Norm. Sup. (3) 80 (1963), 213–348.
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

section HomogeneousGrade

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-! ## Spanning -/

/-- The Roby monomials of degree `n` span `robyGrade b n`. -/
theorem robyGradeMonomial_span_eq_top
    (b : Basis ι R M) (n : ℕ) :
    Submodule.span R (Set.range (robyGradeMonomial b n)) =
      (⊤ : Submodule R (robyGrade b n)) := by
  apply le_antisymm
  · exact le_top
  · intro x hx
    obtain ⟨c, hc⟩ := robyGrade_normalForm b x.2
    have hsum :
        Finsupp.linearCombination R (robyGradeMonomial b n) c = x := by
      apply Subtype.ext
      change (robyGrade b n).subtype
          (Finsupp.linearCombination R (robyGradeMonomial b n) c) = x.1
      rw [LinearMap.map_finsupp_linearCombination]
      simpa [Finsupp.linearCombination_apply, Function.comp_def,
        robyGradeMonomial] using hc
    rw [← hsum]
    rw [← Finsupp.range_linearCombination]
    exact ⟨c, rfl⟩

/-! ## Linear independence -/

/--
The statement that the Roby monomials of degree `n` admit no nontrivial finite
linear relation: if `∑_{d ∈ supp c} c_d b^[d] = 0`, then `c = 0`.
-/
structure RobyGradeIndependenceData
    (b : Basis ι R M) (n : ℕ) where
  zero_of_finite_sum :
    ∀ c : robyDegreeIndex ι n →₀ R,
      c.support.sum (fun d ↦ c d • robyGradeMonomial b n d) = 0 →
        c = 0

/-- The Roby monomials of degree `0` admit no nontrivial finite linear relation. -/
theorem robyGradeIndependenceData_zero (b : Basis ι R M) :
    RobyGradeIndependenceData b 0 :=
  { zero_of_finite_sum :=
      (robyGrade_linearIndependent_iff_finiteSupport b 0).1
        (robyGradeZero_linearIndependent b) }

/-- A `RobyGradeIndependenceData` as a
`RobyFiniteSupportIndependenceData`. -/
theorem robyGradeIndependenceData_toFiniteSupport
    (b : Basis ι R M) (n : ℕ)
    (C : RobyGradeIndependenceData b n) :
    RobyFiniteSupportIndependenceData b n :=
  { zero_of_finite_sum := C.zero_of_finite_sum }

theorem robyGradeMonomial_linearIndependent_of_data
    (b : Basis ι R M) (n : ℕ)
    (C : RobyGradeIndependenceData b n) :
    LinearIndependent R (robyGradeMonomial b n) :=
  robyGrade_linearIndependent_of_data b n
    (robyGradeIndependenceData_toFiniteSupport b n C)

/-- A `RobyGradeIndependenceData` in every positive degree. Since the
degree `0` case holds unconditionally, this gives independence data in all degrees
(`grade_independence`). -/
structure RobyPositiveGradeBasisFamilyData (b : Basis ι R M) where
  positive_grade_independence :
    ∀ {n : ℕ}, 0 < n → RobyGradeIndependenceData b n

namespace RobyPositiveGradeBasisFamilyData

variable {b : Basis ι R M}
variable (C : RobyPositiveGradeBasisFamilyData (R := R) (M := M) b)

theorem grade_independence (C : RobyPositiveGradeBasisFamilyData
    (R := R) (M := M) b) (n : ℕ) :
    RobyGradeIndependenceData b n := by
  by_cases hn : n = 0
  · subst n
    exact robyGradeIndependenceData_zero b
  · exact RobyPositiveGradeBasisFamilyData.positive_grade_independence C
      (Nat.pos_of_ne_zero hn)

end RobyPositiveGradeBasisFamilyData

/-! ## Bases of the graded pieces -/

/-- The basis of `robyGrade b n` by the Roby monomials of degree `n`, given a
`RobyGradeIndependenceData`. -/
noncomputable def robyGradeBasisOfIndependenceData
    (b : Basis ι R M) (n : ℕ)
    (C : RobyGradeIndependenceData b n) :
    Basis (robyDegreeIndex ι n) R (robyGrade b n) :=
  Module.Basis.mk
    (robyGradeMonomial_linearIndependent_of_data b n C)
    (by rw [robyGradeMonomial_span_eq_top b n])

@[simp]
theorem robyGradeBasisOfIndependenceData_apply
    (b : Basis ι R M) (n : ℕ)
    (C : RobyGradeIndependenceData b n)
    (d : robyDegreeIndex ι n) :
    robyGradeBasisOfIndependenceData b n C d = robyGradeMonomial b n d :=
  Module.Basis.mk_apply _ _ d

/-! ## Families of bases -/

/--
A `RobyGradeIndependenceData` in every degree `n`.
-/
structure RobyGradeBasisFamilyData (b : Basis ι R M) where
  grade_independence :
    ∀ n : ℕ, RobyGradeIndependenceData b n

namespace RobyGradeBasisFamilyData

variable {b : Basis ι R M}
variable (C : RobyGradeBasisFamilyData (R := R) (M := M) b)

/-- The basis of `robyGrade b n` by Roby monomials. -/
noncomputable def gradeBasis (n : ℕ) :
    Basis (robyDegreeIndex ι n) R (robyGrade b n) :=
  robyGradeBasisOfIndependenceData b n (C.grade_independence n)

@[simp]
theorem gradeBasis_apply (n : ℕ) (d : robyDegreeIndex ι n) :
    C.gradeBasis n d = robyGradeMonomial b n d :=
  robyGradeBasisOfIndependenceData_apply b n (C.grade_independence n) d

end RobyGradeBasisFamilyData

/-- Independence data in positive degrees extend to all degrees. -/
theorem RobyPositiveGradeBasisFamilyData.toRobyGradeBasisFamilyData
    {b : Basis ι R M}
    (C : RobyPositiveGradeBasisFamilyData (R := R) (M := M) b) :
    RobyGradeBasisFamilyData b :=
  { grade_independence := RobyPositiveGradeBasisFamilyData.grade_independence C }

/-- A basis `b` of `M`, bases of the graded pieces `robyGrade b n`, and a basis of
`Γ_R(M)` by Roby monomials, together with the description of `Γ⁺` in
coordinates. The remaining field of `RobyBasisData`, `b^[d] ∈ Γ⁺` for `d ≠ 0`, holds by
`robyMonomial_mem_positiveIdeal_of_ne_zero`. -/
structure RobyGradeTotalBasisData where
  moduleBasis : Basis ι R M
  grades : RobyGradeBasisFamilyData moduleBasis
  totalBasis : Basis (ι →₀ ℕ) R Γ
  totalBasis_apply : ∀ d : ι →₀ ℕ,
    totalBasis d = robyMonomial moduleBasis d
  totalBasis_repr_aug_zero : ∀ x : Γ,
    x ∈ positiveIdeal (R := R) (M := M) ↔ (totalBasis.repr x) 0 = 0

namespace RobyGradeTotalBasisData

variable (C : RobyGradeTotalBasisData (R := R) (M := M) (ι := ι))

/-- The associated `RobyBasisData`. -/
noncomputable def toRobyBasisData :
    RobyBasisData (R := R) (M := M) (ι := ι) :=
  { moduleBasis := C.moduleBasis
    gradeBasis := RobyGradeBasisFamilyData.gradeBasis C.grades
    totalBasis := C.totalBasis
    gradeBasis_apply := by
      intro n d hd
      exact congrArg Subtype.val
        (RobyGradeBasisFamilyData.gradeBasis_apply C.grades n ⟨d, hd⟩)
    totalBasis_apply := C.totalBasis_apply
    totalBasis_repr_aug_zero := C.totalBasis_repr_aug_zero
    monomial_mem_positive := by
      intro d hd
      exact robyMonomial_mem_positiveIdeal_of_ne_zero C.moduleBasis hd }

@[simp]
theorem toRobyBasisData_moduleBasis :
    C.toRobyBasisData.moduleBasis = C.moduleBasis :=
  rfl

@[simp]
theorem toRobyBasisData_gradeBasis (n : ℕ) :
    C.toRobyBasisData.gradeBasis n =
      RobyGradeBasisFamilyData.gradeBasis C.grades n :=
  rfl

@[simp]
theorem toRobyBasisData_totalBasis :
    C.toRobyBasisData.totalBasis = C.totalBasis :=
  rfl

theorem toRobyBasisData_gradeBasis_apply
    (n : ℕ) (d : ι →₀ ℕ) (hd : robyDegree d = n) :
    (C.toRobyBasisData.gradeBasis n ⟨d, hd⟩).1 =
      robyMonomial C.moduleBasis d :=
  C.toRobyBasisData.gradeBasis_apply n d hd

theorem toRobyBasisData_monomial_mem_positive
    {d : ι →₀ ℕ} (hd : d ≠ 0) :
    robyMonomial C.moduleBasis d ∈ positiveIdeal (R := R) (M := M) :=
  C.toRobyBasisData.monomial_mem_positive hd

end RobyGradeTotalBasisData

end HomogeneousGrade

end FreeConstruction
end Envelope
end AffineCrystalline
