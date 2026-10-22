/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Envelope.FreeConstruction.RobyBasisPositive
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear independence of Roby monomials

Let `M` be a free `R`-module with basis `b`. By a theorem of Roby, the Roby
monomials of degree `n` are linearly independent, hence form a basis of the
degree `n` part `robyGrade b n` of `Γ_R(M)`. This file reformulates linear
independence in terms of finite linear relations, and proves it in degree `0`
using the augmentation.

## Main definitions

* `RobyFiniteSupportIndependenceData`: the statement that every finite
  linear relation among the Roby monomials of degree `n` is trivial.
* `robyGradeBasisOfFiniteSupportData`: the resulting basis of
  `robyGrade b n`.

## Main results

* `robyGrade_linearIndependent_iff_finiteSupport`: linear independence of the
  Roby monomials of degree `n` is equivalent to the triviality of finite linear
  relations among them.
* `robyGradeZero_linearIndependent`: the Roby monomials of degree `0` are
  linearly independent.

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

section PositiveGrade

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/--
The statement that the Roby monomials of degree `n` admit no nontrivial finite
linear relation: if `∑_{d ∈ supp c} c_d b^[d] = 0`, then `c = 0`.
-/
structure RobyFiniteSupportIndependenceData
    (b : Basis ι R M) (n : ℕ) where
  zero_of_finite_sum :
    ∀ c : robyDegreeIndex ι n →₀ R,
      c.support.sum (fun d ↦ c d • robyGradeMonomial b n d) = 0 →
        c = 0

/-- The Roby monomials of degree `n` are linearly independent if and only if they
admit no nontrivial finite linear relation. -/
theorem robyGrade_linearIndependent_iff_finiteSupport
    (b : Basis ι R M) (n : ℕ) :
    LinearIndependent R (robyGradeMonomial b n) ↔
      ∀ c : robyDegreeIndex ι n →₀ R,
        c.support.sum (fun d ↦ c d • robyGradeMonomial b n d) = 0 →
          c = 0 := by
  constructor
  · intro h c hc
    have h' : Function.Injective
        (Finsupp.linearCombination R (robyGradeMonomial b n)) := h
    apply h'
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using hc
  · intro h
    change Function.Injective
      (Finsupp.linearCombination R (robyGradeMonomial b n))
    intro c₁ c₂ h₁₂
    apply sub_eq_zero.mp
    apply h (c₁ - c₂)
    have hsub :
        Finsupp.linearCombination R (robyGradeMonomial b n) (c₁ - c₂) = 0 := by
      rw [map_sub, h₁₂, sub_self]
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using hsub

theorem robyGrade_linearIndependent_iff_finset
    (b : Basis ι R M) (n : ℕ) :
    LinearIndependent R (robyGradeMonomial b n) ↔
      ∀ s : Finset (robyDegreeIndex ι n),
        LinearIndependent R
          (robyGradeMonomial b n ∘ (Subtype.val : s → robyDegreeIndex ι n)) :=
  linearIndependent_iff_finset_linearIndependent

/-- The augmentation of a Roby monomial of degree `0` is `1`: the only such monomial
is `b^[0] = 1`. -/
theorem augmentation_robyGradeMonomial_zero (b : Basis ι R M) (d : robyDegreeIndex ι 0) :
    augmentation (R := R) (M := M) (robyGradeMonomial b 0 d).1 = 1 := by
  rw [robyGradeMonomial_apply_val, (robyDegree_eq_zero_iff d.1).mp d.2, robyMonomial_zero,
    map_one]

/--
The Roby monomials of degree `0` are linearly independent. The only such
monomial is `b^[0] = 1`, and `r · 1 = 0` implies `r = ε(r · 1) = 0`.
-/
theorem robyGradeZero_linearIndependent (b : Basis ι R M) :
    LinearIndependent R (robyGradeMonomial b 0) := by
  letI : Unique (robyDegreeIndex ι 0) :=
    { default := ⟨0, by simp [robyDegree]⟩
      uniq := fun d ↦ Subtype.ext ((robyDegree_eq_zero_iff d.1).mp d.2) }
  rw [linearIndependent_iffₛ]
  intro l₁ l₂ h
  apply Finsupp.unique_ext
  have h' :
      l₁ default • robyGradeMonomial b 0 default =
        l₂ default • robyGradeMonomial b 0 default := by
    simpa [Finsupp.linearCombination_unique] using h
  have h'' := congrArg (fun y : robyGrade b 0 ↦ augmentation (R := R) (M := M) y.1) h'
  simpa only [Submodule.coe_smul, map_smul, augmentation_robyGradeMonomial_zero, smul_eq_mul,
    mul_one] using h''

theorem robyGrade_linearIndependent_of_data
    (b : Basis ι R M) (n : ℕ)
    (C : RobyFiniteSupportIndependenceData b n) :
    LinearIndependent R (robyGradeMonomial b n) :=
  (robyGrade_linearIndependent_iff_finiteSupport b n).2 C.zero_of_finite_sum

theorem robyFiniteSupportIndependenceData_of_linearIndependent
    (b : Basis ι R M) (n : ℕ)
    (h : LinearIndependent R (robyGradeMonomial b n)) :
  RobyFiniteSupportIndependenceData b n :=
  { zero_of_finite_sum :=
      (robyGrade_linearIndependent_iff_finiteSupport b n).1 h }

theorem robyGrade_finite_relation_iff
    (b : Basis ι R M) (n : ℕ) :
    (∃ c : robyDegreeIndex ι n →₀ R,
      Finsupp.linearCombination R (robyGradeMonomial b n) c = 0 ∧ c ≠ 0) ↔
    (∃ s : Finset (robyDegreeIndex ι n),
      ∃ c : robyDegreeIndex ι n →₀ R,
        (↑c.support : Set (robyDegreeIndex ι n)) ⊆ (↑s : Set (robyDegreeIndex ι n)) ∧
          s.sum (fun d ↦ c d • robyGradeMonomial b n d) = 0 ∧ c ≠ 0) := by
  constructor
  · rintro ⟨c, hc, hc0⟩
    refine ⟨c.support, c, Set.Subset.rfl, ?_, hc0⟩
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using hc
  · rintro ⟨s, c, hcs, hc, hc0⟩
    have hcs' : c ∈ Finsupp.supported R R (↑s : Set (robyDegreeIndex ι n)) :=
      (Finsupp.mem_supported R c).2 hcs
    refine ⟨c, ?_, hc0⟩
    rw [Finsupp.linearCombination_apply_of_mem_supported R hcs']
    exact hc

theorem robyPositiveGradeMonomial_mem_positiveIdeal
    (b : Basis ι R M) {n : ℕ} (hn : 0 < n)
    (d : robyDegreeIndex ι n) :
    (robyGradeMonomial b n d).1 ∈ positiveIdeal (R := R) (M := M) :=
  robyMonomial_mem_positiveIdeal_of_degree_pos b hn d.2

theorem robyPositiveGrade_linearIndependent_iff_finiteSupport
    (b : Basis ι R M) {n : ℕ} (_hn : 0 < n) :
    LinearIndependent R (robyGradeMonomial b n) ↔
      ∀ c : robyDegreeIndex ι n →₀ R,
        c.support.sum (fun d ↦ c d • robyGradeMonomial b n d) = 0 →
          c = 0 :=
  robyGrade_linearIndependent_iff_finiteSupport b n

/-- The basis of `robyGrade b n` by Roby monomials, given a
`RobyFiniteSupportIndependenceData`. -/
noncomputable def robyGradeBasisOfFiniteSupportData
    (b : Basis ι R M) (n : ℕ)
    (C : RobyFiniteSupportIndependenceData b n) :
    Basis (robyDegreeIndex ι n) R (robyGrade b n) :=
  robyGradeBasisOfLinearIndependent b n
    (robyGrade_linearIndependent_of_data b n C)

@[simp]
theorem robyGradeBasis_of_finiteSupportData_apply
    (b : Basis ι R M) (n : ℕ)
    (C : RobyFiniteSupportIndependenceData b n)
    (d : robyDegreeIndex ι n) :
    robyGradeBasisOfFiniteSupportData b n C d =
      robyGradeMonomial b n d :=
  robyGradeBasis_of_linearIndependent_apply b n
    (robyGrade_linearIndependent_of_data b n C) d

end PositiveGrade

end FreeConstruction
end Envelope
end AffineCrystalline
