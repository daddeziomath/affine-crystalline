/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Envelope.FreeConstruction.RobyBasisFinite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Spanning of the graded pieces by Roby monomials

Let `M` be a free `R`-module with basis `b`. The degree `n` part
`robyGrade b n` of `Γ_R(M)` is spanned by the Roby monomials `b^[d]` with
`|d| = n`, so every element of it is a finite `R`-linear combination of these
monomials. If moreover these monomials are linearly independent, they form a
basis of `robyGrade b n`. Roby monomials of positive degree lie in `Γ⁺`.

## Main definitions

* `robyDegreeIndex`: the exponents of degree `n`.
* `robyGradeMonomial`: the Roby monomial `b^[d]` as an element of
  `robyGrade b n`.
* `robyGradeBasisOfLinearIndependent`: the basis of `robyGrade b n` given by
  linearly independent Roby monomials.
* `robyGradeEmptyPositiveBasis`: the empty basis of `robyGrade b n`, `n > 0`,
  when `M = 0`.

## Main results

* `robyGrade_normalForm`: every element of `robyGrade b n` is a finite linear
  combination of Roby monomials of degree `n`.
* `robyMonomial_mem_positiveIdeal_of_ne_zero`: `b^[d] ∈ Γ⁺` for `d ≠ 0`.
* `robyGrade_empty_eq_bot`: if `M = 0`, then `robyGrade b n = 0` for `n > 0`.

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

section PositiveNormalForm

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-- The exponent type indexing the degree-`n` Roby monomials. -/
abbrev robyDegreeIndex (ι : Type v) (n : ℕ) :=
  {d : ι →₀ ℕ // robyDegree d = n}

/-- The degree-`n` Roby monomial, regarded as an element of its graded piece. -/
def robyGradeMonomial (b : Basis ι R M) (n : ℕ) :
    robyDegreeIndex ι n → robyGrade b n :=
  fun d ↦ ⟨robyMonomial b d.1,
    Eq.mp
      (congrArg (fun k : ℕ ↦ robyMonomial b d.1 ∈ robyGrade b k) d.2)
      (robyMonomial_mem_grade b d.1)⟩

@[simp]
theorem robyGradeMonomial_apply_val (b : Basis ι R M) (n : ℕ)
    (d : robyDegreeIndex ι n) :
    (robyGradeMonomial b n d).1 = robyMonomial b d.1 :=
  rfl

theorem robyGrade_eq_span_range (b : Basis ι R M) (n : ℕ) :
    robyGrade b n =
      Submodule.span R (Set.range fun d : robyDegreeIndex ι n ↦
        robyMonomial b d.1) := by
  apply congrArg (Submodule.span R)
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d.1, d.2, rfl⟩

/-! ## Spanning -/

/-- An element of `Γ_R(M)` lies in `robyGrade b n` if and only if it is a finite
linear combination of Roby monomials of degree `n`. -/
theorem robyGrade_mem_iff_exists_finsupp
    (b : Basis ι R M) {n : ℕ} {x : Γ} :
    x ∈ robyGrade b n ↔
      ∃ c : robyDegreeIndex ι n →₀ R,
        Finsupp.linearCombination R
            (fun d : robyDegreeIndex ι n ↦ robyMonomial b d.1) c = x := by
  rw [robyGrade_eq_span_range]
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- Every element of `robyGrade b n` is a finite linear combination of Roby
monomials of degree `n`. -/
theorem robyGrade_normalForm
    (b : Basis ι R M) {n : ℕ} {x : Γ} (hx : x ∈ robyGrade b n) :
    ∃ c : robyDegreeIndex ι n →₀ R,
      c.sum (fun d a ↦ a • robyMonomial b d.1) = x := by
  rcases (robyGrade_mem_iff_exists_finsupp b).mp hx with ⟨c, hc⟩
  exact ⟨c, by simpa [Finsupp.linearCombination_apply] using hc⟩

theorem robyDegree_ne_zero_of_pos {d : ι →₀ ℕ} {n : ℕ}
    (hn : 0 < n) (hd : robyDegree d = n) : d ≠ 0 := by
  intro hzero
  subst d
  apply hn.ne'
  exact hd.symm.trans ((robyDegree_eq_zero_iff (0 : ι →₀ ℕ)).2 rfl)

/-- A Roby monomial `b^[d]` with `d ≠ 0` lies in `Γ⁺`. -/
theorem robyMonomial_mem_positiveIdeal_of_ne_zero
    (b : Basis ι R M) {d : ι →₀ ℕ} (hd : d ≠ 0) :
    robyMonomial b d ∈ positiveIdeal (R := R) (M := M) := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
  have hdp : DividedPowerAlgebra.dp R (d i) (b i) ∈
      positiveIdeal (R := R) (M := M) :=
    dp_mem_positiveIdeal (Finsupp.mem_support_iff.mp hi) (b i)
  have hmul := (positiveIdeal (R := R) (M := M)).mul_mem_left
    ((d.erase i).prod fun j k ↦ DividedPowerAlgebra.dp R k (b j)) hdp
  change d.prod (fun j k ↦ DividedPowerAlgebra.dp R k (b j)) ∈
    positiveIdeal (R := R) (M := M)
  rw [← Finsupp.mul_prod_erase d i
    (fun j k ↦ DividedPowerAlgebra.dp R k (b j)) hi]
  simpa [mul_comm] using hmul

theorem robyMonomial_mem_positiveIdeal_of_degree_pos
    (b : Basis ι R M) {d : ι →₀ ℕ} {n : ℕ}
    (hn : 0 < n) (hd : robyDegree d = n) :
    robyMonomial b d ∈ positiveIdeal (R := R) (M := M) :=
  robyMonomial_mem_positiveIdeal_of_ne_zero b
    (robyDegree_ne_zero_of_pos hn hd)

/-! ## Bases from linear independence -/

private theorem robyGrade_span_range_le_top
    (b : Basis ι R M) (n : ℕ) :
    Submodule.span R (Set.range (robyGradeMonomial b n)) =
      (⊤ : Submodule R (robyGrade b n)) := by
  apply le_antisymm
  · exact le_top
  · intro x hx
    have hx' : x.1 ∈ robyGrade b n := x.2
    obtain ⟨c, hc⟩ := robyGrade_normalForm b hx'
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

/-- If the Roby monomials of degree `n` are linearly independent, they form a
basis of `robyGrade b n`. -/
noncomputable def robyGradeBasisOfLinearIndependent
    (b : Basis ι R M) (n : ℕ)
    (hι : LinearIndependent R (robyGradeMonomial b n)) :
    Basis (robyDegreeIndex ι n) R (robyGrade b n) :=
  Module.Basis.mk hι (by
    rw [robyGrade_span_range_le_top b n])

@[simp]
theorem robyGradeBasis_of_linearIndependent_apply
    (b : Basis ι R M) (n : ℕ)
    (hι : LinearIndependent R (robyGradeMonomial b n))
    (d : robyDegreeIndex ι n) :
    robyGradeBasisOfLinearIndependent b n hι d =
      robyGradeMonomial b n d :=
  Module.Basis.mk_apply _ _ d

end PositiveNormalForm

section EmptyPositiveGrade

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable [Subsingleton M]

local notation "Γ" => DividedPowerAlgebra R M

/-! ## The zero module

If `M = 0`, with the empty basis, the only exponent is `0`, so the graded pieces
of positive degree vanish and have the empty basis.
-/

/-- If `M = 0`, then `robyGrade b n = 0` for `n > 0`. -/
theorem robyGrade_empty_eq_bot {n : ℕ} (hn : n ≠ 0) :
    robyGrade (Basis.empty M : Basis PEmpty R M) n =
      (⊥ : Submodule R Γ) := by
  apply le_antisymm
  · rw [robyGrade]
    refine Submodule.span_le.2 ?_
    rintro x ⟨d, hd, rfl⟩
    have hd0 : d = 0 := by
      ext i
      exact PEmpty.elim i
    subst d
    have hzero : n = 0 := by
      calc
        n = robyDegree (0 : PEmpty →₀ ℕ) := hd.symm
        _ = 0 := by simp [robyDegree]
    exact (hn hzero).elim
  · exact bot_le

/-- If `M = 0`, the empty family is a basis of `robyGrade b n` for `n > 0`. -/
noncomputable def robyGradeEmptyPositiveBasis {n : ℕ} (hn : n ≠ 0) :
    Basis PEmpty R (robyGrade (Basis.empty M : Basis PEmpty R M) n) :=
  (robyGrade_empty_eq_bot (R := R) (M := M) hn).symm ▸
    (Basis.empty (⊥ : Submodule R Γ) : Basis PEmpty R (⊥ : Submodule R Γ))

end EmptyPositiveGrade

end FreeConstruction
end Envelope
end AffineCrystalline
