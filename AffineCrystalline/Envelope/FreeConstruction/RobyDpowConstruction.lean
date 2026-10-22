/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.DPAlgebraAugmentation
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Roby's divided powers for a free module

Let `M` be a free `R`-module with basis `(bᵢ)_{i ∈ ι}`. For an exponent
`d : ι →₀ ℕ`, the Roby monomial `b^[d] = ∏ᵢ [dᵢ](bᵢ)` has degree `∑ᵢ dᵢ`. By a
theorem of Roby, the Roby monomials form a basis of `Γ_R(M)`, and those of
degree `n` form a basis of the degree-`n` part. Writing `x ∈ Γ⁺` in this basis
as `x = ∑_d x_d b^[d]`, the divided powers of `x` are given by the explicit
formula `robyDpow`, a sum over multisets `k` of size `n` of exponents in the
support of `x`, with integer coefficients `robyCoefficient`.

In this file we define these objects, and show that the formula defines
divided powers on `Γ⁺` satisfying Roby's formula on generators, given the
following data:

* `RobyBasisData`: a basis of `M`, bases of `Γ_R(M)` and of its graded
  pieces by Roby monomials, and the description of `Γ⁺` in coordinates;
* `RobyDpowLawData`: the divided power axioms for `robyDpow`, and
  Roby's formula `robyDpow n [k](m) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`.

## Main definitions

* `robyDegree`, `robyMonomial`, `robyGrade`: the degree of an exponent, the Roby
  monomial `b^[d]` and the span of the Roby monomials of degree `n`.
* `robyCoefficient`: the integer coefficients in Roby's formula.
* `robyDpow`: Roby's formula for the divided powers of an element of `Γ⁺`.
* `RobyBasisData`, `RobyDpowLawData`: the data above.
* `dividedPowers`: the divided powers on `Γ⁺` defined by `robyDpow`.

## Main results

* `dividedPowers_generator_formula`: Roby's formula on generators.
* `dividedPowers_unique`: any divided powers on `Γ⁺` satisfying Roby's formula
  on generators equal `dividedPowers`.

## References

* N. Roby, *Lois polynômes et lois formelles en théorie des modules*,
  Ann. Sci. École Norm. Sup. (3) 80 (1963), 213–348.
* N. Roby, *Les algèbres à puissances divisées*, Bull. Sci. Math. (2) 89 (1965),
  75–91.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *A formalization of divided
  powers in Lean*, ITP 2025, LIPIcs, 4:1–4:17.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *Formalizing polynomial laws
  and the universal divided power algebra*, arXiv:2512.05750.
-/

open DividedPowers
open Module
open scoped BigOperators

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section Construction

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-! ## Roby monomials -/

/-- The degree `∑ᵢ dᵢ` of an exponent `d : ι →₀ ℕ`. -/
def robyDegree (d : ι →₀ ℕ) : ℕ := d.sum fun _ n ↦ n

/-- The Roby monomial `b^[d] = ∏ᵢ [dᵢ](bᵢ)`. -/
def robyMonomial (b : Basis ι R M) (d : ι →₀ ℕ) : Γ :=
  d.prod fun i n ↦ DividedPowerAlgebra.dp R n (b i)

/-- The `R`-submodule of `Γ_R(M)` spanned by the Roby monomials of degree `n`. -/
def robyGrade (b : Basis ι R M) (n : ℕ) : Submodule R Γ :=
  Submodule.span R {x | ∃ d, robyDegree d = n ∧ x = robyMonomial b d}

theorem robyMonomial_mem_grade (b : Basis ι R M) (d : ι →₀ ℕ) :
    robyMonomial b d ∈ robyGrade b (robyDegree d) := by
  change robyMonomial b d ∈
    Submodule.span R {x | ∃ e, robyDegree e = robyDegree d ∧ x = robyMonomial b e}
  apply Submodule.subset_span
  exact ⟨d, rfl, rfl⟩

/-! ## Roby's formula -/

/-- The integer coefficient attached to a multiset `k` of size `n` of exponents
supported in a finite set `s` in Roby's formula for divided powers (the
coefficient `cK` of Chambert-Loir and de Frutos-Fernández). -/
def robyCoefficient {n : ℕ} (k : Sym (ι →₀ ℕ) n)
    (s : Finset (ι →₀ ℕ)) : ℕ := by
  classical
  exact
    (k.val.sum.prod fun i _ ↦ Nat.multinomial s fun a ↦ (Multiset.count a k.val • a) i) *
      (∏ d ∈ s,
        Nat.factorial (Multiset.count d k.val) ^ (d.support.card - 1) *
          (∏ i ∈ d.support, (Multiset.count d k.val).uniformBell (d i)))

@[simp]
theorem robyCoefficient_zero {s : Finset (ι →₀ ℕ)} :
    robyCoefficient (ι := ι) (k := (∅ : Sym (ι →₀ ℕ) 0)) s = 1 := by
  classical
  rw [robyCoefficient]
  change
    ((∅ : Multiset (ι →₀ ℕ)).sum.prod
        (fun i _ ↦ Nat.multinomial s fun a ↦ (Multiset.count a (∅ : Multiset (ι →₀ ℕ)) • a) i)) *
      (∏ d ∈ s,
        Nat.factorial (Multiset.count d (∅ : Multiset (ι →₀ ℕ))) ^ (d.support.card - 1) *
          (∏ i ∈ d.support,
            (Multiset.count d (∅ : Multiset (ι →₀ ℕ))).uniformBell (d i))) = 1
  simp [Nat.uniformBell_zero_left]

/-- Roby's formula for the `n`-th divided power of `x ∈ Γ⁺`, in terms of the
coordinates of `x` in a basis `B` of `Γ_R(M)` (indexed by exponents). It is
defined to be `0` for `x ∉ Γ⁺`. -/
def robyDpow (b : Basis ι R M) (B : Basis (ι →₀ ℕ) R Γ)
    (n : ℕ) (x : Γ) : Γ := by
  classical
  exact
    if x ∈ positiveIdeal (R := R) (M := M) then
      ∑ k ∈ ((B.repr x).support.sym n),
        robyCoefficient (ι := ι) k ((B.repr x).support) •
          ((∏ d ∈ (B.repr x).support,
            (B.repr x) d ^ Multiset.count d k.val) •
            robyMonomial b k.val.sum)
    else 0

@[simp]
theorem robyDpow_of_not_mem
    (b : Basis ι R M) (B : Basis (ι →₀ ℕ) R Γ)
    {n : ℕ} {x : Γ} (hx : x ∉ positiveIdeal (R := R) (M := M)) :
    robyDpow b B n x = 0 := by
  simp [robyDpow, hx]

/-! ## Bases by Roby monomials -/

/--
A basis `b` of `M`, together with bases of the graded pieces `robyGrade b n`
(`gradeBasis`) and of `Γ_R(M)` (`totalBasis`) given by the Roby monomials, and
the following facts used to evaluate `robyDpow` on `Γ⁺`:

* `x ∈ Γ⁺` if and only if the coordinate of `x` on `b^[0] = 1` vanishes;
* `b^[d] ∈ Γ⁺` for `d ≠ 0`.
-/
structure RobyBasisData where
  moduleBasis : Basis ι R M
  gradeBasis : ∀ n : ℕ,
    Basis {d : ι →₀ ℕ // robyDegree d = n} R
      (robyGrade moduleBasis n)
  totalBasis : Basis (ι →₀ ℕ) R Γ
  gradeBasis_apply : ∀ (n : ℕ) (d : ι →₀ ℕ) (hd : robyDegree d = n),
    (gradeBasis n ⟨d, hd⟩).1 = robyMonomial moduleBasis d
  totalBasis_apply : ∀ d : ι →₀ ℕ,
    totalBasis d = robyMonomial moduleBasis d
  totalBasis_repr_aug_zero : ∀ x : Γ,
    x ∈ positiveIdeal (R := R) (M := M) ↔ (totalBasis.repr x) 0 = 0
  monomial_mem_positive : ∀ {d : ι →₀ ℕ}, d ≠ 0 →
    robyMonomial moduleBasis d ∈ positiveIdeal (R := R) (M := M)

namespace RobyBasisData

variable (C : RobyBasisData (R := R) (M := M) (ι := ι))

@[simp]
theorem totalBasis_apply_eq (d : ι →₀ ℕ) :
    C.totalBasis d = robyMonomial C.moduleBasis d :=
  C.totalBasis_apply d

theorem gradeBasis_apply_eq (n : ℕ) (d : ι →₀ ℕ) (hd : robyDegree d = n) :
    (C.gradeBasis n ⟨d, hd⟩).1 = robyMonomial C.moduleBasis d :=
  C.gradeBasis_apply n d hd

theorem monomial_mem_positive' {d : ι →₀ ℕ} (hd : d ≠ 0) :
    robyMonomial C.moduleBasis d ∈ positiveIdeal (R := R) (M := M) :=
  C.monomial_mem_positive hd

end RobyBasisData

/-! ## The divided power axioms for Roby's formula -/

/--
The divided power axioms for `robyDpow` on `Γ⁺`, together with Roby's formula
`robyDpow n [k](m) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`.
-/
structure RobyDpowLawData
    (C : RobyBasisData (R := R) (M := M) (ι := ι)) where
  dpow_mem : ∀ {n : ℕ} {x : Γ}, n ≠ 0 →
    x ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis n x ∈ positiveIdeal (R := R) (M := M)
  dpow_zero : ∀ {x : Γ}, x ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis 0 x = 1
  dpow_one : ∀ {x : Γ}, x ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis 1 x = x
  dpow_add : ∀ {n : ℕ} {x y : Γ},
    x ∈ positiveIdeal (R := R) (M := M) →
    y ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis n (x + y) =
      (Finset.antidiagonal n).sum fun k ↦
        robyDpow C.moduleBasis C.totalBasis k.1 x *
          robyDpow C.moduleBasis C.totalBasis k.2 y
  dpow_mul : ∀ {n : ℕ} {a x : Γ},
    x ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis n (a * x) =
      a ^ n * robyDpow C.moduleBasis C.totalBasis n x
  mul_dpow : ∀ {m n : ℕ} {x : Γ},
    x ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis m x *
        robyDpow C.moduleBasis C.totalBasis n x =
      (Nat.choose (m + n) m : Γ) *
        robyDpow C.moduleBasis C.totalBasis (m + n) x
  dpow_comp : ∀ {m n : ℕ} {x : Γ}, n ≠ 0 →
    x ∈ positiveIdeal (R := R) (M := M) →
    robyDpow C.moduleBasis C.totalBasis m
        (robyDpow C.moduleBasis C.totalBasis n x) =
      (Nat.uniformBell m n : Γ) *
        robyDpow C.moduleBasis C.totalBasis (m * n) x
  generator_formula : ∀ {n k : ℕ} {m : M}, k ≠ 0 →
    robyDpow C.moduleBasis C.totalBasis n
        (DividedPowerAlgebra.dp R k m) =
      generatorDpow (R := R) (M := M) n k m

/-! ## Roby's divided powers -/

/-- The divided powers on `Γ⁺` given by Roby's formula `robyDpow`. -/
def dividedPowers (C : RobyBasisData (R := R) (M := M) (ι := ι))
    (L : RobyDpowLawData C) :
    DividedPowers (positiveIdeal (R := R) (M := M)) where
  dpow := robyDpow C.moduleBasis C.totalBasis
  dpow_null hx := robyDpow_of_not_mem C.moduleBasis C.totalBasis hx
  dpow_zero hx := L.dpow_zero hx
  dpow_one hx := L.dpow_one hx
  dpow_mem hn hx := L.dpow_mem hn hx
  dpow_add hx hy := L.dpow_add hx hy
  dpow_mul hx := L.dpow_mul hx
  mul_dpow hx := L.mul_dpow hx
  dpow_comp hn hx := L.dpow_comp hn hx

@[simp]
theorem dividedPowers_apply
    (C : RobyBasisData (R := R) (M := M) (ι := ι))
    (L : RobyDpowLawData C) (n : ℕ) (x : Γ) :
    (dividedPowers C L).dpow n x = robyDpow C.moduleBasis C.totalBasis n x :=
  rfl

/-- Roby's formula `γ_n([k](m)) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`. -/
theorem dividedPowers_generator_formula
    (C : RobyBasisData (R := R) (M := M) (ι := ι))
    (L : RobyDpowLawData C) {n k : ℕ} {m : M} (hk : k ≠ 0) :
    (dividedPowers C L).dpow n (DividedPowerAlgebra.dp R k m) =
      generatorDpow (R := R) (M := M) n k m := by
  rw [dividedPowers_apply]
  exact L.generator_formula hk

/-- Any divided powers on `Γ⁺` satisfying Roby's formula on generators are equal
to `dividedPowers C L`. -/
theorem dividedPowers_unique
    (C : RobyBasisData (R := R) (M := M) (ι := ι))
    (L : RobyDpowLawData C)
    (H : DividedPowers (positiveIdeal (R := R) (M := M)))
    (hH : ∀ {n k : ℕ} {m : M}, k ≠ 0 →
      H.dpow n (DividedPowerAlgebra.dp R k m) =
        generatorDpow (R := R) (M := M) n k m) :
    H = dividedPowers C L := by
  refine dividedPowers_eq_of_positiveGenerator_agreement
    (R := R) (M := M) (h₁ := dividedPowers C L) (h₂ := H) ?_
  intro n x hx
  rcases hx with ⟨k, hk, m, rfl⟩
  calc
    (dividedPowers C L).dpow n (DividedPowerAlgebra.dp R k m) =
        generatorDpow (R := R) (M := M) n k m :=
      dividedPowers_generator_formula C L hk
    _ = H.dpow n (DividedPowerAlgebra.dp R k m) := (hH hk).symm

end Construction

end FreeConstruction
end Envelope
end AffineCrystalline
