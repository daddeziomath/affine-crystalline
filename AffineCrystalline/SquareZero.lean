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

/-!
# Divided powers on a square-zero extension

Let `(A, I, γ)` be a divided power ring and let `M` be an `A`-module. In the
trivial square-zero extension `A ⊕ M` (Mathlib's `TrivSqZeroExt A M`) the
ideal `I ⊕ M` carries the divided powers
`δ₀(x + z) = 1` and `δₙ(x + z) = γₙ(x) + γₙ₋₁(x) z` for `n ≥ 1`,
which extend `γ`. The inclusion `A → A ⊕ M` is then a divided power morphism.
This is the basic input for divided power derivations and the universal
property of the module of divided power differentials `Ω_{B,δ}`.

Mathlib's `DividedPowers.OfSquareZero.dividedPowers` is a different
construction: it puts the divided powers `x ↦ xⁿ / n!` on an ideal of square
zero, whereas here a given `γ` is extended across a square-zero module.

## Main definitions

* `SqZero A M`: the square-zero extension `A ⊕ M`.
* `sqZeroIdeal I M`: the ideal `I ⊕ M`.
* `sqZeroDpow γ M`: the operations `δₙ` above.
* `sqZeroDividedPowers γ M`: `δ` as a divided power structure on `I ⊕ M`.

## Main results

* `sqZeroDpow_add`, `sqZeroDpow_mul`, `sqZeroDpow_mul_dpow`, `sqZeroDpow_comp`:
  the axioms of divided powers for `δ`.
* `sqZero_isDPMorphism`: the inclusion `A → A ⊕ M` is a divided power morphism.

## References

* [Stacks Project, Tag 07HH](https://stacks.math.columbia.edu/tag/07HH)
-/

open scoped TensorProduct
open scoped Simplicial
open scoped CategoryTheory
open DividedPowers

universe u

section SquareZero

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The square-zero extension `A ⊕ M`, in which `M` is an ideal of square zero. -/
abbrev SqZero (A M : Type u) : Type u :=
  TrivSqZeroExt A M

/-- The ideal `I ⊕ M ⊆ A ⊕ M`, the preimage of `I` under the first projection.
An element lies in it if and only if its first coordinate lies in `I`
(`mem_sqZeroIdeal`). -/
def sqZeroIdeal (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module Aᵐᵒᵖ M]
    [IsCentralScalar A M] : Ideal (SqZero A M) :=
  I.comap (TrivSqZeroExt.fstHom A A M)

theorem mem_sqZeroIdeal (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] (a : SqZero A M) :
    a ∈ sqZeroIdeal I M ↔ a.fst ∈ I := by
  simp [sqZeroIdeal, Ideal.mem_comap]

variable (γ : DividedPowers I) (M : Type u) [AddCommGroup M] [Module A M]
  [Module Aᵐᵒᵖ M] [IsCentralScalar A M]

/-- `dpowPred γ n x` is `γₙ₋₁(x)` for `n ≥ 1` and `0` for `n = 0`: the
coefficient of `z` in `δₙ(x + z)`. Truncated subtraction would give the wrong
value `γ₀(x) z = z` at `n = 0`, where `δ₀(x + z) = 1`. -/
private def dpowPred (n : ℕ) (x : A) : A :=
  if n = 0 then 0 else γ.dpow (n - 1) x

private theorem dpowPred_succ (n : ℕ) (x : A) :
    dpowPred γ (n + 1) x = γ.dpow n x := by
  simp [dpowPred]

/-- The operations `δₙ(x + z) = γₙ(x) + dpowPred γ n x • z` on `A ⊕ M`, that is
`γₙ(x) + γₙ₋₁(x) z` for `n ≥ 1` and `γ₀(x)` for `n = 0`. -/
noncomputable def sqZeroDpow (n : ℕ) (a : SqZero A M) : SqZero A M :=
  TrivSqZeroExt.inl (γ.dpow n a.fst) + TrivSqZeroExt.inr (dpowPred γ n a.fst • a.snd)

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
@[simp] theorem sqZeroDpow_fst (n : ℕ) (a : SqZero A M) :
    (sqZeroDpow γ M n a).fst = γ.dpow n a.fst := by simp [sqZeroDpow]

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
@[simp] theorem sqZeroDpow_snd (n : ℕ) (a : SqZero A M) :
    (sqZeroDpow γ M n a).snd = dpowPred γ n a.fst • a.snd := by simp [sqZeroDpow]

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
/-- The `M`-component of `δₙ₊₁(x + z)` is `γₙ(x) z`. This is the form used to
relate divided power morphisms into `A ⊕ M` to divided power derivations. -/
@[simp] theorem sqZeroDpow_snd_succ (n : ℕ) (a : SqZero A M) :
    (sqZeroDpow γ M (n + 1) a).snd = γ.dpow n a.fst • a.snd := by
  rw [sqZeroDpow_snd, dpowPred_succ]

theorem sqZeroDpow_null {n : ℕ} {a : SqZero A M}
    (ha : a ∉ sqZeroIdeal I M) : sqZeroDpow γ M n a = 0 := by
  rw [mem_sqZeroIdeal] at ha
  apply TrivSqZeroExt.ext
  · simp [γ.dpow_null ha]
  · rcases eq_or_ne n 0 with h | h
    · simp [sqZeroDpow_snd, dpowPred, h]
    · simp [sqZeroDpow_snd, dpowPred, h, γ.dpow_null ha]

theorem sqZeroDpow_zero {a : SqZero A M} (ha : a ∈ sqZeroIdeal I M) :
    sqZeroDpow γ M 0 a = 1 := by
  rw [mem_sqZeroIdeal] at ha
  apply TrivSqZeroExt.ext
  · simp [γ.dpow_zero ha]
  · simp [dpowPred]

theorem sqZeroDpow_one {a : SqZero A M} (ha : a ∈ sqZeroIdeal I M) :
    sqZeroDpow γ M 1 a = a := by
  rw [mem_sqZeroIdeal] at ha
  apply TrivSqZeroExt.ext
  · simp [γ.dpow_one ha]
  · rw [sqZeroDpow_snd, show (1 : ℕ) = 0 + 1 from rfl, dpowPred_succ, γ.dpow_zero ha, one_smul]

theorem sqZeroDpow_mem {n : ℕ} (hn : n ≠ 0) {a : SqZero A M}
    (ha : a ∈ sqZeroIdeal I M) : sqZeroDpow γ M n a ∈ sqZeroIdeal I M := by
  rw [mem_sqZeroIdeal] at ha ⊢
  simp [γ.dpow_mem hn ha]

/-- For `x ∈ I` and `n ≥ 1`, `x γₙ₋₁(x) = n γₙ(x)`. This is the product formula
`γₘ(x) γₙ(x) = (m + n choose m) γₘ₊ₙ(x)` at `m = 1`; it is used in
`sqZeroDpow_mul`. -/
theorem self_mul_dpow_sub_one {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I) :
    x * γ.dpow (n - 1) x = n * γ.dpow n x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.succ_sub_one]
  have := γ.mul_dpow (m := 1) (n := k) hx
  rw [γ.dpow_one hx, Nat.choose_one_right] at this
  rw [Nat.succ_eq_add_one, Nat.add_comm k 1, this, Nat.cast_add, Nat.cast_one]

open Finset in
/-- The sum formula for `dpowPred`: for `n ≥ 1`,
`∑_{i + j = n} γᵢ(x) dpowPred γ j y = dpowPred γ n (x + y)`. The term with
`j = 0` vanishes, and after reindexing the remaining sum is the sum formula
for `γ` in degree `n - 1`. -/
theorem sum_dpow_dpowPred {n : ℕ} (hn : n ≠ 0) {x y : A}
    (hx : x ∈ I) (hy : y ∈ I) :
    ∑ k ∈ antidiagonal n, γ.dpow k.1 x * dpowPred γ k.2 y = dpowPred γ n (x + y) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.antidiagonal_succ', Finset.sum_cons, dpowPred, if_pos rfl, mul_zero, zero_add,
    Finset.sum_map]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coe_refl,
    Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, id_eq]
  simp_rw [dpowPred_succ]
  rw [← γ.dpow_add hx hy]

open Finset in
/-- The sum formula `δₙ(a + b) = ∑_{i + j = n} δᵢ(a) δⱼ(b)`. The first component
is the sum formula for `γ`. Since `M² = 0`, the `M`-component is a sum of two
terms, each computed by `sum_dpow_dpowPred`. -/
theorem sqZeroDpow_add {n : ℕ} {a b : SqZero A M}
    (ha : a ∈ sqZeroIdeal I M) (hb : b ∈ sqZeroIdeal I M) :
    sqZeroDpow γ M n (a + b) =
      ∑ k ∈ antidiagonal n, sqZeroDpow γ M k.1 a * sqZeroDpow γ M k.2 b := by
  rw [mem_sqZeroIdeal] at ha hb
  apply TrivSqZeroExt.ext
  · simp only [sqZeroDpow_fst, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.fst_mul]
    exact γ.dpow_add ha hb
  · rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp [dpowPred]
    · simp only [sqZeroDpow_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, sqZeroDpow_fst,
        sqZeroDpow_snd, op_smul_eq_smul, smul_add, smul_smul]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
      have hswap : ∑ k ∈ antidiagonal n, γ.dpow k.2 b.fst * dpowPred γ k.1 a.fst
          = ∑ k ∈ antidiagonal n, γ.dpow k.1 b.fst * dpowPred γ k.2 a.fst := by
        have h := Finset.Nat.sum_antidiagonal_swap (n := n)
          (f := fun p ↦ γ.dpow p.1 b.fst * dpowPred γ p.2 a.fst)
        simpa using h
      rw [hswap, sum_dpow_dpowPred γ hn ha hb, sum_dpow_dpowPred γ hn hb ha, add_comm b.fst a.fst,
        add_comm]

/-- The scalar formula `δₙ(c ξ) = cⁿ δₙ(ξ)`. Write `c = (a, w)` and `ξ = (x, z)`,
so that `cⁿ = (aⁿ, n aⁿ⁻¹ w)`. The coefficients of `z` on both sides are
`aⁿ γₙ₋₁(x)`. The coefficient of `w` is `aⁿ⁻¹ x γₙ₋₁(x)` on the left and
`n aⁿ⁻¹ γₙ(x)` on the right; they agree by `self_mul_dpow_sub_one`. -/
theorem sqZeroDpow_mul {n : ℕ} (c : SqZero A M) {ξ : SqZero A M}
    (hξ : ξ ∈ sqZeroIdeal I M) :
    sqZeroDpow γ M n (c * ξ) = c ^ n * sqZeroDpow γ M n ξ := by
  rw [mem_sqZeroIdeal] at hξ
  apply TrivSqZeroExt.ext
  · simp [γ.dpow_mul hξ]
  · rcases n with _ | m
    · simp [sqZeroDpow_snd, dpowPred]
    · simp only [sqZeroDpow_snd, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, op_smul_eq_smul,
        TrivSqZeroExt.snd_pow, TrivSqZeroExt.fst_pow, sqZeroDpow_fst, sqZeroDpow_snd, smul_add,
        smul_smul, Nat.pred_succ, dpowPred_succ]
      rw [γ.dpow_mul hξ, ← Nat.cast_smul_eq_nsmul A, smul_smul, smul_smul]
      have key := self_mul_dpow_sub_one γ (n := m + 1) (Nat.succ_ne_zero m) hξ
      rw [Nat.succ_sub_one] at key
      congr 1
      · congr 1
        ring
      · congr 1
        rw [Nat.cast_add, Nat.cast_one,
          show c.fst ^ m * γ.dpow m ξ.fst * ξ.fst = c.fst ^ m * (γ.dpow m ξ.fst * ξ.fst) from
            by ring,
          mul_comm (γ.dpow m ξ.fst) ξ.fst, key]
        push_cast
        ring

/-- The identity behind the product formula for `δ`:
`γₘ(x) dpowPred γ n x + γₙ(x) dpowPred γ m x =
(m + n choose m) dpowPred γ (m + n) x`. The cases with `m = 0` or `n = 0` follow
from `γ₀(x) = 1`; for `m, n ≥ 1` one combines two instances of the product
formula for `γ` with the symmetry of binomial coefficients and Pascal's rule. -/
theorem dpow_mul_dpowPred_add (m n : ℕ) {x : A} (hx : x ∈ I) :
    γ.dpow m x * dpowPred γ n x + γ.dpow n x * dpowPred γ m x =
      (Nat.choose (m + n) m : A) * dpowPred γ (m + n) x := by
  rcases m with _ | m' <;> rcases n with _ | n'
  · simp [dpowPred]
  · simp [dpowPred, γ.dpow_zero hx]
  · simp [dpowPred, γ.dpow_zero hx]
  · have hmn : m' + 1 + (n' + 1) = (m' + n' + 1) + 1 := by ring
    rw [dpowPred_succ, dpowPred_succ, hmn, dpowPred_succ,
      γ.mul_dpow (n := n') hx, γ.mul_dpow (m := n' + 1) (n := m') hx,
      show m' + 1 + n' = m' + n' + 1 from by ring,
      show n' + 1 + m' = m' + n' + 1 from by ring]
    have hsymm : (m' + n' + 1).choose (n' + 1) = (m' + n' + 1).choose m' := by
      have h : m' + n' + 1 - m' = n' + 1 := by omega
      conv_lhs => rw [← h]
      exact Nat.choose_symm (by omega)
    rw [hsymm]
    have hpascal : (m' + n' + 1).choose m' + (m' + n' + 1).choose (m' + 1)
        = (m' + n' + 1 + 1).choose (m' + 1) := by
      rw [Nat.choose_succ_succ' (m' + n' + 1) m']
    rw [← add_mul, ← Nat.cast_add, add_comm ((m' + n' + 1).choose (m' + 1)), hpascal]

/-- The product formula `δₘ(ξ) δₙ(ξ) = (m + n choose m) δₘ₊ₙ(ξ)`. -/
theorem sqZeroDpow_mul_dpow {m n : ℕ} {ξ : SqZero A M}
    (hξ : ξ ∈ sqZeroIdeal I M) :
    sqZeroDpow γ M m ξ * sqZeroDpow γ M n ξ =
      (Nat.choose (m + n) m : SqZero A M) * sqZeroDpow γ M (m + n) ξ := by
  rw [mem_sqZeroIdeal] at hξ
  apply TrivSqZeroExt.ext
  · simp [γ.mul_dpow hξ]
  · simp only [sqZeroDpow_snd, TrivSqZeroExt.snd_mul, op_smul_eq_smul,
      sqZeroDpow_fst, sqZeroDpow_snd, smul_smul, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero]
    rw [← add_smul, dpow_mul_dpowPred_add γ m n hξ]

/-- The identity behind the composition formula for `δ`: for `n ≥ 1`,
`dpowPred γ m (γₙ(x)) dpowPred γ n x = uniformBell m n · dpowPred γ (m n) x`.
For `m = m' + 1` the composition formula for `γ` turns the left side into
`γₘ'ₙ(x) γₙ₋₁(x)`, the product formula turns this into a binomial coefficient
times `γₘ'ₙ₊ₙ₋₁(x)`, and `Nat.uniformBell_succ_left` identifies the
coefficient with `uniformBell (m' + 1) n`. -/
theorem dpowPred_comp (m n : ℕ) (hn : n ≠ 0) {x : A} (hx : x ∈ I) :
    dpowPred γ m (γ.dpow n x) * dpowPred γ n x =
      (Nat.uniformBell m n : A) * dpowPred γ (m * n) x := by
  rcases m with _ | m'
  · simp [dpowPred, Nat.uniformBell_zero_left]
  · have hmn : (m' + 1) * n = m' * n + n := by ring
    have hRHS : dpowPred γ ((m' + 1) * n) x = γ.dpow (m' * n + (n - 1)) x := by
      rw [dpowPred, if_neg (show (m' + 1) * n ≠ 0 by simp [hn]),
        show (m' + 1) * n - 1 = m' * n + (n - 1) by omega]
    rw [dpowPred_succ, hRHS, dpowPred, if_neg hn,
      γ.dpow_comp hn hx, mul_assoc, γ.mul_dpow hx, Nat.choose_symm_add]
    rw [Nat.uniformBell_succ_left, show m' * n + n - 1 = m' * n + (n - 1) from by omega]
    push_cast
    ring

/-- The composition formula `δₘ(δₙ(ξ)) = uniformBell m n · δₘₙ(ξ)` for `n ≥ 1`.
The first component is the composition formula for `γ`; the `M`-component is
`dpowPred_comp`. -/
theorem sqZeroDpow_comp {m n : ℕ} (hn : n ≠ 0) {ξ : SqZero A M}
    (hξ : ξ ∈ sqZeroIdeal I M) :
    sqZeroDpow γ M m (sqZeroDpow γ M n ξ) =
      (Nat.uniformBell m n : SqZero A M) * sqZeroDpow γ M (m * n) ξ := by
  rw [mem_sqZeroIdeal] at hξ
  apply TrivSqZeroExt.ext
  · simp [sqZeroDpow_fst, γ.dpow_comp hn hξ]
  · simp only [sqZeroDpow_snd, sqZeroDpow_fst, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_smul]
    rw [dpowPred_comp γ m n hn hξ]

/-- **Divided powers on a square-zero extension.** The divided power structure
`δ` on `I ⊕ M ⊆ A ⊕ M` extending `γ`. -/
noncomputable def sqZeroDividedPowers : DividedPowers (sqZeroIdeal I M) where
  dpow := sqZeroDpow γ M
  dpow_null hx := sqZeroDpow_null γ M hx
  dpow_zero hx := sqZeroDpow_zero γ M hx
  dpow_one hx := sqZeroDpow_one γ M hx
  dpow_mem hn hx := sqZeroDpow_mem γ M hn hx
  dpow_add hx hy := sqZeroDpow_add γ M hx hy
  dpow_mul {_n a _x} hx := sqZeroDpow_mul γ M a hx
  mul_dpow hx := sqZeroDpow_mul_dpow γ M hx
  dpow_comp hn hx := sqZeroDpow_comp γ M hn hx

/-- The inclusion `A → A ⊕ M` is a divided power morphism. -/
theorem sqZero_isDPMorphism :
    IsDPMorphism γ (sqZeroDividedPowers γ M) (TrivSqZeroExt.inlHom A M) where
  ideal_comp := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_sqZeroIdeal]
    simpa using ha
  dpow_comp {n} a ha := by
    change sqZeroDpow γ M n (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (γ.dpow n a)
    apply TrivSqZeroExt.ext
    · simp [sqZeroDpow_fst]
    · simp [sqZeroDpow_snd]

end SquareZero
