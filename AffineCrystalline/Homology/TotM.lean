/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Homology.Elementwise
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Pi

/-!
# Total complexes of first-quadrant bicomplexes of modules

A *raw bicomplex* `K : RawBi R` consists of `R`-modules `K.M p q` (`p q : ℕ`)
with horizontal differentials `dh p p' q : M p q ⟶ M p' q` and vertical
differentials `dv p q q' : M p q ⟶ M p q'`.  The differentials are indexed as in
`HomologicalComplex` (they vanish unless the second index is the successor of
the first), square to zero and commute.

The total complex `Tot K` is realized concretely: its degree-`n` term is the
submodule of families `(x_{p,q})` supported on the antidiagonal `p + q = n`, and
the differential is
`(d x)_{p,q} = dh x_{p-1,q} + (-1)^p dv x_{p,q-1}`.
Because the differentials are indexed as in `HomologicalComplex`, no transport
along equalities of indices is needed, and the edge cases `p = 0`, `q = 0` are
handled by the shape axioms.

The main results are the *acyclic assembly lemmas*: a first-quadrant bicomplex
with exact columns, or with exact rows, has acyclic total complex.  Their
augmented forms state that an augmentation `L → K` by a row (resp. column) whose
augmented columns (resp. rows) are exact induces a quasi-isomorphism
`L ⟶ Tot K`.  All proofs are elementwise staircase arguments, based on the
criteria of `AffineCrystalline.Homology.Elementwise`.

## Main definitions

* `AffineCrystalline.Homology.RawBi`: first-quadrant bicomplexes of modules.
* `RawBi.tot`, `RawBi.dRaw`, `RawBi.totComplex`: the total complex, as a complex
  of submodules of the module `RawBi.Fam` of all families.
* `RawBi.ColumnsExact`, `RawBi.RowsExact`: elementwise exactness of all columns,
  resp. all rows, including injectivity in degree `0`.
* `RawBi.augRow`, `RawBi.augRowι`: the bicomplex augmented by a row `L` placed
  in degree `q = 0`, and the induced map `L ⟶ Tot K`.
* `RawBi.transpose`, `RawBi.transposeTotIso`: the transposed bicomplex and the
  sign-twisted isomorphism of total complexes.
* `RawBi.augCol`, `RawBi.augColι`: augmentation by a column, obtained from
  `augRow` by transposition.

## Main results

* `RawBi.exactAt_totComplex_of_columnsExact`: exact columns imply an acyclic
  total complex.
* `RawBi.exactAt_totComplex_of_rowsExact`: exact rows imply an acyclic total
  complex.
* `RawBi.augRowι_quasiIso`: if the columns of the row-augmented bicomplex are
  exact, then `L ⟶ Tot K` is a quasi-isomorphism.
* `RawBi.augColι_quasiIso`: if the rows of the column-augmented bicomplex are
  exact, then `L ⟶ Tot K` is a quasi-isomorphism.

## References

* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG), for the
  use of the double complex lemma.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AffineCrystalline.Homology

variable {R : Type u} [Ring R]

/-- A first-quadrant bicomplex of `R`-modules, with differentials indexed as in
`HomologicalComplex`: `dh p p' q` and `dv p q q'` vanish unless `p' = p + 1`,
resp. `q' = q + 1`. -/
structure RawBi (R : Type u) [Ring R] where
  M : ℕ → ℕ → ModuleCat.{v} R
  dh : ∀ p p' q, M p q ⟶ M p' q
  dv : ∀ p q q', M p q ⟶ M p q'
  dh_shape : ∀ p p' q, p + 1 ≠ p' → dh p p' q = 0
  dv_shape : ∀ p q q', q + 1 ≠ q' → dv p q q' = 0
  dh_dh : ∀ p p' p'' q, dh p p' q ≫ dh p' p'' q = 0
  dv_dv : ∀ p q q' q'', dv p q q' ≫ dv p q' q'' = 0
  comm : ∀ p p' q q', dh p p' q ≫ dv p' q q' = dv p q q' ≫ dh p p' q'

namespace RawBi

variable (K : RawBi.{v} R)

/-- Elementwise form of `RawBi.dh_shape`. -/
theorem dh_shape_apply {p p' q : ℕ} (h : p + 1 ≠ p') (x : K.M p q) :
    (K.dh p p' q).hom x = 0 := by
  rw [K.dh_shape p p' q h]
  rfl

/-- Elementwise form of `RawBi.dv_shape`. -/
theorem dv_shape_apply {p q q' : ℕ} (h : q + 1 ≠ q') (x : K.M p q) :
    (K.dv p q q').hom x = 0 := by
  rw [K.dv_shape p q q' h]
  rfl

/-- Elementwise form of `RawBi.dh_dh`. -/
theorem dh_dh_apply (p p' p'' q : ℕ) (x : K.M p q) :
    (K.dh p' p'' q).hom ((K.dh p p' q).hom x) = 0 := by
  change (K.dh p p' q ≫ K.dh p' p'' q).hom x = 0
  rw [K.dh_dh]
  rfl

/-- Elementwise form of `RawBi.dv_dv`. -/
theorem dv_dv_apply (p q q' q'' : ℕ) (x : K.M p q) :
    (K.dv p q' q'').hom ((K.dv p q q').hom x) = 0 := by
  change (K.dv p q q' ≫ K.dv p q' q'').hom x = 0
  rw [K.dv_dv]
  rfl

/-- Elementwise form of `RawBi.comm`. -/
theorem comm_apply (p p' q q' : ℕ) (x : K.M p q) :
    (K.dv p' q q').hom ((K.dh p p' q).hom x) = (K.dh p p' q').hom ((K.dv p q q').hom x) := by
  change (K.dh p p' q ≫ K.dv p' q q').hom x = (K.dv p q q' ≫ K.dh p p' q').hom x
  rw [K.comm]

/-- The module of all families `(x_{p,q})`, the ambient module of the total
complex. -/
abbrev Fam : Type v := (pq : ℕ × ℕ) → K.M pq.1 pq.2

/-- The total differential on all families:
`(d x)_{p,q} = dh x_{p-1,q} + (-1)^p dv x_{p,q-1}`. -/
def dRaw : K.Fam →ₗ[R] K.Fam :=
  LinearMap.pi fun pq ↦
    (K.dh (pq.1 - 1) pq.1 pq.2).hom ∘ₗ LinearMap.proj (R := R) (φ := fun pq : ℕ × ℕ ↦
      (K.M pq.1 pq.2 : Type v)) (pq.1 - 1, pq.2) +
    ((-1 : ℤ) ^ pq.1) • ((K.dv pq.1 (pq.2 - 1) pq.2).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun pq : ℕ × ℕ ↦ (K.M pq.1 pq.2 : Type v))
        (pq.1, pq.2 - 1))

theorem dRaw_apply (f : K.Fam) (p q : ℕ) :
    K.dRaw f (p, q) = (K.dh (p - 1) p q).hom (f (p - 1, q)) +
      ((-1 : ℤ) ^ p) • (K.dv p (q - 1) q).hom (f (p, q - 1)) :=
  rfl

/-- The total differential squares to zero. -/
theorem dRaw_dRaw (f : K.Fam) : K.dRaw (K.dRaw f) = 0 := by
  funext ⟨p, q⟩
  simp only [dRaw_apply, map_add, map_zsmul, Pi.zero_apply, dh_dh_apply, dv_dv_apply,
    smul_zero, zero_add, add_zero]
  rw [K.comm_apply]
  rcases p with _ | p
  · rw [K.dh_shape_apply (p := 0 - 1) (p' := 0) (by omega)]
    simp
  · simp only [Nat.add_sub_cancel, pow_succ, mul_neg, mul_one, neg_smul, add_neg_cancel]

/-- On the bottom row only the horizontal differential contributes. -/
theorem dRaw_apply_row_zero (f : K.Fam) (p : ℕ) :
    K.dRaw f (p, 0) = (K.dh (p - 1) p 0).hom (f (p - 1, 0)) := by
  rw [dRaw_apply, K.dv_shape_apply (by omega), smul_zero, add_zero]

/-- On the first column only the vertical differential contributes. -/
theorem dRaw_apply_col_zero (f : K.Fam) (q : ℕ) :
    K.dRaw f (0, q) = (K.dv 0 (q - 1) q).hom (f (0, q - 1)) := by
  rw [dRaw_apply, K.dh_shape_apply (by omega), zero_add, pow_zero, one_smul]

/-- The degree-`n` part of the total complex: the families supported on the
antidiagonal `p + q = n`. -/
def tot (n : ℕ) : Submodule R K.Fam where
  carrier := {f | ∀ pq : ℕ × ℕ, pq.1 + pq.2 ≠ n → f pq = 0}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' := by
    intro f g hf hg pq hpq
    simp [hf pq hpq, hg pq hpq]
  smul_mem' := by
    intro r f hf pq hpq
    simp [hf pq hpq]

/-- The total differential raises the total degree by one. -/
theorem dRaw_mem {n : ℕ} {f : K.Fam} (hf : f ∈ K.tot n) : K.dRaw f ∈ K.tot (n + 1) := by
  rintro ⟨p, q⟩ hpq
  rw [dRaw_apply]
  have h1 : (K.dh (p - 1) p q).hom (f (p - 1, q)) = 0 := by
    rcases p with _ | p
    · exact K.dh_shape_apply (by omega) _
    · rw [hf (p + 1 - 1, q) (by simp at hpq ⊢; omega), map_zero]
  have h2 : (K.dv p (q - 1) q).hom (f (p, q - 1)) = 0 := by
    rcases q with _ | q
    · exact K.dv_shape_apply (by omega) _
    · rw [hf (p, q + 1 - 1) (by simp at hpq ⊢; omega), map_zero]
  rw [h1, h2, smul_zero, add_zero]

/-- The total complex of a raw bicomplex, as a cochain complex of
submodules of `RawBi.Fam`. -/
noncomputable def totComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (K.tot n))
    (fun n ↦ ModuleCat.ofHom ((K.dRaw.restrict (p := K.tot n) (q := K.tot (n + 1))
      (fun f hf ↦ K.dRaw_mem hf))))
    (by
      intro n
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun f ↦ Subtype.ext (K.dRaw_dRaw f.1))

/-- The underlying family of an element of the total complex. -/
def val {n : ℕ} (x : K.totComplex.X n) : K.Fam := (show ↥(K.tot n) from x).1

theorem val_mem {n : ℕ} (x : K.totComplex.X n) : K.val x ∈ K.tot n :=
  (show ↥(K.tot n) from x).2

/-- An element of the total complex from a supported family. -/
def ofFam {n : ℕ} (f : K.Fam) (hf : f ∈ K.tot n) : K.totComplex.X n :=
  (show ↥(K.tot n) from ⟨f, hf⟩)

@[simp]
theorem val_ofFam {n : ℕ} (f : K.Fam) (hf : f ∈ K.tot n) : K.val (K.ofFam f hf) = f := rfl

theorem val_injective {n : ℕ} {x y : K.totComplex.X n} (h : K.val x = K.val y) : x = y :=
  Subtype.ext h

@[simp]
theorem val_zero (n : ℕ) : K.val (0 : K.totComplex.X n) = 0 := rfl

theorem totComplex_d_val (n : ℕ) (f : K.totComplex.X n) :
    K.val ((K.totComplex.d n (n + 1)).hom f) = K.dRaw (K.val f) := by
  simp only [totComplex, CochainComplex.of_d]
  rfl

theorem totComplex_d_zero_zero : K.totComplex.d 0 0 = 0 :=
  K.totComplex.shape 0 0 (by simp)

theorem totComplex_d_pred_val (n : ℕ) (hn : 0 < n) (f : K.totComplex.X (n - 1)) :
    K.val ((K.totComplex.d (n - 1) n).hom f) = K.dRaw (K.val f) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact K.totComplex_d_val m f

/-! ## The differential of a single element -/

section Single

/-- The family concentrated in bidegree `(a, b)`. -/
def single (a b : ℕ) (x : K.M a b) : K.Fam :=
  Pi.single (M := fun pq : ℕ × ℕ ↦ (K.M pq.1 pq.2 : Type v)) (a, b) x

theorem single_mem (a b : ℕ) (x : K.M a b) : K.single a b x ∈ K.tot (a + b) := by
  intro pq hpq
  apply Pi.single_eq_of_ne
  rintro rfl
  exact hpq rfl

theorem single_apply_same (a b : ℕ) (x : K.M a b) : K.single a b x (a, b) = x :=
  Pi.single_eq_same (M := fun pq : ℕ × ℕ ↦ (K.M pq.1 pq.2 : Type v)) (a, b) x

theorem single_apply_ne (a b : ℕ) (x : K.M a b) {pq : ℕ × ℕ} (h : pq ≠ (a, b)) :
    K.single a b x pq = 0 :=
  Pi.single_eq_of_ne (M := fun pq : ℕ × ℕ ↦ (K.M pq.1 pq.2 : Type v)) h x

theorem dRaw_single_right (a b : ℕ) (x : K.M a b) :
    K.dRaw (K.single a b x) (a + 1, b) = (K.dh a (a + 1) b).hom x := by
  rw [dRaw_apply]
  change (K.dh a (a + 1) b).hom (K.single a b x (a, b)) +
      ((-1 : ℤ) ^ (a + 1)) • (K.dv (a + 1) (b - 1) b).hom (K.single a b x (a + 1, b - 1)) = _
  rw [K.single_apply_same, K.single_apply_ne _ _ _ (by simp), map_zero, smul_zero, add_zero]

theorem dRaw_single_up (a b : ℕ) (x : K.M a b) :
    K.dRaw (K.single a b x) (a, b + 1) = ((-1 : ℤ) ^ a) • (K.dv a b (b + 1)).hom x := by
  rw [dRaw_apply]
  change (K.dh (a - 1) a (b + 1)).hom (K.single a b x (a - 1, b + 1)) +
      ((-1 : ℤ) ^ a) • (K.dv a b (b + 1)).hom (K.single a b x (a, b)) = _
  rw [K.single_apply_same, K.single_apply_ne _ _ _ (by simp only [ne_eq, Prod.mk.injEq]; omega),
    map_zero, zero_add]

theorem dRaw_single_other (a b : ℕ) (x : K.M a b) (p q : ℕ)
    (h1 : (p, q) ≠ (a + 1, b)) (h2 : (p, q) ≠ (a, b + 1)) :
    K.dRaw (K.single a b x) (p, q) = 0 := by
  rw [dRaw_apply]
  have e1 : (K.dh (p - 1) p q).hom (K.single a b x (p - 1, q)) = 0 := by
    by_cases hc : (p - 1, q) = (a, b)
    · rcases p with _ | p
      · exact K.dh_shape_apply (by omega) _
      · exfalso
        apply h1
        simp only [Prod.mk.injEq] at hc ⊢
        omega
    · rw [K.single_apply_ne _ _ _ hc, map_zero]
  have e2 : (K.dv p (q - 1) q).hom (K.single a b x (p, q - 1)) = 0 := by
    by_cases hc : (p, q - 1) = (a, b)
    · rcases q with _ | q
      · exact K.dv_shape_apply (by omega) _
      · exfalso
        apply h2
        simp only [Prod.mk.injEq] at hc ⊢
        omega
    · rw [K.single_apply_ne _ _ _ hc, map_zero]
  rw [e1, e2, smul_zero, add_zero]

end Single

/-! ## Acyclic assembly: exact columns -/

/-- Every column (fixed `p`) is exact in every degree `q`; in degree `q = 0` this
means that `dv p 0 1` is injective. -/
def ColumnsExact : Prop :=
  ∀ p q (x : K.M p q), (K.dv p q (q + 1)).hom x = 0 →
    ∃ y : K.M p (q - 1), (K.dv p (q - 1) q).hom y = x

/-- Every row (fixed `q`) is exact in every degree `p`; in degree `p = 0` this
means that `dh 0 1 q` is injective. -/
def RowsExact : Prop :=
  ∀ p q (x : K.M p q), (K.dh p (p + 1) q).hom x = 0 →
    ∃ y : K.M (p - 1) q, (K.dh (p - 1) p q).hom y = x

theorem neg_one_pow_smul_eq_zero {M : Type*} [AddCommGroup M] (p : ℕ) {x : M}
    (h : ((-1 : ℤ) ^ p) • x = 0) : x = 0 := by
  have := congrArg (fun y ↦ ((-1 : ℤ) ^ p) • y) h
  simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
    smul_zero] at this
  exact this

theorem neg_one_pow_smul_smul {M : Type*} [AddCommGroup M] (p : ℕ) (x : M) :
    ((-1 : ℤ) ^ p) • ((-1 : ℤ) ^ p) • x = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- The leftmost possibly nonzero column of a cocycle is a vertical cocycle. -/
theorem dv_apply_eq_zero_of_columns_lt {f : K.Fam} (hd : K.dRaw f = 0) {k : ℕ}
    (hsupp : ∀ pq : ℕ × ℕ, pq.1 < k → f pq = 0) (q : ℕ) :
    (K.dv k q (q + 1)).hom (f (k, q)) = 0 := by
  have h0 := congrFun hd (k, q + 1)
  simp only [dRaw_apply, Pi.zero_apply] at h0
  have hleft : (K.dh (k - 1) k (q + 1)).hom (f (k - 1, q + 1)) = 0 := by
    rcases k with _ | k
    · exact K.dh_shape_apply (by omega) _
    · rw [hsupp (k + 1 - 1, q + 1) (by simp), map_zero]
  rw [hleft, zero_add] at h0
  exact neg_one_pow_smul_eq_zero k h0

/-- One step of the staircase argument for exact columns: a cocycle of degree `n + 1`
vanishing in the columns `p < k` can be modified by a coboundary so that it vanishes in the
columns `p < k + 1`. -/
theorem columns_staircase_step (hK : K.ColumnsExact) {n : ℕ} {f : K.Fam}
    (hf : f ∈ K.tot (n + 1)) (hd : K.dRaw f = 0) {k : ℕ}
    (hsupp : ∀ pq : ℕ × ℕ, pq.1 < k → f pq = 0) :
    ∃ g ∈ K.tot n, ∀ pq : ℕ × ℕ, pq.1 < k + 1 → (f - K.dRaw g) pq = 0 := by
  obtain ⟨y, hy⟩ := hK k (n + 1 - k) _ (K.dv_apply_eq_zero_of_columns_lt hd hsupp _)
  rcases Nat.eq_zero_or_pos (n + 1 - k) with hq0 | hqpos
  · -- the column `k` of `f` already vanishes
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rintro ⟨p, q⟩ hp
    rw [map_zero, sub_zero]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
    · exact hsupp (p, q) hp
    · change p = k at hp
      subst hp
      by_cases hq : q = n + 1 - p
      · subst hq
        rw [← hy]
        exact K.dv_shape_apply (by omega) _
      · exact hf (p, q) (by simp only [ne_eq]; omega)
  · refine ⟨K.single k (n + 1 - k - 1) (((-1 : ℤ) ^ k) • y), ?_, ?_⟩
    · have := K.single_mem k (n + 1 - k - 1) (((-1 : ℤ) ^ k) • y)
      rwa [show k + (n + 1 - k - 1) = n by omega] at this
    · rintro ⟨p, q⟩ hp
      rw [Pi.sub_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
      · rw [hsupp (p, q) hp, K.dRaw_single_other _ _ _ _ _
          (by simp only [ne_eq, Prod.mk.injEq]; omega)
          (by simp only [ne_eq, Prod.mk.injEq]; omega), sub_zero]
      · change p = k at hp
        subst hp
        by_cases hq : q = n + 1 - p
        · subst hq
          have key := K.dRaw_single_up p (n + 1 - p - 1) (((-1 : ℤ) ^ p) • y)
          rw [show n + 1 - p - 1 + 1 = n + 1 - p by omega] at key
          rw [key, map_zsmul, neg_one_pow_smul_smul, hy, sub_self]
        · rw [hf (p, q) (by simp only [ne_eq]; omega), K.dRaw_single_other _ _ _ _ _
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
            (by simp only [ne_eq, Prod.mk.injEq]; omega), sub_zero]

/-- The staircase argument for exact columns: a cocycle of positive degree can be
modified by a coboundary so that it vanishes in all columns `p < k`. -/
theorem columns_staircase (hK : K.ColumnsExact) (n : ℕ) (f : K.Fam)
    (hf : f ∈ K.tot (n + 1)) (hd : K.dRaw f = 0) (k : ℕ) :
    ∃ g ∈ K.tot n, ∀ pq : ℕ × ℕ, pq.1 < k → (f - K.dRaw g) pq = 0 := by
  induction k with
  | zero => exact ⟨0, Submodule.zero_mem _, fun pq h ↦ absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨g, hg, hsupp⟩ := ih
    obtain ⟨g', hg', hsupp'⟩ := K.columns_staircase_step hK (sub_mem hf (K.dRaw_mem hg))
      (by rw [map_sub, hd, K.dRaw_dRaw, sub_zero]) hsupp
    refine ⟨g + g', add_mem hg hg', fun pq hpq ↦ ?_⟩
    rw [map_add, ← sub_sub]
    exact hsupp' pq hpq

/-- The total complex is exact as soon as every degree-zero cocycle vanishes and
every cocycle of positive degree is a coboundary, stated on families. -/
theorem exactAt_totComplex_of_raw
    (H0 : ∀ f ∈ K.tot 0, K.dRaw f = 0 → f = 0)
    (H : ∀ n (f : K.Fam), f ∈ K.tot (n + 1) → K.dRaw f = 0 → ∃ g ∈ K.tot n, K.dRaw g = f)
    (n : ℕ) : K.totComplex.ExactAt n := by
  rw [exactAt_iff_elementwise]
  intro x hx
  have hx' : K.dRaw (K.val x) = 0 := by
    have := congrArg K.val hx
    rw [totComplex_d_val] at this
    exact this
  rcases n with _ | n
  · refine ⟨0, ?_⟩
    rw [map_zero]
    apply K.val_injective
    exact (H0 _ (K.val_mem x) hx').symm
  · obtain ⟨g, hg, hgf⟩ := H n (K.val x) (K.val_mem x) hx'
    refine ⟨K.ofFam g hg, ?_⟩
    apply K.val_injective
    rw [K.totComplex_d_pred_val (n + 1) (by omega), val_ofFam, hgf]

/-- With exact columns, every cocycle of positive degree is a coboundary. -/
theorem exists_dRaw_eq_of_columnsExact (hK : K.ColumnsExact) (n : ℕ) (f : K.Fam)
    (hf : f ∈ K.tot (n + 1)) (hd : K.dRaw f = 0) : ∃ g ∈ K.tot n, K.dRaw g = f := by
  obtain ⟨g, hg, hsupp⟩ := K.columns_staircase hK n f hf hd (n + 2)
  refine ⟨g, hg, ?_⟩
  funext pq
  by_cases hpq : pq.1 < n + 2
  · exact (sub_eq_zero.1 (hsupp pq hpq)).symm
  · rw [hf pq (by omega), K.dRaw_mem hg pq (by omega)]

/-- With exact columns, every degree-zero cocycle vanishes. -/
theorem eq_zero_of_columnsExact_of_mem_tot_zero (hK : K.ColumnsExact) (f : K.Fam) (hf : f ∈ K.tot 0)
    (hd : K.dRaw f = 0) : f = 0 := by
  funext ⟨p, q⟩
  by_cases hpq : p + q = 0
  · obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    have h0 := congrArg (fun F ↦ F (0, 1)) hd
    simp only [dRaw_apply, Pi.zero_apply] at h0
    rw [K.dh_shape_apply (by omega), zero_add, pow_zero, one_smul] at h0
    obtain ⟨y, hy⟩ := hK 0 0 _ h0
    rw [← hy]
    exact K.dv_shape_apply (by omega) _
  · exact hf (p, q) hpq

/-- **Acyclic assembly (columns).** A first-quadrant bicomplex with exact
columns has an acyclic total complex. -/
theorem exactAt_totComplex_of_columnsExact (hK : K.ColumnsExact) (n : ℕ) :
    K.totComplex.ExactAt n :=
  K.exactAt_totComplex_of_raw (K.eq_zero_of_columnsExact_of_mem_tot_zero hK)
    (K.exists_dRaw_eq_of_columnsExact hK) n

/-- The lowest possibly nonzero row of a cocycle is a horizontal cocycle. -/
theorem dh_apply_eq_zero_of_rows_lt {f : K.Fam} (hd : K.dRaw f = 0) {k : ℕ}
    (hsupp : ∀ pq : ℕ × ℕ, pq.2 < k → f pq = 0) (p : ℕ) :
    (K.dh p (p + 1) k).hom (f (p, k)) = 0 := by
  have h0 := congrFun hd (p + 1, k)
  simp only [dRaw_apply, Pi.zero_apply] at h0
  have hright : (K.dv (p + 1) (k - 1) k).hom (f (p + 1, k - 1)) = 0 := by
    rcases k with _ | k
    · exact K.dv_shape_apply (by omega) _
    · rw [hsupp (p + 1, k + 1 - 1) (by simp), map_zero]
  rw [hright, smul_zero, add_zero] at h0
  exact h0

/-- One step of the staircase argument for exact rows: a cocycle of degree `n + 1` vanishing
in the rows `q < k` can be modified by a coboundary so that it vanishes in the rows
`q < k + 1`. -/
theorem rows_staircase_step (hK : K.RowsExact) {n : ℕ} {f : K.Fam}
    (hf : f ∈ K.tot (n + 1)) (hd : K.dRaw f = 0) {k : ℕ}
    (hsupp : ∀ pq : ℕ × ℕ, pq.2 < k → f pq = 0) :
    ∃ g ∈ K.tot n, ∀ pq : ℕ × ℕ, pq.2 < k + 1 → (f - K.dRaw g) pq = 0 := by
  obtain ⟨y, hy⟩ := hK (n + 1 - k) k _ (K.dh_apply_eq_zero_of_rows_lt hd hsupp _)
  rcases Nat.eq_zero_or_pos (n + 1 - k) with hp0 | hppos
  · -- the row `k` of `f` already vanishes
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rintro ⟨p, q⟩ hq
    rw [map_zero, sub_zero]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
    · exact hsupp (p, q) hq
    · change q = k at hq
      subst hq
      by_cases hp : p = n + 1 - q
      · subst hp
        rw [← hy]
        exact K.dh_shape_apply (by omega) _
      · exact hf (p, q) (by simp only [ne_eq]; omega)
  · refine ⟨K.single (n + 1 - k - 1) k y, ?_, ?_⟩
    · have := K.single_mem (n + 1 - k - 1) k y
      rwa [show n + 1 - k - 1 + k = n by omega] at this
    · rintro ⟨p, q⟩ hq
      rw [Pi.sub_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · rw [hsupp (p, q) hq, K.dRaw_single_other _ _ _ _ _
          (by simp only [ne_eq, Prod.mk.injEq]; omega)
          (by simp only [ne_eq, Prod.mk.injEq]; omega), sub_zero]
      · change q = k at hq
        subst hq
        by_cases hp : p = n + 1 - q
        · subst hp
          have key := K.dRaw_single_right (n + 1 - q - 1) q y
          rw [show n + 1 - q - 1 + 1 = n + 1 - q by omega] at key
          rw [key, hy, sub_self]
        · rw [hf (p, q) (by simp only [ne_eq]; omega), K.dRaw_single_other _ _ _ _ _
            (by simp only [ne_eq, Prod.mk.injEq]; omega)
            (by simp only [ne_eq, Prod.mk.injEq]; omega), sub_zero]

/-- The staircase argument for exact rows: a cocycle of positive degree can be
modified by a coboundary so that it vanishes in all rows `q < k`. -/
theorem rows_staircase (hK : K.RowsExact) (n : ℕ) (f : K.Fam)
    (hf : f ∈ K.tot (n + 1)) (hd : K.dRaw f = 0) (k : ℕ) :
    ∃ g ∈ K.tot n, ∀ pq : ℕ × ℕ, pq.2 < k → (f - K.dRaw g) pq = 0 := by
  induction k with
  | zero => exact ⟨0, Submodule.zero_mem _, fun pq h ↦ absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨g, hg, hsupp⟩ := ih
    obtain ⟨g', hg', hsupp'⟩ := K.rows_staircase_step hK (sub_mem hf (K.dRaw_mem hg))
      (by rw [map_sub, hd, K.dRaw_dRaw, sub_zero]) hsupp
    refine ⟨g + g', add_mem hg hg', fun pq hpq ↦ ?_⟩
    rw [map_add, ← sub_sub]
    exact hsupp' pq hpq

/-- With exact rows, every cocycle of positive degree is a coboundary. -/
theorem exists_dRaw_eq_of_rowsExact (hK : K.RowsExact) (n : ℕ) (f : K.Fam)
    (hf : f ∈ K.tot (n + 1)) (hd : K.dRaw f = 0) : ∃ g ∈ K.tot n, K.dRaw g = f := by
  obtain ⟨g, hg, hsupp⟩ := K.rows_staircase hK n f hf hd (n + 2)
  refine ⟨g, hg, ?_⟩
  funext pq
  by_cases hpq : pq.2 < n + 2
  · exact (sub_eq_zero.1 (hsupp pq hpq)).symm
  · rw [hf pq (by omega), K.dRaw_mem hg pq (by omega)]

/-- With exact rows, every degree-zero cocycle vanishes. -/
theorem eq_zero_of_rowsExact_of_mem_tot_zero (hK : K.RowsExact) (f : K.Fam) (hf : f ∈ K.tot 0)
    (hd : K.dRaw f = 0) : f = 0 := by
  funext ⟨p, q⟩
  by_cases hpq : p + q = 0
  · obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    have h0 := congrArg (fun F ↦ F (1, 0)) hd
    simp only [dRaw_apply, Pi.zero_apply] at h0
    rw [K.dv_shape_apply (p := 1) (q := 0 - 1) (q' := 0) (by omega), smul_zero,
      add_zero] at h0
    obtain ⟨y, hy⟩ := hK 0 0 _ h0
    rw [← hy]
    exact K.dh_shape_apply (by omega) _
  · exact hf (p, q) hpq

/-- **Acyclic assembly (rows).** A first-quadrant bicomplex with exact rows has
an acyclic total complex. -/
theorem exactAt_totComplex_of_rowsExact (hK : K.RowsExact) (n : ℕ) :
    K.totComplex.ExactAt n :=
  K.exactAt_totComplex_of_raw (K.eq_zero_of_rowsExact_of_mem_tot_zero hK)
    (K.exists_dRaw_eq_of_rowsExact hK) n

/-! ## Augmentation by a row -/

section AugRow

variable (L : CochainComplex (ModuleCat.{v} R) ℕ) (η : ∀ p, L.X p ⟶ K.M p 0)

/-- The modules of the bicomplex augmented by the row `L` placed in degree
`q = 0` (the original rows are shifted up by one). -/
@[reducible] def augRowM : ℕ → ℕ → ModuleCat.{v} R
  | p, 0 => L.X p
  | p, q + 1 => K.M p q

/-- Horizontal differentials of the row-augmented bicomplex. -/
def augRowDh : ∀ p p' q, K.augRowM L p q ⟶ K.augRowM L p' q
  | p, p', 0 => L.d p p'
  | p, p', q + 1 => K.dh p p' q

/-- Vertical differentials of the row-augmented bicomplex. -/
def augRowDv : ∀ p q q', K.augRowM L p q ⟶ K.augRowM L p q'
  | p, 0, 1 => η p
  | p, q + 1, q' + 1 => K.dv p q q'
  | _, _, _ => 0

@[simp] theorem augRowDh_zero (p p' : ℕ) : K.augRowDh L p p' 0 = L.d p p' := rfl
@[simp] theorem augRowDh_succ (p p' q : ℕ) : K.augRowDh L p p' (q + 1) = K.dh p p' q := rfl
@[simp] theorem augRowDv_zero_one (p : ℕ) : K.augRowDv L η p 0 1 = η p := rfl
@[simp] theorem augRowDv_succ_succ (p q q' : ℕ) :
    K.augRowDv L η p (q + 1) (q' + 1) = K.dv p q q' := rfl
@[simp] theorem augRowDv_zero_zero (p : ℕ) : K.augRowDv L η p 0 0 = 0 := rfl
@[simp] theorem augRowDv_zero_add_two (p q' : ℕ) : K.augRowDv L η p 0 (q' + 2) = 0 := rfl
@[simp] theorem augRowDv_succ_zero (p q : ℕ) : K.augRowDv L η p (q + 1) 0 = 0 := rfl

/-- The vertical differentials of the row-augmented bicomplex vanish unless `q' = q + 1`. -/
theorem augRowDv_shape (p q q' : ℕ) (h : q + 1 ≠ q') : K.augRowDv L η p q q' = 0 := by
  rcases q with _ | q <;> rcases q' with _ | _ | q'
  · rfl
  · exact absurd rfl h
  · rfl
  · rfl
  · exact K.dv_shape p (q + 1 - 1) 0 (by omega)
  · exact K.dv_shape p q (q' + 1) (by omega)

/-- The vertical differentials of the row-augmented bicomplex square to zero, provided
`η p ≫ dv p 0 1 = 0`. -/
theorem augRowDv_comp_augRowDv (hη0 : ∀ p, η p ≫ K.dv p 0 1 = 0) (p q q' q'' : ℕ) :
    K.augRowDv L η p q q' ≫ K.augRowDv L η p q' q'' = 0 := by
  rcases q with _ | q
  · rcases q' with _ | _ | q'
    · exact zero_comp
    · rcases q'' with _ | q''
      · exact comp_zero
      · by_cases h1 : q'' = 1
        · subst h1
          exact hη0 p
        · change η p ≫ K.dv p 0 q'' = 0
          rw [K.dv_shape p 0 q'' (by omega), comp_zero]
    · exact zero_comp
  · rcases q' with _ | q'
    · exact zero_comp
    · rcases q'' with _ | q''
      · exact comp_zero
      · exact K.dv_dv p q q' q''

/-- The horizontal and vertical differentials of the row-augmented bicomplex commute,
provided `η` commutes with the horizontal differentials. -/
theorem augRowDh_comp_augRowDv (hη : ∀ p p', L.d p p' ≫ η p' = η p ≫ K.dh p p' 0)
    (p p' q q' : ℕ) :
    K.augRowDh L p p' q ≫ K.augRowDv L η p' q q' =
      K.augRowDv L η p q q' ≫ K.augRowDh L p p' q' := by
  rcases q with _ | q <;> rcases q' with _ | _ | q'
  all_goals first
    | exact hη p p'
    | exact K.comm p p' _ _
    | exact comp_zero.trans zero_comp.symm

variable (hη : ∀ p p', L.d p p' ≫ η p' = η p ≫ K.dh p p' 0)
  (hη0 : ∀ p, η p ≫ K.dv p 0 1 = 0)

include hη hη0 in
/-- The bicomplex augmented by the row `L`, via the maps `η p : L^p ⟶ K(p,0)`,
assumed compatible with the horizontal differentials (`hη`) and killed by the
vertical differential (`hη0`). -/
@[reducible] def augRow : RawBi.{v} R where
  M := K.augRowM L
  dh := K.augRowDh L
  dv := K.augRowDv L η
  dh_shape p p' q h := by
    cases q with
    | zero => exact L.shape p p' (by simpa using h)
    | succ q => exact K.dh_shape p p' q h
  dv_shape := K.augRowDv_shape L η
  dh_dh p p' p'' q := by
    cases q with
    | zero => exact L.d_comp_d p p' p''
    | succ q => exact K.dh_dh p p' p'' q
  dv_dv := K.augRowDv_comp_augRowDv L η hη0
  comm := K.augRowDh_comp_augRowDv L η hη

/-- The family of the row-augmented bicomplex obtained by shifting a family of
`K` up by one row. -/
def augRowLiftAux (k : K.Fam) (p : ℕ) : ∀ q, K.augRowM L p q
  | 0 => 0
  | q + 1 => k (p, q)

local notation "Kp" => RawBi.augRow K L η hη hη0

/-- Shift a family of `K` up into the augmented bicomplex. -/
def augRowLift (k : K.Fam) : (Kp).Fam := fun pq ↦ K.augRowLiftAux L k pq.1 pq.2

/-- Forget the augmentation row, shifting the remaining rows down by one. -/
def augRowTail (F : (Kp).Fam) : K.Fam := fun pq ↦ F (pq.1, pq.2 + 1)

@[simp] theorem augRowTail_augRowLift (k : K.Fam) :
    K.augRowTail L η hη hη0 (K.augRowLift L η hη hη0 k) = k := rfl

theorem augRowTail_mem {n : ℕ} {F : (Kp).Fam} (hF : F ∈ (Kp).tot n) :
    K.augRowTail L η hη hη0 F ∈ K.tot (n - 1) := by
  rintro ⟨p, q⟩ h
  exact hF (p, q + 1) (by simp only [ne_eq] at h ⊢; omega)

theorem augRowLift_mem {n : ℕ} {k : K.Fam} (hk : k ∈ K.tot n) :
    K.augRowLift L η hη hη0 k ∈ (Kp).tot (n + 1) := by
  rintro ⟨p, q⟩ h
  rcases q with _ | q
  · rfl
  · exact hk (p, q) (by simp only [ne_eq] at h ⊢; omega)

/-- A family of the augmented bicomplex concentrated in bidegree `(n, 0)`, i.e.
in the augmentation row. -/
def augRowSingle (n : ℕ) (l : L.X n) : (Kp).Fam := (Kp).single n 0 l

theorem augRowSingle_same (n : ℕ) (l : L.X n) :
    K.augRowSingle L η hη hη0 n l (n, 0) = l :=
  (Kp).single_apply_same n 0 l

theorem augRowSingle_ne (n : ℕ) (l : L.X n) {pq : ℕ × ℕ} (h : pq ≠ (n, 0)) :
    K.augRowSingle L η hη hη0 n l pq = 0 :=
  (Kp).single_apply_ne n 0 l h

theorem augRowSingle_mem (n : ℕ) (l : L.X n) :
    K.augRowSingle L η hη hη0 n l ∈ (Kp).tot n :=
  (Kp).single_mem n 0 l

theorem augRow_dRaw_zero (F : (Kp).Fam) (p : ℕ) :
    (Kp).dRaw F (p, 0) = (L.d (p - 1) p).hom (F (p - 1, 0)) := by
  rw [dRaw_apply]
  change (L.d (p - 1) p).hom (F (p - 1, 0)) +
    ((-1 : ℤ) ^ p) • (0 : L.X p ⟶ L.X p).hom (F (p, 0)) = _
  rw [show ((0 : L.X p ⟶ L.X p).hom (F (p, 0)) : L.X p) = 0 from rfl, smul_zero, add_zero]

theorem augRow_dRaw_one (F : (Kp).Fam) (p : ℕ) :
    (Kp).dRaw F (p, 1) = K.dRaw (K.augRowTail L η hη hη0 F) (p, 0) +
      ((-1 : ℤ) ^ p) • (η p).hom (F (p, 0)) := by
  rw [K.dRaw_apply_row_zero]
  rfl

theorem augRow_dRaw_succ_succ (F : (Kp).Fam) (p q : ℕ) :
    (Kp).dRaw F (p, q + 2) = K.dRaw (K.augRowTail L η hη hη0 F) (p, q + 1) :=
  rfl

include hη hη0 in
/-- The total differential of `η i l`, placed in bidegree `(i, 0)`, is `η (i + 1) (d l)`,
placed in bidegree `(i + 1, 0)`. -/
theorem dRaw_single_η (i : ℕ) (l : L.X i) :
    K.dRaw (K.single i 0 ((η i).hom l)) =
      K.single (i + 1) 0 ((η (i + 1)).hom ((L.d i (i + 1)).hom l)) := by
  funext ⟨p, q⟩
  by_cases h1 : (p, q) = (i + 1, 0)
  · simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rw [K.dRaw_single_right, K.single_apply_same]
    change (η i ≫ K.dh i (i + 1) 0).hom l = (L.d i (i + 1) ≫ η (i + 1)).hom l
    rw [hη]
  · by_cases h2 : (p, q) = (i, 0 + 1)
    · simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [K.dRaw_single_up, K.single_apply_ne _ _ _ (by simp)]
      change ((-1 : ℤ) ^ p) • (η p ≫ K.dv p 0 1).hom l = 0
      rw [hη0, ModuleCat.hom_zero, LinearMap.zero_apply, smul_zero]
    · rw [K.dRaw_single_other _ _ _ _ _ h1 h2, K.single_apply_ne _ _ _ h1]

/-- The augmentation map `L ⟶ Tot K`, sending `l ∈ L^n` to `η n l` placed in
bidegree `(n, 0)`. -/
noncomputable def augRowι : L ⟶ K.totComplex where
  f n := ModuleCat.ofHom
    { toFun := fun l ↦ K.ofFam (K.single n 0 ((η n).hom l)) (K.single_mem n 0 _)
      map_add' := by
        intro a b
        apply K.val_injective
        simp only [val_ofFam, map_add, single]
        change _ = Pi.single _ _ + Pi.single _ _
        rw [Pi.single_add]
      map_smul' := by
        intro r a
        apply K.val_injective
        simp only [val_ofFam, map_smul, single, RingHom.id_apply]
        change _ = r • Pi.single _ _
        rw [Pi.single_smul] }
  comm' := by
    rintro i _ rfl
    apply ModuleCat.hom_ext
    ext l
    apply K.val_injective
    change K.val ((K.totComplex.d i (i + 1)).hom (K.ofFam (K.single i 0 ((η i).hom l))
        (K.single_mem i 0 _))) = K.single (i + 1) 0 ((η (i + 1)).hom ((L.d i (i + 1)).hom l))
    rw [totComplex_d_val, val_ofFam, K.dRaw_single_η L η hη hη0]

theorem augRowι_val (n : ℕ) (l : L.X n) :
    K.val (((K.augRowι L η hη hη0).f n).hom l) = K.single n 0 ((η n).hom l) := rfl

/-- The shift of a cocycle of `K` into the row-augmented bicomplex is a cocycle. -/
theorem augRow_dRaw_augRowLift {k : K.Fam} (hk : K.dRaw k = 0) :
    (Kp).dRaw (K.augRowLift L η hη hη0 k) = 0 := by
  funext ⟨p, q⟩
  rcases q with _ | _ | q
  · rw [augRow_dRaw_zero]
    change (L.d (p - 1) p).hom 0 = 0
    exact map_zero _
  · rw [augRow_dRaw_one]
    change K.dRaw k (p, 0) + ((-1 : ℤ) ^ p) • (η p).hom 0 = 0
    rw [hk, map_zero, smul_zero, Pi.zero_apply, add_zero]
  · rw [augRow_dRaw_succ_succ]
    change K.dRaw k (p, q + 1) = 0
    rw [hk]
    rfl

/-- If a family `G` of degree `n` of the row-augmented bicomplex has as coboundary the shift
of `k`, then `k` is the coboundary of the shifted rows of `G` plus the image under `η` of
`(-1)^n G(n, 0)`, placed in bidegree `(n, 0)`. -/
theorem eq_dRaw_augRowTail_add_single {n : ℕ} {k : K.Fam} {G : (Kp).Fam}
    (hG : G ∈ (Kp).tot n) (hGF : (Kp).dRaw G = K.augRowLift L η hη hη0 k) :
    k = K.dRaw (K.augRowTail L η hη hη0 G) +
      K.single n 0 (((-1 : ℤ) ^ n) • (η n).hom (G (n, 0))) := by
  funext ⟨p, q⟩
  have h := congrFun hGF (p, q + 1)
  rcases q with _ | q
  · rw [augRow_dRaw_one] at h
    rw [Pi.add_apply]
    change K.augRowLift L η hη hη0 k (p, 0 + 1) = _
    rw [← h]
    congr 1
    by_cases hp : p = n
    · subst hp
      rw [K.single_apply_same]
    · rw [K.single_apply_ne _ _ _ (by simp [hp]), hG (p, 0) (by simp [hp])]
      exact (congrArg (fun t ↦ ((-1 : ℤ) ^ p) • t) (map_zero (η p).hom)).trans (smul_zero _)
  · rw [augRow_dRaw_succ_succ] at h
    rw [Pi.add_apply, K.single_apply_ne _ _ _ (by simp), add_zero]
    exact h.symm

/-- Surjectivity of `augRowι` on cohomology, in elementwise form. -/
theorem augRowι_elementwise_surj (hex : (Kp).ColumnsExact) (n : ℕ) (y : K.totComplex.X n)
    (hy : (K.totComplex.d n (n + 1)).hom y = 0) :
    ∃ x : L.X n, (L.d n (n + 1)).hom x = 0 ∧
      ∃ z : K.totComplex.X (n - 1),
        ((K.augRowι L η hη hη0).f n).hom x = y + (K.totComplex.d (n - 1) n).hom z := by
  have hk : K.dRaw (K.val y) = 0 := by
    rw [← totComplex_d_val, hy, val_zero]
  obtain ⟨G, hG, hGF⟩ := (Kp).exists_dRaw_eq_of_columnsExact hex n _
    (K.augRowLift_mem L η hη hη0 (K.val_mem y)) (K.augRow_dRaw_augRowLift L η hη hη0 hk)
  let l : L.X n := G (n, 0)
  have hl : (L.d n (n + 1)).hom l = 0 := by
    have h := congrFun hGF (n + 1, 0)
    rw [augRow_dRaw_zero] at h
    exact h
  have hkey := K.eq_dRaw_augRowTail_add_single L η hη hη0 hG hGF
  refine ⟨((-1 : ℤ) ^ n) • l, by rw [map_zsmul, hl, smul_zero], ?_⟩
  refine ⟨K.ofFam (-(K.augRowTail L η hη hη0 G))
    (Submodule.neg_mem _ (K.augRowTail_mem L η hη hη0 hG)), K.val_injective ?_⟩
  rw [augRowι_val, map_zsmul]
  rcases n with _ | n
  · have h0 : K.augRowTail L η hη hη0 G = 0 := by
      funext ⟨p, q⟩
      exact hG (p, q + 1) (by simp)
    rw [K.totComplex_d_zero_zero]
    change _ = K.val y + 0
    rw [add_zero, hkey, h0, map_zero, zero_add]
  · change _ = K.val y + K.val ((K.totComplex.d n (n + 1)).hom _)
    rw [totComplex_d_val, val_ofFam, map_neg, hkey]
    abel

/-- In degree `0`, a cocycle `x` of `L` with `η 0 x = 0` vanishes, provided the columns of the
row-augmented bicomplex are exact. -/
theorem eq_zero_of_augRow_columnsExact (hex : (Kp).ColumnsExact) (x : L.X 0)
    (hx : (L.d 0 1).hom x = 0) (hηx : (η 0).hom x = 0) : x = 0 := by
  have hFd : (Kp).dRaw ((Kp).single 0 0 x) = 0 := by
    funext ⟨p, q⟩
    by_cases h1 : (p, q) = (0 + 1, 0)
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ((Kp).dRaw_single_right 0 0 x).trans hx
    · by_cases h2 : (p, q) = (0, 0 + 1)
      · simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        refine ((Kp).dRaw_single_up 0 0 x).trans ?_
        change ((-1 : ℤ) ^ 0) • (η 0).hom x = 0
        rw [hηx, smul_zero]
      · exact (Kp).dRaw_single_other _ _ _ _ _ h1 h2
  have hF0 := (Kp).eq_zero_of_columnsExact_of_mem_tot_zero hex _ ((Kp).single_mem 0 0 x) hFd
  exact ((Kp).single_apply_same 0 0 x).symm.trans (congrFun hF0 (0, 0))

/-- Given a cocycle `x ∈ L^{m+1}` whose image under `η`, placed in bidegree `(m + 1, 0)`, is
the coboundary of `z`, the family with augmentation-row entry `x` and shifted rows
`-(-1)^{m+1} z` is a cocycle of the row-augmented bicomplex. -/
theorem augRow_dRaw_augRowSingle_add_augRowLift {m : ℕ} (x : L.X (m + 1))
    (hx : (L.d (m + 1) (m + 2)).hom x = 0) (z : K.Fam)
    (hz : K.single (m + 1) 0 ((η (m + 1)).hom x) = K.dRaw z) :
    (Kp).dRaw (K.augRowSingle L η hη hη0 (m + 1) x +
      K.augRowLift L η hη hη0 ((-((-1 : ℤ) ^ (m + 1))) • z)) = 0 := by
  have htail : K.augRowTail L η hη hη0 (K.augRowSingle L η hη hη0 (m + 1) x +
      K.augRowLift L η hη hη0 ((-((-1 : ℤ) ^ (m + 1))) • z)) = (-((-1 : ℤ) ^ (m + 1))) • z := by
    funext ⟨p, q⟩
    change K.augRowSingle L η hη hη0 (m + 1) x (p, q + 1) +
      K.augRowLift L η hη hη0 ((-((-1 : ℤ) ^ (m + 1))) • z) (p, q + 1) = _
    rw [K.augRowSingle_ne L η hη hη0 (m + 1) x (by simp), zero_add]
    rfl
  funext ⟨p, q⟩
  rcases q with _ | _ | q
  · rw [augRow_dRaw_zero]
    change (L.d (p - 1) p).hom (K.augRowSingle L η hη hη0 (m + 1) x (p - 1, 0) + 0) = 0
    rw [add_zero]
    by_cases hp : p = m + 2
    · subst hp
      exact (congrArg (L.d (m + 1) (m + 2)).hom
        (K.augRowSingle_same L η hη hη0 (m + 1) x)).trans hx
    · rw [K.augRowSingle_ne L η hη hη0 (m + 1) x
        (by simp only [ne_eq, Prod.mk.injEq]; omega), map_zero]
  · rw [augRow_dRaw_one, htail, map_zsmul, Pi.smul_apply, ← hz]
    change _ + ((-1 : ℤ) ^ p) • (η p).hom (K.augRowSingle L η hη hη0 (m + 1) x (p, 0) + 0) = 0
    rw [add_zero]
    by_cases hp : p = m + 1
    · subst hp
      rw [K.single_apply_same, K.augRowSingle_same, neg_smul, neg_add_cancel]
    · rw [K.single_apply_ne _ _ _ (by simp [hp]),
        K.augRowSingle_ne L η hη hη0 (m + 1) x (by simp [hp]), smul_zero, map_zero, smul_zero,
        add_zero]
  · rw [augRow_dRaw_succ_succ, htail, map_zsmul, Pi.smul_apply, ← hz,
      K.single_apply_ne _ _ _ (by simp), smul_zero]
    rfl

/-- Injectivity of `augRowι` on cohomology, in elementwise form. -/
theorem augRowι_elementwise_inj (hex : (Kp).ColumnsExact) (n : ℕ) (x : L.X n)
    (hx : (L.d n (n + 1)).hom x = 0) (z : K.totComplex.X (n - 1))
    (hz : ((K.augRowι L η hη hη0).f n).hom x = (K.totComplex.d (n - 1) n).hom z) :
    ∃ w : L.X (n - 1), (L.d (n - 1) n).hom w = x := by
  rcases n with _ | m
  · refine ⟨0, ?_⟩
    rw [map_zero]
    refine (K.eq_zero_of_augRow_columnsExact L η hη hη0 hex x hx ?_).symm
    have h := congrFun (congrArg K.val hz) (0, 0)
    rw [augRowι_val, K.single_apply_same, K.totComplex_d_zero_zero] at h
    exact h
  · have hz' : K.single (m + 1) 0 ((η (m + 1)).hom x) = K.dRaw (K.val z) := by
      have h := congrArg K.val hz
      rw [augRowι_val, K.totComplex_d_pred_val (m + 1) (by omega)] at h
      exact h
    obtain ⟨G, hG, hGF⟩ := (Kp).exists_dRaw_eq_of_columnsExact hex m _
      (Submodule.add_mem _ (K.augRowSingle_mem L η hη hη0 (m + 1) x)
        (K.augRowLift_mem L η hη hη0 (zsmul_mem (K.val_mem z) _)))
      (K.augRow_dRaw_augRowSingle_add_augRowLift L η hη hη0 x hx _ hz')
    refine ⟨G (m, 0), ?_⟩
    have h := congrFun hGF (m + 1, 0)
    rw [augRow_dRaw_zero, Pi.add_apply, K.augRowSingle_same] at h
    exact h.trans (add_zero x)

/-- **Augmented acyclic assembly (columns).** If every column of the bicomplex
augmented by the row `L` is exact, the augmentation `L → Tot K` is a
quasi-isomorphism. -/
theorem augRowι_quasiIso (hex : (Kp).ColumnsExact) : QuasiIso (K.augRowι L η hη hη0) :=
  quasiIso_of_elementwise _ (K.augRowι_elementwise_surj L η hη hη0 hex)
    (K.augRowι_elementwise_inj L η hη hη0 hex)

end AugRow

/-! ## Transposition -/

/-- The transposed bicomplex (rows and columns exchanged). -/
@[reducible] def transpose : RawBi.{v} R where
  M p q := K.M q p
  dh p p' q := K.dv q p p'
  dv p q q' := K.dh q q' p
  dh_shape p p' q h := K.dv_shape q p p' h
  dv_shape p q q' h := K.dh_shape q q' p h
  dh_dh p p' p'' q := K.dv_dv q p p' p''
  dv_dv p q q' q'' := K.dh_dh q q' q'' p
  comm p p' q q' := (K.comm q q' p p').symm

/-- The sign-twisted transposition of families, `x ↦ ((-1)^{pq} x_{q,p})_{p,q}`. -/
def transposeFam : K.transpose.Fam →ₗ[R] K.Fam where
  toFun x pq := ((-1 : ℤ) ^ (pq.1 * pq.2)) • x (pq.2, pq.1)
  map_add' x y := by
    funext pq
    simp [smul_add]
  map_smul' r x := by
    funext pq
    change ((-1 : ℤ) ^ (pq.1 * pq.2)) • (r • x (pq.2, pq.1)) =
      r • (((-1 : ℤ) ^ (pq.1 * pq.2)) • x (pq.2, pq.1))
    rw [smul_comm]

theorem transposeFam_apply (x : K.transpose.Fam) (p q : ℕ) :
    K.transposeFam x (p, q) = ((-1 : ℤ) ^ (p * q)) • x (q, p) := rfl

theorem transposeFam_mem {n : ℕ} {x : K.transpose.Fam} (hx : x ∈ K.transpose.tot n) :
    K.transposeFam x ∈ K.tot n := by
  rintro ⟨p, q⟩ h
  rw [transposeFam_apply, hx (q, p) (by simp only [ne_eq] at h ⊢; omega), smul_zero]

theorem neg_one_pow_eq_of_even_sub {a b : ℕ} (h : Even (a + b)) :
    ((-1 : ℤ) ^ a) = (-1 : ℤ) ^ b := by
  rcases h with ⟨k, hk⟩
  have : (-1 : ℤ) ^ a * (-1 : ℤ) ^ b = 1 := by
    rw [← pow_add, hk, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hb : (-1 : ℤ) ^ b * (-1 : ℤ) ^ b = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc (-1 : ℤ) ^ a = (-1 : ℤ) ^ a * ((-1 : ℤ) ^ b * (-1 : ℤ) ^ b) := by rw [hb, mul_one]
    _ = ((-1 : ℤ) ^ a * (-1 : ℤ) ^ b) * (-1 : ℤ) ^ b := by ring
    _ = (-1 : ℤ) ^ b := by rw [this, one_mul]

/-- The sign-twisted transposition commutes with the total differentials. -/
theorem transposeFam_dRaw (x : K.transpose.Fam) :
    K.transposeFam (K.transpose.dRaw x) = K.dRaw (K.transposeFam x) := by
  funext ⟨p, q⟩
  rw [transposeFam_apply, dRaw_apply, dRaw_apply, transposeFam_apply, transposeFam_apply]
  change ((-1 : ℤ) ^ (p * q)) • ((K.dv p (q - 1) q).hom (x (q - 1, p)) +
      ((-1 : ℤ) ^ q) • (K.dh (p - 1) p q).hom (x (q, p - 1))) = _
  rw [map_zsmul, map_zsmul, smul_add, smul_smul, add_comm]
  congr 1
  · rcases p with _ | p
    · rw [K.dh_shape_apply (p := 0 - 1) (p' := 0) (by omega), smul_zero, smul_zero]
    · congr 1
      rw [← pow_add]
      apply neg_one_pow_eq_of_even_sub
      simp only [Nat.add_sub_cancel]
      exact ⟨p * q + q, by ring⟩
  · rcases q with _ | q
    · rw [K.dv_shape_apply (q := 0 - 1) (q' := 0) (by omega)]
      simp
    · rw [smul_smul]
      congr 1
      rw [← pow_add]
      simp only [Nat.add_sub_cancel]
      congr 1
      ring

/-- The isomorphism `Tot (Kᵀ) ≅ Tot K` given by the sign-twisted transposition
of families. -/
noncomputable def transposeTotIso : K.transpose.totComplex ≅ K.totComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ LinearEquiv.toModuleIso
      { toFun := fun x ↦ K.ofFam (K.transposeFam (K.transpose.val x))
          (K.transposeFam_mem (K.transpose.val_mem x))
        map_add' := fun x y ↦ K.val_injective (map_add K.transposeFam _ _)
        map_smul' := fun r x ↦ K.val_injective (map_smul K.transposeFam r _)
        invFun := fun x ↦ K.transpose.ofFam (K.transpose.transposeFam (K.val x))
          (K.transpose.transposeFam_mem (K.val_mem x))
        left_inv := fun x ↦ by
          apply K.transpose.val_injective
          funext ⟨p, q⟩
          change ((-1 : ℤ) ^ (p * q)) • ((-1 : ℤ) ^ (q * p)) • K.transpose.val x (p, q) =
            K.transpose.val x (p, q)
          rw [mul_comm q p, neg_one_pow_smul_smul]
        right_inv := fun x ↦ by
          apply K.val_injective
          funext ⟨p, q⟩
          change ((-1 : ℤ) ^ (p * q)) • ((-1 : ℤ) ^ (q * p)) • K.val x (p, q) = K.val x (p, q)
          rw [mul_comm q p, neg_one_pow_smul_smul] })
    (by
      rintro i _ rfl
      apply ModuleCat.hom_ext
      ext x
      apply K.val_injective
      change K.val ((K.totComplex.d i (i + 1)).hom (K.ofFam _ _)) =
        K.transposeFam (K.transpose.val ((K.transpose.totComplex.d i (i + 1)).hom x))
      rw [totComplex_d_val, totComplex_d_val, val_ofFam, transposeFam_dRaw])

theorem transposeTotIso_val (n : ℕ) (x : K.transpose.totComplex.X n) :
    K.val ((K.transposeTotIso.hom.f n).hom x) = K.transposeFam (K.transpose.val x) := rfl

/-! ## Augmentation by a column -/

section AugCol

variable (L : CochainComplex (ModuleCat.{v} R) ℕ) (ε : ∀ q, L.X q ⟶ K.M 0 q)
  (hε : ∀ q q', L.d q q' ≫ ε q' = ε q ≫ K.dv 0 q q')
  (hε0 : ∀ q, ε q ≫ K.dh 0 1 q = 0)

/-- The bicomplex augmented by the column `L` placed in degree `p = 0`,
presented as the transpose of a row augmentation of the transpose. -/
@[reducible] def augCol : RawBi.{v} R :=
  (K.transpose.augRow L ε hε hε0).transpose

/-- The augmentation map `L ⟶ Tot K`, sending `l ∈ L^n` to `ε n l` placed in
bidegree `(0, n)`. -/
noncomputable def augColι : L ⟶ K.totComplex :=
  K.transpose.augRowι L ε hε hε0 ≫ K.transposeTotIso.hom

theorem augColι_val (n : ℕ) (l : L.X n) :
    K.val (((K.augColι L ε hε hε0).f n).hom l) = K.single 0 n ((ε n).hom l) := by
  change K.transposeFam (K.transpose.single n 0 ((ε n).hom l)) = _
  funext ⟨p, q⟩
  rw [transposeFam_apply]
  by_cases h : (p, q) = (0, n)
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [zero_mul, pow_zero, one_smul]
    exact (K.transpose.single_apply_same q 0 _).trans (K.single_apply_same 0 q _).symm
  · rw [K.transpose.single_apply_ne _ _ _ (by simp only [ne_eq, Prod.mk.injEq] at h ⊢; omega),
      K.single_apply_ne _ _ _ h, smul_zero]

/-- **Augmented acyclic assembly (rows).** If every row of the bicomplex
augmented by the column `L` is exact, the augmentation `L → Tot K` is a
quasi-isomorphism. -/
theorem augColι_quasiIso (hex : (K.augCol L ε hε hε0).RowsExact) :
    QuasiIso (K.augColι L ε hε hε0) := by
  have h1 : QuasiIso (K.transpose.augRowι L ε hε hε0) :=
    K.transpose.augRowι_quasiIso L ε hε hε0 (fun p q x hx ↦ hex q p x hx)
  unfold augColι
  infer_instance

end AugCol

end RawBi

end AffineCrystalline.Homology
