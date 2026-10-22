/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Homology.TotQuasiIso

/-!
# Projection of a total complex onto its bottom row

For a first-quadrant bicomplex of modules `K`, the projection

```text
Tot K ⟶ K(•,0),   (x_{p,q}) ↦ x_{n,0}   in degree n,
```

is a morphism of cochain complexes.  It is a quasi-isomorphism as soon as the
total complex of the rows `q ≥ 1` (the bicomplex `K.rowShift`) is acyclic.
Indeed, the projection is surjective and its kernel, the families with vanishing
bottom row, is the total complex of `K.rowShift` shifted by one; the proof is an
elementwise version of this observation.

The analogous statement for the projection onto the first column,
`RawBi.colZeroProj_quasiIso`, is deduced by transposition in
`AffineCrystalline.Homology.CosimplicialTot`.

## Main definitions

* `RawBi.RawAcyclic`: acyclicity of the total complex, stated on families.
* `RawBi.rowShift`: the bicomplex formed by the rows `q ≥ 1`.
* `RawBi.rowZeroComplex`: the bottom row as a cochain complex.
* `RawBi.rowZeroProj`: the projection `Tot K ⟶ K(•,0)`.

## Main results

* `RawBi.rawAcyclic_of_columnsExact`, `RawBi.rawAcyclic_of_rowsExact`: acyclic
  assembly, in the form used here.
* `RawBi.rowZeroProj_quasiIso`: if `Tot (K.rowShift)` is acyclic, the projection
  onto the bottom row is a quasi-isomorphism.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AffineCrystalline.Homology

variable {R : Type u} [Ring R]

namespace RawBi

variable (K : RawBi.{v} R)

/-- Acyclicity of the total complex, stated on families: every degree-zero
cocycle vanishes and every cocycle of positive degree is a coboundary. -/
def RawAcyclic : Prop :=
  (∀ f ∈ K.tot 0, K.dRaw f = 0 → f = 0) ∧
    ∀ n (f : K.Fam), f ∈ K.tot (n + 1) → K.dRaw f = 0 → ∃ g ∈ K.tot n, K.dRaw g = f

/-- A bicomplex with exact columns has acyclic total complex. -/
theorem rawAcyclic_of_columnsExact (h : K.ColumnsExact) : K.RawAcyclic :=
  ⟨K.eq_zero_of_columnsExact_of_mem_tot_zero h, K.exists_dRaw_eq_of_columnsExact h⟩

/-- A bicomplex with exact rows has acyclic total complex. -/
theorem rawAcyclic_of_rowsExact (h : K.RowsExact) : K.RawAcyclic :=
  ⟨K.eq_zero_of_rowsExact_of_mem_tot_zero h, K.exists_dRaw_eq_of_rowsExact h⟩

/-- The bicomplex formed by the rows `q ≥ 1`, reindexed to start in row `0`. -/
@[reducible] def rowShift : RawBi.{v} R where
  M p q := K.M p (q + 1)
  dh p p' q := K.dh p p' (q + 1)
  dv p q q' := K.dv p (q + 1) (q' + 1)
  dh_shape p p' q h := K.dh_shape p p' (q + 1) h
  dv_shape p q q' h := K.dv_shape p (q + 1) (q' + 1) (by omega)
  dh_dh p p' p'' q := K.dh_dh p p' p'' (q + 1)
  dv_dv p q q' q'' := K.dv_dv p (q + 1) (q' + 1) (q'' + 1)
  comm p p' q q' := K.comm p p' (q + 1) (q' + 1)

/-- The bottom row as a cochain complex. -/
noncomputable def rowZeroComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun p ↦ K.M p 0) (fun p ↦ K.dh p (p + 1) 0)
    (fun p ↦ K.dh_dh p (p + 1) (p + 2) 0)

theorem rowZeroComplex_d (p : ℕ) : K.rowZeroComplex.d p (p + 1) = K.dh p (p + 1) 0 := by
  simp [rowZeroComplex]

theorem rowZeroComplex_d_pred (n : ℕ) (hn : 0 < n) :
    K.rowZeroComplex.d (n - 1) n = K.dh (n - 1) n 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact K.rowZeroComplex_d m

theorem rowZeroComplex_d_zero_zero : K.rowZeroComplex.d 0 0 = 0 :=
  K.rowZeroComplex.shape 0 0 (by simp)

/-- The projection of the total complex onto its bottom row. -/
noncomputable def rowZeroProj : K.totComplex ⟶ K.rowZeroComplex where
  f n := ModuleCat.ofHom
    { toFun := fun x ↦ (show K.M n 0 from K.val x (n, 0))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  comm' := by
    rintro i _ rfl
    apply ModuleCat.hom_ext
    ext x
    change (K.rowZeroComplex.d i (i + 1)).hom (K.val x (i, 0)) =
      (show K.M (i + 1) 0 from K.val ((K.totComplex.d i (i + 1)).hom x) (i + 1, 0))
    rw [totComplex_d_val, rowZeroComplex_d, dRaw_apply_row_zero]
    rfl

theorem rowZeroProj_apply (n : ℕ) (x : K.totComplex.X n) :
    (K.rowZeroProj.f n).hom x = K.val x (n, 0) := rfl

/-! ### Families split into the bottom row and the shifted rows -/

/-- The shifted rows of a family. -/
def rowTail (F : K.Fam) : K.rowShift.Fam := fun pq ↦ F (pq.1, pq.2 + 1)

/-- Auxiliary function for `RawBi.rowLift`, defined by recursion on the row
index. -/
def rowLiftAux (g : K.rowShift.Fam) (p : ℕ) : ∀ q, K.M p q
  | 0 => 0
  | q + 1 => g (p, q)

/-- Place a family of the shifted rows back into the rows `q ≥ 1`, with zero
bottom row. -/
def rowLift (g : K.rowShift.Fam) : K.Fam := fun pq ↦ K.rowLiftAux g pq.1 pq.2

theorem rowTail_rowLift (g : K.rowShift.Fam) : K.rowTail (K.rowLift g) = g := rfl

theorem rowLift_zero_row (g : K.rowShift.Fam) (p : ℕ) : K.rowLift g (p, 0) = 0 := rfl

theorem rowTail_mem {n : ℕ} {F : K.Fam} (hF : F ∈ K.tot n) :
    K.rowTail F ∈ K.rowShift.tot (n - 1) := by
  rintro ⟨p, q⟩ h
  exact hF (p, q + 1) (by simp only [ne_eq] at h ⊢; omega)

theorem rowLift_mem {n : ℕ} {g : K.rowShift.Fam} (hg : g ∈ K.rowShift.tot n) :
    K.rowLift g ∈ K.tot (n + 1) := by
  rintro ⟨p, q⟩ h
  rcases q with _ | q
  · rfl
  · exact hg (p, q) (by simp only [ne_eq] at h ⊢; omega)

theorem fam_ext_row {F G : K.Fam} (h0 : ∀ p, F (p, 0) = G (p, 0))
    (ht : K.rowTail F = K.rowTail G) : F = G := by
  funext ⟨p, q⟩
  rcases q with _ | q
  · exact h0 p
  · exact congrFun ht (p, q)

/-- The shifted rows of `d F` are the total differential of the shifted rows of
`F`, corrected in row `0` by the vertical differential of the bottom row of
`F`. -/
theorem rowTail_dRaw (F : K.Fam) (p q : ℕ) :
    K.rowTail (K.dRaw F) (p, q) = K.rowShift.dRaw (K.rowTail F) (p, q) +
      (if q = 0 then ((-1 : ℤ) ^ p) • (K.dv p q (q + 1)).hom (F (p, q)) else 0) := by
  change K.dRaw F (p, q + 1) = _
  rw [dRaw_apply, dRaw_apply]
  change (K.dh (p - 1) p (q + 1)).hom (F (p - 1, q + 1)) +
      ((-1 : ℤ) ^ p) • (K.dv p q (q + 1)).hom (F (p, q)) =
    (K.dh (p - 1) p (q + 1)).hom (F (p - 1, q + 1)) +
      ((-1 : ℤ) ^ p) • (K.dv p (q - 1 + 1) (q + 1)).hom (F (p, q - 1 + 1)) + _
  rcases q with _ | q
  · rw [if_pos rfl, K.dv_shape_apply (p := p) (q := 0 - 1 + 1) (q' := 0 + 1) (by omega),
      smul_zero, add_zero]
  · rw [if_neg (Nat.succ_ne_zero q), add_zero]
    rfl

theorem rowTail_dRaw_lift (g : K.rowShift.Fam) :
    K.rowTail (K.dRaw (K.rowLift g)) = K.rowShift.dRaw g := by
  funext ⟨p, q⟩
  rw [rowTail_dRaw]
  rcases q with _ | q
  · rw [if_pos rfl, rowLift_zero_row, map_zero, smul_zero, add_zero]
    rfl
  · rw [if_neg (Nat.succ_ne_zero q), add_zero]
    rfl

theorem dRaw_lift_zero_row (g : K.rowShift.Fam) (p : ℕ) :
    K.dRaw (K.rowLift g) (p, 0) = 0 := by
  rw [dRaw_apply_row_zero, rowLift_zero_row, map_zero]

/-- A cocycle with vanishing bottom row restricts to a cocycle of the shifted rows. -/
theorem rowShift_dRaw_rowTail_eq_zero {F : K.Fam} (hd : K.dRaw F = 0)
    (h0 : ∀ p, F (p, 0) = 0) : K.rowShift.dRaw (K.rowTail F) = 0 := by
  funext ⟨p, q⟩
  have h1 := K.rowTail_dRaw F p q
  rw [hd] at h1
  rcases q with _ | q
  · rw [if_pos rfl, h0, map_zero, smul_zero, add_zero] at h1
    exact h1.symm
  · rw [if_neg (Nat.succ_ne_zero q), add_zero] at h1
    exact h1.symm

/-- If the total complex of the shifted rows is acyclic, a cocycle of degree `n + 1` with
vanishing bottom row is the coboundary of a family of degree `n` with vanishing bottom row. -/
theorem exists_dRaw_eq_of_row_zero (h : K.rowShift.RawAcyclic) {n : ℕ} {F : K.Fam}
    (hF : F ∈ K.tot (n + 1)) (hd : K.dRaw F = 0) (h0 : ∀ p, F (p, 0) = 0) :
    ∃ G ∈ K.tot n, (∀ p, G (p, 0) = 0) ∧ K.dRaw G = F := by
  have ht := K.rowShift_dRaw_rowTail_eq_zero hd h0
  have htmem : K.rowTail F ∈ K.rowShift.tot n := by simpa using K.rowTail_mem hF
  rcases n with _ | m
  · refine ⟨0, Submodule.zero_mem _, fun _ ↦ rfl, ?_⟩
    rw [map_zero]
    exact K.fam_ext_row (fun p ↦ (h0 p).symm) (h.1 _ htmem ht).symm
  · obtain ⟨g, hg, hgt⟩ := h.2 m _ htmem ht
    refine ⟨K.rowLift g, K.rowLift_mem hg, K.rowLift_zero_row g, ?_⟩
    refine K.fam_ext_row (fun p ↦ ?_) ?_
    · rw [K.dRaw_lift_zero_row, h0]
    · rw [K.rowTail_dRaw_lift, hgt]

/-- Surjectivity of `rowZeroProj` on cohomology, in elementwise form: every cocycle of the
bottom row is the projection of a cocycle of the total complex. -/
theorem rowZeroProj_elementwise_surj (h : K.rowShift.RawAcyclic) (n : ℕ)
    (r : K.rowZeroComplex.X n) (hr : (K.rowZeroComplex.d n (n + 1)).hom r = 0) :
    ∃ x : K.totComplex.X n, (K.totComplex.d n (n + 1)).hom x = 0 ∧
      ∃ z : K.rowZeroComplex.X (n - 1),
        (K.rowZeroProj.f n).hom x = r + (K.rowZeroComplex.d (n - 1) n).hom z := by
  let r' : K.M n 0 := r
  rw [rowZeroComplex_d] at hr
  have hd0 : ∀ p, K.dRaw (K.single n 0 r') (p, 0) = 0 := fun p ↦ by
    by_cases hp : p = n + 1
    · subst hp
      rw [dRaw_single_right]
      exact hr
    · exact K.dRaw_single_other _ _ _ _ _ (by simpa using hp) (by simp)
  obtain ⟨G, hG, hG0, hGd⟩ := K.exists_dRaw_eq_of_row_zero h
    (K.dRaw_mem (K.single_mem n 0 r')) (K.dRaw_dRaw _) hd0
  refine ⟨K.ofFam (K.single n 0 r' - G) (sub_mem (K.single_mem n 0 r') hG), ?_, 0, ?_⟩
  · apply K.val_injective
    rw [totComplex_d_val, val_ofFam, map_sub, hGd, sub_self]
    rfl
  · rw [map_zero, add_zero, rowZeroProj_apply, val_ofFam, Pi.sub_apply, hG0, sub_zero]
    exact K.single_apply_same n 0 r'

/-- Injectivity of `rowZeroProj` on cohomology, in elementwise form: a cocycle of the total
complex whose projection is a coboundary is itself a coboundary. -/
theorem rowZeroProj_elementwise_inj (h : K.rowShift.RawAcyclic) (n : ℕ)
    (x : K.totComplex.X n) (hx : (K.totComplex.d n (n + 1)).hom x = 0)
    (z : K.rowZeroComplex.X (n - 1))
    (hz : (K.rowZeroProj.f n).hom x = (K.rowZeroComplex.d (n - 1) n).hom z) :
    ∃ w : K.totComplex.X (n - 1), (K.totComplex.d (n - 1) n).hom w = x := by
  have hdx : K.dRaw (K.val x) = 0 := by
    rw [← totComplex_d_val, hx, val_zero]
  rcases n with _ | m
  · -- in degree `0`, the cocycle `x` vanishes
    rw [K.rowZeroComplex_d_zero_zero, rowZeroProj_apply] at hz
    refine ⟨0, K.val_injective ?_⟩
    rw [map_zero, val_zero]
    refine (K.fam_ext_row (G := 0) (fun p ↦ ?_)
      (funext fun pq ↦ K.val_mem x (pq.1, pq.2 + 1) (by simp))).symm
    rcases p with _ | p
    · exact hz
    · exact K.val_mem x (p + 1, 0) (by simp)
  · -- subtract the coboundary of the bottom-row primitive `z`
    let z' : K.M m 0 := z
    have hz' : K.val x (m + 1, 0) = (K.dh m (m + 1) 0).hom z' :=
      hz.trans (congrArg (fun f ↦ f.hom z) (K.rowZeroComplex_d m))
    have hsmem : K.single m 0 z' ∈ K.tot m := K.single_mem m 0 z'
    have hx'0 : ∀ p, (K.val x - K.dRaw (K.single m 0 z')) (p, 0) = 0 := fun p ↦ by
      by_cases hp : p = m + 1
      · subst hp
        rw [Pi.sub_apply, dRaw_single_right, hz', sub_self]
      · rw [Pi.sub_apply, K.val_mem x (p, 0) (by simpa using hp),
          K.dRaw_single_other _ _ _ _ _ (by simpa using hp) (by simp), sub_zero]
    obtain ⟨G, hG, -, hGd⟩ := K.exists_dRaw_eq_of_row_zero h
      (sub_mem (K.val_mem x) (K.dRaw_mem hsmem)) (by rw [map_sub, hdx, K.dRaw_dRaw, sub_zero])
      hx'0
    refine ⟨K.ofFam (K.single m 0 z' + G) (add_mem hsmem hG), K.val_injective ?_⟩
    rw [K.totComplex_d_pred_val (m + 1) (by omega), val_ofFam, map_add, hGd, add_sub_cancel]

/-- **Projection onto the bottom row.**  If the total complex of the rows
`q ≥ 1` is acyclic, the projection `Tot K ⟶ K(•,0)` is a quasi-isomorphism. -/
theorem rowZeroProj_quasiIso (h : K.rowShift.RawAcyclic) : QuasiIso K.rowZeroProj :=
  quasiIso_of_elementwise _ (K.rowZeroProj_elementwise_surj h) (K.rowZeroProj_elementwise_inj h)

end RawBi

end AffineCrystalline.Homology
