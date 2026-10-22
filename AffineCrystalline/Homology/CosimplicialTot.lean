/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Homology.TotProjection
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Module.BigOperators

/-!
# The Bhatt–de Jong lemma for cosimplicial cochain complexes of modules

Let `Kc` be a cosimplicial object in `ℕ`-indexed cochain complexes of modules,
and let `K` be the associated first-quadrant bicomplex, `K(p,q) = Kc[p]^q`, with
the alternating coface differential in the `p`-direction and the internal
differential in the `q`-direction.  The total complex of `K` admits two
projections

```text
Kc[0]  ⟵  Tot K  ⟶  (Kc[•]^0, alternating coface differential),
```

and this file gives criteria for each of them to be a quasi-isomorphism.

* Column form: if every first-vertex map `Kc[0] ⟶ Kc[n]` is a
  quasi-isomorphism, the projection onto the first column `Kc[0]` is a
  quasi-isomorphism.  The proof compares `Kc` with the constant cosimplicial
  object on `Kc[0]` through the maps induced by `[n] ⟶ [0]`; this is a
  columnwise quasi-isomorphism, so it induces a quasi-isomorphism on total
  complexes (`RawBi.totMap_quasiIso`), and the statement is checked directly for
  constant cosimplicial objects.
* Row form: if for every `q ≥ 1` the alternating coface complex of the
  cosimplicial module `Kc[•]^q` is exact, the projection onto the bottom row is
  a quasi-isomorphism.  This follows from acyclic assembly and
  `RawBi.rowZeroProj_quasiIso`.

Applied to the bicomplex `Ω^q_{D(p)}` of de Rham complexes of the divided power
envelopes of a Čech nerve, these two statements give the comparison between
crystalline and de Rham cohomology in the affine case.

## Main definitions

* `RawBi.colZeroComplex`, `RawBi.colZeroProj`: the first column of a bicomplex
  and the projection of the total complex onto it.
* `RawBi.ofCosimplicial`: the bicomplex of a cosimplicial cochain complex.
* `RawBi.rowZeroComplexIso`, `RawBi.colZeroComplexIso`: identification of its
  bottom row with the alternating coface complex of `Kc[•]^0`, and of its first
  column with `Kc[0]`.
* `RawBi.homOfCosimplicial`: the morphism of bicomplexes induced by a morphism
  of cosimplicial complexes.
* `RawBi.toConst`: the canonical morphism from `Kc` to the constant cosimplicial
  object on `Kc[0]`.

## Main results

* `RawBi.colZeroProj_quasiIso`: if the total complex of the columns `p ≥ 1` is
  acyclic, the projection onto the first column is a quasi-isomorphism.
* `RawBi.bhattDeJong_column`: the column form of the Bhatt–de Jong lemma.
* `RawBi.bhattDeJong_row`: the row form of the Bhatt–de Jong lemma.

## References

* B. Bhatt, A. J. de Jong, *Crystalline cohomology and de Rham cohomology*,
  arXiv:1110.5001.
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace AffineCrystalline.Homology

variable {R : Type u} [Ring R]

/-- A cochain complex is isomorphic to the complex `CochainComplex.of` built
from its successor differentials. -/
noncomputable def ofSuccIso (X : CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex.of (fun n ↦ X.X n) (fun n ↦ X.d n (n + 1)) (fun _ ↦ X.d_comp_d _ _ _) ≅
      X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i _ rfl
    simp [CochainComplex.of_d])

namespace RawBi

variable (K : RawBi.{v} R)

/-! ## Projection onto the first column -/

/-- The first column as a cochain complex. -/
noncomputable def colZeroComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  K.transpose.rowZeroComplex

/-- The projection of the total complex onto its first column. -/
noncomputable def colZeroProj : K.totComplex ⟶ K.colZeroComplex :=
  K.transposeTotIso.inv ≫ K.transpose.rowZeroProj

/-- The projection onto the first column takes the `(0, n)` component; the
transposition sign `(-1)^(n * 0)` is trivial. -/
theorem colZeroProj_apply (n : ℕ) (x : K.totComplex.X n) :
    (K.colZeroProj.f n).hom x = K.val x (0, n) := by
  change ((-1 : ℤ) ^ (n * 0)) • K.val x (0, n) = K.val x (0, n)
  rw [mul_zero, pow_zero, one_smul]

/-- **Projection onto the first column.**  If the total complex of the columns
`p ≥ 1` is acyclic, the projection `Tot K ⟶ K(0,•)` is a quasi-isomorphism. -/
theorem colZeroProj_quasiIso (h : K.transpose.rowShift.RawAcyclic) :
    QuasiIso K.colZeroProj := by
  have := K.transpose.rowZeroProj_quasiIso h
  have h2 := quasiIso_of_isIso K.transposeTotIso.inv
  exact quasiIso_comp _ _ (hφ := h2) (hφ' := this)

/-! ## Bicomplexes of cosimplicial complexes -/

section Cosimplicial

variable (Kc : CosimplicialObject (CochainComplex (ModuleCat.{v} R) ℕ))

/-- The cosimplicial module `Kc[•]^q` of degree-`q` components. -/
abbrev component (q : ℕ) : CosimplicialObject (ModuleCat.{v} R) :=
  Kc ⋙ HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℕ) q

/-- The alternating coface complex of the cosimplicial module `Kc[•]^q`. -/
noncomputable abbrev componentComplex (q : ℕ) : CochainComplex (ModuleCat.{v} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R)).obj (component Kc q)

/-- The bicomplex `K(p,q) = Kc[p]^q`, with the alternating coface differential
horizontally and the internal differential of `Kc[p]` vertically. -/
noncomputable def ofCosimplicial : RawBi.{v} R where
  M p q := (Kc.obj ⦋p⦌).X q
  dh p p' q := (componentComplex Kc q).d p p'
  dv p q q' := (Kc.obj ⦋p⦌).d q q'
  dh_shape p p' q h := (componentComplex Kc q).shape p p' (by simpa using h)
  dv_shape p q q' h := (Kc.obj ⦋p⦌).shape q q' (by simpa using h)
  dh_dh p p' p'' q := (componentComplex Kc q).d_comp_d p p' p''
  dv_dv p q q' q'' := (Kc.obj ⦋p⦌).d_comp_d q q' q''
  comm p p' q q' := (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R)).map
    (Functor.whiskerLeft Kc
      (HomologicalComplex.dNatTrans (ModuleCat.{v} R) (ComplexShape.up ℕ) q q'))).comm p p').symm

/-- The horizontal differential is the alternating sum of the cofaces. -/
theorem ofCosimplicial_dh_succ (p q : ℕ) :
    (ofCosimplicial Kc).dh p (p + 1) q =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • ((Kc.map (SimplexCategory.δ i)).f q) := by
  change (componentComplex Kc q).d p (p + 1) = _
  exact CochainComplex.of_d (fun n ↦ (component Kc q).obj ⦋n⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (component Kc q)) p

/-- The bottom row of the bicomplex is the alternating coface complex of
`Kc[•]^0`. -/
noncomputable def rowZeroComplexIso :
    (ofCosimplicial Kc).rowZeroComplex ≅ componentComplex Kc 0 :=
  ofSuccIso (componentComplex Kc 0)

/-- The first column of the bicomplex is `Kc[0]`. -/
noncomputable def colZeroComplexIso :
    (ofCosimplicial Kc).colZeroComplex ≅ Kc.obj ⦋0⦌ :=
  ofSuccIso (Kc.obj ⦋0⦌)

variable {Kc} in
/-- The morphism of bicomplexes induced by a morphism of cosimplicial
complexes. -/
noncomputable def homOfCosimplicial
    {Kc' : CosimplicialObject (CochainComplex (ModuleCat.{v} R) ℕ)}
    (τ : Kc ⟶ Kc') : Hom (ofCosimplicial Kc) (ofCosimplicial Kc') where
  f p q := (τ.app ⦋p⦌).f q
  comm_h p p' q := (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R)).map
    (Functor.whiskerRight τ
      (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℕ) q))).comm p p').symm
  comm_v p q q' := ((τ.app ⦋p⦌).comm q q').symm

variable {Kc} in
/-- A levelwise quasi-isomorphism of cosimplicial complexes induces a columnwise
quasi-isomorphism of bicomplexes. -/
theorem homOfCosimplicial_colSurj_colInj
    {Kc' : CosimplicialObject (CochainComplex (ModuleCat.{v} R) ℕ)} (τ : Kc ⟶ Kc')
    (hτ : ∀ p, QuasiIso (τ.app ⦋p⦌)) :
    (homOfCosimplicial τ).ColSurj ∧ (homOfCosimplicial τ).ColInj := by
  constructor
  · intro p q y hy
    exact ((quasiIsoAt_iff_elementwise (τ.app ⦋p⦌) q).1 inferInstance).1 y hy
  · intro p q x hx z hz
    exact ((quasiIsoAt_iff_elementwise (τ.app ⦋p⦌) q).1 inferInstance).2 x hx z hz

/-! ## The constant cosimplicial complex -/

/-- The constant cosimplicial object on a complex. -/
abbrev constCosimplicial (M : CochainComplex (ModuleCat.{v} R) ℕ) :
    CosimplicialObject (CochainComplex (ModuleCat.{v} R) ℕ) :=
  (Functor.const SimplexCategory).obj M

/-- `∑_{i=0}^{n+1} (-1)^i` is `0` for even `n` and `1` for odd `n`. -/
theorem sum_neg_one_pow_eq_ite (n : ℕ) :
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) = if Even n then 0 else 1 := by
  simp [Fin.sum_neg_one_pow, Nat.even_add_one, parity_simps]

/-- For a constant cosimplicial complex, the horizontal differential
`K(p,q) ⟶ K(p+1,q)` is `0` for even `p` and the identity for odd `p`. -/
theorem const_dh_apply (M : CochainComplex (ModuleCat.{v} R) ℕ) (p q : ℕ) (x : M.X q) :
    ((ofCosimplicial (constCosimplicial M)).dh p (p + 1) q).hom x =
      (if Even p then 0 else 1 : ℤ) • x := by
  rw [ofCosimplicial_dh_succ, ← sum_neg_one_pow_eq_ite, Finset.sum_smul]
  erw [ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rfl

/-- For a constant cosimplicial complex, the rows of the bicomplex restricted to
the columns `p ≥ 1` are exact, since their differentials alternate between the
identity and `0`. -/
theorem const_colShift_columnsExact (M : CochainComplex (ModuleCat.{v} R) ℕ) :
    (ofCosimplicial (constCosimplicial M)).transpose.rowShift.ColumnsExact := by
  intro p q x hx
  let x0 : M.X p := x
  have hx0 : (if Even (q + 1) then 0 else 1 : ℤ) • x0 = 0 :=
    (const_dh_apply M (q + 1) p x0).symm.trans hx
  change ∃ y : M.X p,
    ((ofCosimplicial (constCosimplicial M)).dh (q - 1 + 1) (q + 1) p).hom y = x0
  rcases q with _ | q
  · have : ¬ Even (0 + 1) := by decide
    rw [if_neg this, one_smul] at hx0
    exact ⟨0, (map_zero _).trans hx0.symm⟩
  · by_cases hq : Even (q + 1 + 1)
    · have hq' : ¬ Even (q + 1) := by
        rw [Nat.even_add_one] at hq; exact hq
      refine ⟨x0, ?_⟩
      have := const_dh_apply M (q + 1) p x0
      rw [if_neg hq', one_smul] at this
      exact this
    · rw [if_neg hq, one_smul] at hx0
      exact ⟨0, (map_zero _).trans hx0.symm⟩

/-- The canonical morphism from `Kc` to the constant cosimplicial object on
`Kc[0]`, induced by the maps `[n] ⟶ [0]`. -/
noncomputable def toConst :
    Kc ⟶ constCosimplicial (Kc.obj ⦋0⦌) where
  app n := Kc.map (SimplexCategory.const n ⦋0⦌ 0)
  naturality m n θ := by
    change Kc.map θ ≫ Kc.map (SimplexCategory.const n ⦋0⦌ 0) =
      Kc.map (SimplexCategory.const m ⦋0⦌ 0) ≫ 𝟙 _
    rw [← Kc.map_comp, Category.comp_id, SimplexCategory.eq_const_to_zero (θ ≫ _)]

/-- In degree `0`, the morphism to the constant cosimplicial object is the
identity. -/
theorem toConst_app_zero : (toConst Kc).app ⦋0⦌ = 𝟙 _ := by
  change Kc.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) = 𝟙 _
  rw [← Kc.map_id]
  congr 1
  exact (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm

/-- If every first-vertex map `Kc[0] ⟶ Kc[p]` is a quasi-isomorphism, then so is every
component `Kc[p] ⟶ Kc[0]` of `toConst Kc`. -/
theorem quasiIso_toConst_app
    (hP : ∀ n : ℕ, QuasiIso (Kc.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))) (p : ℕ) :
    QuasiIso ((toConst Kc).app ⦋p⦌) := by
  have h1 : Kc.map (SimplexCategory.const ⦋0⦌ ⦋p⦌ 0) ≫ (toConst Kc).app ⦋p⦌ = 𝟙 _ := by
    change Kc.map _ ≫ Kc.map _ = 𝟙 _
    rw [← Kc.map_comp, ← Kc.map_id]
    congr 1
    exact SimplexCategory.eq_const_to_zero _ |>.trans
      (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm
  have : QuasiIso (Kc.map (SimplexCategory.const ⦋0⦌ ⦋p⦌ 0) ≫ (toConst Kc).app ⦋p⦌) := by
    rw [h1]
    infer_instance
  exact quasiIso_of_comp_left (Kc.map (SimplexCategory.const ⦋0⦌ ⦋p⦌ 0)) _

/-- The projection of `Tot (ofCosimplicial Kc)` onto its first column factors through the
corresponding projection for the constant cosimplicial complex on `Kc[0]`. -/
theorem colZeroProj_eq_totMap_comp :
    (ofCosimplicial Kc).colZeroProj =
      totMap (homOfCosimplicial (toConst Kc)) ≫
        (ofCosimplicial (constCosimplicial (Kc.obj ⦋0⦌))).colZeroProj := by
  ext n x
  change (((ofCosimplicial Kc).colZeroProj.f n).hom x) =
    (((ofCosimplicial (constCosimplicial (Kc.obj ⦋0⦌))).colZeroProj.f n).hom
      (((totMap (homOfCosimplicial (toConst Kc))).f n).hom x))
  rw [colZeroProj_apply, colZeroProj_apply, totMap_val, Hom.famMap_apply]
  change _ = (((toConst Kc).app ⦋0⦌).f n).hom _
  rw [toConst_app_zero]
  rfl

/-- **Bhatt–de Jong lemma, column form.**  If every first-vertex map
`Kc[0] ⟶ Kc[n]` is a quasi-isomorphism, the projection of the total complex
onto its first column `Kc[0]` is a quasi-isomorphism. -/
theorem bhattDeJong_column
    (hP : ∀ n : ℕ, QuasiIso (Kc.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))) :
    QuasiIso (ofCosimplicial Kc).colZeroProj := by
  obtain ⟨hS, hI⟩ :=
    homOfCosimplicial_colSurj_colInj (toConst Kc) (quasiIso_toConst_app Kc hP)
  have hT := totMap_quasiIso (homOfCosimplicial (toConst Kc)) hS hI
  have hC := (ofCosimplicial (constCosimplicial (Kc.obj ⦋0⦌))).colZeroProj_quasiIso
    ((ofCosimplicial (constCosimplicial (Kc.obj ⦋0⦌))).transpose.rowShift.rawAcyclic_of_columnsExact
      (const_colShift_columnsExact (Kc.obj ⦋0⦌)))
  rw [colZeroProj_eq_totMap_comp]
  exact quasiIso_comp _ _ (hφ := hT) (hφ' := hC)

/-- **Bhatt–de Jong lemma, row form.**  If the alternating coface complex of
`Kc[•]^q` is exact for every `q ≥ 1`, the projection of the total complex onto
its bottom row, the alternating coface complex of `Kc[•]^0`, is a
quasi-isomorphism. -/
theorem bhattDeJong_row
    (hV : ∀ q n, (componentComplex Kc (q + 1)).ExactAt n) :
    QuasiIso (ofCosimplicial Kc).rowZeroProj := by
  apply rowZeroProj_quasiIso
  apply rawAcyclic_of_rowsExact
  intro p q x hx
  exact (exactAt_iff_elementwise _ p).1 (hV q p) x hx

end Cosimplicial

end RawBi

end AffineCrystalline.Homology
