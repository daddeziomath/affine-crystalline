/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Homology.TotM

/-!
# Columnwise quasi-isomorphisms induce quasi-isomorphisms of total complexes

Let `φ : K ⟶ L` be a morphism of first-quadrant bicomplexes of modules which is
a quasi-isomorphism on every column.  Then the induced morphism of total
complexes `Tot K ⟶ Tot L` is a quasi-isomorphism.

The proof forms the columnwise mapping fibre of `φ`, the bicomplex with terms
`K(p,q) ⊕ L(p,q-1)`.  Its columns are the mapping fibres of the column maps,
hence exact, so its total complex is acyclic by acyclic assembly
(`RawBi.exists_dRaw_eq_of_columnsExact`).  The total complex of the fibre is identified, on
families, with the mapping fibre of `Tot K ⟶ Tot L`, and an elementwise
argument transfers its acyclicity to the statement that the total map is a
quasi-isomorphism.

## Main definitions

* `AffineCrystalline.Homology.SuccBi`: bicomplexes given by successor-indexed
  differentials, converted to raw bicomplexes by `SuccBi.toRaw` (in the style of
  `CochainComplex.of`).
* `RawBi.Hom`: morphisms of raw bicomplexes, and `RawBi.totMap`, the induced
  morphism of total complexes.
* `RawBi.Hom.fiber`: the columnwise mapping fibre `K(p,q) ⊕ L(p,q-1)`.
* `RawBi.Hom.ColSurj`, `RawBi.Hom.ColInj`: elementwise surjectivity and
  injectivity on the cohomology of every column.

## Main results

* `RawBi.Hom.columnsExact_fib`: the columns of the fibre of a columnwise
  quasi-isomorphism are exact.
* `RawBi.totMap_quasiIso`: a columnwise quasi-isomorphism of first-quadrant
  bicomplexes induces a quasi-isomorphism of total complexes.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AffineCrystalline.Homology

variable {R : Type u} [Ring R]

/-! ## Successor-indexed bicomplexes -/

/-- A first-quadrant bicomplex of modules with successor-indexed differentials
`dh p q : M p q ⟶ M (p+1) q` and `dv p q : M p q ⟶ M p (q+1)`. -/
structure SuccBi (R : Type u) [Ring R] where
  M : ℕ → ℕ → ModuleCat.{v} R
  dh : ∀ p q, M p q ⟶ M (p + 1) q
  dv : ∀ p q, M p q ⟶ M p (q + 1)
  dh_dh : ∀ p q, dh p q ≫ dh (p + 1) q = 0
  dv_dv : ∀ p q, dv p q ≫ dv p (q + 1) = 0
  comm : ∀ p q, dh p q ≫ dv (p + 1) q = dv p q ≫ dh p (q + 1)

namespace SuccBi

variable (S : SuccBi.{v} R)

/-- The horizontal differentials with arbitrary indices, zero unless
`p' = p + 1`. -/
def dhRaw (p p' q : ℕ) : S.M p q ⟶ S.M p' q :=
  if h : p + 1 = p' then S.dh p q ≫ eqToHom (by rw [h]) else 0

/-- The vertical differentials with arbitrary indices, zero unless
`q' = q + 1`. -/
def dvRaw (p q q' : ℕ) : S.M p q ⟶ S.M p q' :=
  if h : q + 1 = q' then S.dv p q ≫ eqToHom (by rw [h]) else 0

@[simp] theorem dhRaw_succ (p q : ℕ) : S.dhRaw p (p + 1) q = S.dh p q := by
  simp [dhRaw]

@[simp] theorem dvRaw_succ (p q : ℕ) : S.dvRaw p q (q + 1) = S.dv p q := by
  simp [dvRaw]

theorem dhRaw_ne {p p' : ℕ} (q : ℕ) (h : p + 1 ≠ p') : S.dhRaw p p' q = 0 := by
  simp [dhRaw, h]

theorem dvRaw_ne (p : ℕ) {q q' : ℕ} (h : q + 1 ≠ q') : S.dvRaw p q q' = 0 := by
  simp [dvRaw, h]

/-- The raw bicomplex of a successor-indexed bicomplex. -/
def toRaw : RawBi.{v} R where
  M := S.M
  dh := S.dhRaw
  dv := S.dvRaw
  dh_shape p p' q h := S.dhRaw_ne q h
  dv_shape p q q' h := S.dvRaw_ne p h
  dh_dh p p' p'' q := by
    by_cases h1 : p + 1 = p'
    · subst h1
      by_cases h2 : p + 1 + 1 = p''
      · subst h2
        simp [S.dh_dh]
      · rw [S.dhRaw_ne q h2, comp_zero]
    · rw [S.dhRaw_ne q h1, zero_comp]
  dv_dv p q q' q'' := by
    by_cases h1 : q + 1 = q'
    · subst h1
      by_cases h2 : q + 1 + 1 = q''
      · subst h2
        simp [S.dv_dv]
      · rw [S.dvRaw_ne p h2, comp_zero]
    · rw [S.dvRaw_ne p h1, zero_comp]
  comm p p' q q' := by
    by_cases h1 : p + 1 = p'
    · subst h1
      by_cases h2 : q + 1 = q'
      · subst h2
        simp [S.comm]
      · rw [S.dvRaw_ne _ h2, S.dvRaw_ne _ h2, comp_zero, zero_comp]
    · rw [S.dhRaw_ne _ h1, S.dhRaw_ne _ h1, comp_zero, zero_comp]

@[simp] theorem toRaw_M : S.toRaw.M = S.M := rfl

theorem toRaw_dh_succ (p q : ℕ) : S.toRaw.dh p (p + 1) q = S.dh p q := S.dhRaw_succ p q

theorem toRaw_dv_succ (p q : ℕ) : S.toRaw.dv p q (q + 1) = S.dv p q := S.dvRaw_succ p q

end SuccBi

/-! ## Maps of raw bicomplexes -/

namespace RawBi

/-- A morphism of raw bicomplexes: maps `f p q : K(p,q) ⟶ L(p,q)` commuting
with both differentials. -/
structure Hom (K L : RawBi.{v} R) where
  f : ∀ p q, K.M p q ⟶ L.M p q
  comm_h : ∀ p p' q, K.dh p p' q ≫ f p' q = f p q ≫ L.dh p p' q
  comm_v : ∀ p q q', K.dv p q q' ≫ f p q' = f p q ≫ L.dv p q q'

variable {K L : RawBi.{v} R} (φ : Hom K L)

namespace Hom

theorem comm_h_apply (p p' q : ℕ) (x : K.M p q) :
    (φ.f p' q).hom ((K.dh p p' q).hom x) = (L.dh p p' q).hom ((φ.f p q).hom x) := by
  change (K.dh p p' q ≫ φ.f p' q).hom x = (φ.f p q ≫ L.dh p p' q).hom x
  rw [φ.comm_h]

theorem comm_v_apply (p q q' : ℕ) (x : K.M p q) :
    (φ.f p q').hom ((K.dv p q q').hom x) = (L.dv p q q').hom ((φ.f p q).hom x) := by
  change (K.dv p q q' ≫ φ.f p q').hom x = (φ.f p q ≫ L.dv p q q').hom x
  rw [φ.comm_v]

/-- The induced linear map on families. -/
def famMap : K.Fam →ₗ[R] L.Fam :=
  LinearMap.pi fun pq ↦ (φ.f pq.1 pq.2).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun pq : ℕ × ℕ ↦ (K.M pq.1 pq.2 : Type v)) pq

theorem famMap_apply (x : K.Fam) (pq : ℕ × ℕ) :
    φ.famMap x pq = (φ.f pq.1 pq.2).hom (x pq) := rfl

theorem famMap_mem {n : ℕ} {x : K.Fam} (hx : x ∈ K.tot n) : φ.famMap x ∈ L.tot n := by
  intro pq h
  rw [famMap_apply, hx pq h, map_zero]

theorem famMap_dRaw (x : K.Fam) : φ.famMap (K.dRaw x) = L.dRaw (φ.famMap x) := by
  funext ⟨p, q⟩
  rw [famMap_apply, dRaw_apply, dRaw_apply, map_add, map_zsmul, famMap_apply, famMap_apply,
    φ.comm_h_apply, φ.comm_v_apply]

end Hom

/-- The morphism of total complexes induced by a morphism of bicomplexes. -/
noncomputable def totMap : K.totComplex ⟶ L.totComplex where
  f n := ModuleCat.ofHom
    { toFun := fun x ↦ L.ofFam (φ.famMap (K.val x)) (φ.famMap_mem (K.val_mem x))
      map_add' := fun x y ↦ L.val_injective (map_add φ.famMap _ _)
      map_smul' := fun r x ↦ L.val_injective (map_smul φ.famMap r _) }
  comm' := by
    rintro i _ rfl
    apply ModuleCat.hom_ext
    ext x
    apply L.val_injective
    change L.val ((L.totComplex.d i (i + 1)).hom (L.ofFam _ _)) =
      φ.famMap (K.val ((K.totComplex.d i (i + 1)).hom x))
    rw [totComplex_d_val, totComplex_d_val, val_ofFam, φ.famMap_dRaw]

theorem totMap_val (n : ℕ) (x : K.totComplex.X n) :
    L.val (((totMap φ).f n).hom x) = φ.famMap (K.val x) := rfl

/-! ## The columnwise mapping fibre -/

namespace Hom

/-- The carrier of the fibre in bidegree `(p, q)`: `K(p,q) ⊕ L(p,q-1)`, with the
second component forced to vanish when `q = 0`. -/
def fibSub (_φ : Hom K L) (p q : ℕ) : Submodule R (K.M p q × L.M p (q - 1)) where
  carrier := {xy | q = 0 → xy.2 = 0}
  zero_mem' := fun _ ↦ rfl
  add_mem' := by
    intro a b ha hb h
    simp [ha h, hb h]
  smul_mem' := by
    intro r a ha h
    simp [ha h]

/-- The columnwise mapping fibre of a morphism of bicomplexes: horizontal
differentials `dh ⊕ dh`, and vertical differential
`(x, y) ↦ (dv x, f x - dv y)`. -/
noncomputable def fiber : SuccBi.{v} R where
  M p q := ModuleCat.of R (φ.fibSub p q)
  dh p q := ModuleCat.ofHom
    { toFun := fun xy ↦ ⟨((K.dh p (p + 1) q).hom xy.1.1,
          (L.dh p (p + 1) (q - 1)).hom xy.1.2), fun h ↦ by
            change (L.dh p (p + 1) (q - 1)).hom xy.1.2 = 0
            rw [xy.2 h, map_zero]⟩
      map_add' := fun a b ↦ Subtype.ext (Prod.ext (map_add _ _ _) (map_add _ _ _))
      map_smul' := fun r a ↦ Subtype.ext (Prod.ext (map_smul _ _ _) (map_smul _ _ _)) }
  dv p q := ModuleCat.ofHom
    { toFun := fun xy ↦ ⟨((K.dv p q (q + 1)).hom xy.1.1,
          (show L.M p q from (φ.f p q).hom xy.1.1 - (L.dv p (q - 1) q).hom xy.1.2)),
          fun h ↦ absurd h (Nat.succ_ne_zero q)⟩
      map_add' := fun a b ↦ Subtype.ext (Prod.ext (map_add _ _ _) (by
        change (φ.f p q).hom (a.1.1 + b.1.1) - (L.dv p (q - 1) q).hom (a.1.2 + b.1.2) = _
        rw [map_add, map_add, add_sub_add_comm]
        rfl))
      map_smul' := fun r a ↦ Subtype.ext (Prod.ext (map_smul _ _ _) (by
        change (φ.f p q).hom (r • a.1.1) - (L.dv p (q - 1) q).hom (r • a.1.2) = _
        rw [map_smul, map_smul, ← smul_sub]
        rfl)) }
  dh_dh p q := by
    apply ModuleCat.hom_ext
    ext xy
    · exact K.dh_dh_apply p (p + 1) (p + 2) q xy.1.1
    · exact L.dh_dh_apply p (p + 1) (p + 2) (q - 1) xy.1.2
  dv_dv p q := by
    apply ModuleCat.hom_ext
    ext xy
    · exact K.dv_dv_apply p q (q + 1) (q + 2) xy.1.1
    · change (φ.f p (q + 1)).hom ((K.dv p q (q + 1)).hom xy.1.1) -
          (L.dv p q (q + 1)).hom ((φ.f p q).hom xy.1.1 - (L.dv p (q - 1) q).hom xy.1.2) = 0
      rw [map_sub, L.dv_dv_apply, φ.comm_v_apply, sub_zero, sub_self]
  comm p q := by
    apply ModuleCat.hom_ext
    ext xy
    · exact K.comm_apply p (p + 1) q (q + 1) xy.1.1
    · change (φ.f (p + 1) q).hom ((K.dh p (p + 1) q).hom xy.1.1) -
          (L.dv (p + 1) (q - 1) q).hom ((L.dh p (p + 1) (q - 1)).hom xy.1.2) =
        (L.dh p (p + 1) q).hom ((φ.f p q).hom xy.1.1 - (L.dv p (q - 1) q).hom xy.1.2)
      rw [map_sub, φ.comm_h_apply, L.comm_apply]

/-- The columnwise mapping fibre, as a raw bicomplex. -/
noncomputable abbrev fib : RawBi.{v} R := φ.fiber.toRaw

/-- Surjectivity on the cohomology of every column, stated elementwise. -/
def ColSurj : Prop :=
  ∀ p q (y : L.M p q), (L.dv p q (q + 1)).hom y = 0 →
    ∃ x : K.M p q, (K.dv p q (q + 1)).hom x = 0 ∧
      ∃ z : L.M p (q - 1), (φ.f p q).hom x = y + (L.dv p (q - 1) q).hom z

/-- Injectivity on the cohomology of every column, stated elementwise. -/
def ColInj : Prop :=
  ∀ p q (x : K.M p q), (K.dv p q (q + 1)).hom x = 0 → ∀ z : L.M p (q - 1),
    (φ.f p q).hom x = (L.dv p (q - 1) q).hom z →
      ∃ w : K.M p (q - 1), (K.dv p (q - 1) q).hom w = x

theorem fib_dv_succ_apply (p q : ℕ) (xy : φ.fibSub p q) :
    (φ.fib.dv p q (q + 1)).hom xy =
      ⟨((K.dv p q (q + 1)).hom xy.1.1,
        (show L.M p q from (φ.f p q).hom xy.1.1 - (L.dv p (q - 1) q).hom xy.1.2)),
        fun h ↦ absurd h (Nat.succ_ne_zero q)⟩ := by
  change (φ.fiber.dvRaw p q (q + 1)).hom xy = _
  rw [SuccBi.dvRaw_succ]
  rfl

/-- In positive degree, a cocycle `(x, y)` of a column of the fibre of a columnwise
quasi-isomorphism is a coboundary. -/
theorem fib_exists_dv_eq_succ (hS : φ.ColSurj) (hI : φ.ColInj) {p q : ℕ}
    (xy : φ.fibSub p (q + 1)) (h1 : (K.dv p (q + 1) (q + 1 + 1)).hom xy.1.1 = 0)
    (h2 : (φ.f p (q + 1)).hom xy.1.1 = (L.dv p (q + 1 - 1) (q + 1)).hom xy.1.2) :
    ∃ res : φ.fibSub p q, (φ.fib.dv p q (q + 1)).hom res = xy := by
  obtain ⟨w, hw⟩ := hI p (q + 1) xy.1.1 h1 xy.1.2 h2
  let y0 : L.M p q := xy.1.2
  let w0 : K.M p q := w
  have hw0 : (K.dv p q (q + 1)).hom w0 = xy.1.1 := hw
  have h20 : (φ.f p (q + 1)).hom xy.1.1 = (L.dv p q (q + 1)).hom y0 := h2
  have hc : (L.dv p q (q + 1)).hom (y0 - (φ.f p q).hom w0) = 0 := by
    rw [map_sub, ← φ.comm_v_apply, hw0, h20, sub_self]
  obtain ⟨x'', hx'', z, hz⟩ := hS p q _ hc
  let z' : L.M p (q - 1) := if q = 0 then 0 else z
  have hz' : (L.dv p (q - 1) q).hom z' = (L.dv p (q - 1) q).hom z := by
    by_cases hq : q = 0
    · subst hq
      simp only [z', if_pos rfl, map_zero]
      exact (L.dv_shape_apply (by omega) z).symm
    · simp [z', hq]
  refine ⟨⟨(w0 + x'', z'), fun h ↦ by simp [z', h]⟩, ?_⟩
  erw [fib_dv_succ_apply]
  apply Subtype.ext
  apply Prod.ext
  · change (K.dv p q (q + 1)).hom (w0 + x'') = xy.1.1
    rw [map_add, hw0, hx'', add_zero]
  · change (φ.f p q).hom (w0 + x'') - (L.dv p (q - 1) q).hom z' = y0
    rw [hz', map_add, hz]
    abel

/-- The columns of the mapping fibre of a columnwise quasi-isomorphism are
exact. -/
theorem columnsExact_fib (hS : φ.ColSurj) (hI : φ.ColInj) : φ.fib.ColumnsExact := by
  intro p q xy hxy
  erw [fib_dv_succ_apply] at hxy
  have h1 : (K.dv p q (q + 1)).hom xy.1.1 = 0 := congrArg (fun t ↦ t.1.1) hxy
  have h2 : (φ.f p q).hom xy.1.1 - (L.dv p (q - 1) q).hom xy.1.2 = 0 :=
    congrArg (fun t ↦ t.1.2) hxy
  rw [sub_eq_zero] at h2
  rcases q with _ | q
  · -- degree zero: the element vanishes
    refine ⟨0, ?_⟩
    have hy : xy.1.2 = 0 := xy.2 rfl
    obtain ⟨w, hw⟩ := hI p 0 xy.1.1 h1 0 (by rw [h2, hy])
    have hx : xy.1.1 = 0 := by
      rw [← hw]
      exact K.dv_shape_apply (by omega) _
    rw [map_zero]
    apply Subtype.ext
    exact Prod.ext hx.symm hy.symm
  · exact φ.fib_exists_dv_eq_succ hS hI xy h1 h2

/-! ### Families of the fibre -/

/-- The `K`-part of a family of the fibre. -/
def famX (F : φ.fib.Fam) : K.Fam := fun pq ↦ (F pq).1.1

/-- The (sign-twisted, shifted) `L`-part of a family of the fibre. -/
def famY (F : φ.fib.Fam) : L.Fam := fun pq ↦ ((-1 : ℤ) ^ pq.1) • (F (pq.1, pq.2 + 1)).1.2

/-- Assemble a family of the fibre. -/
def famMk (x : K.Fam) (y : L.Fam) : φ.fib.Fam := fun pq ↦
  ⟨(x pq, if h : pq.2 = 0 then 0 else ((-1 : ℤ) ^ pq.1) • y (pq.1, pq.2 - 1)),
    fun h ↦ by simp [h]⟩

theorem famX_famMk (x : K.Fam) (y : L.Fam) : φ.famX (φ.famMk x y) = x := rfl

theorem famY_famMk (x : K.Fam) (y : L.Fam) : φ.famY (φ.famMk x y) = y := by
  funext ⟨p, q⟩
  change ((-1 : ℤ) ^ p) • (if h : q + 1 = 0 then 0 else ((-1 : ℤ) ^ p) • y (p, q + 1 - 1)) =
    y (p, q)
  rw [dif_neg (Nat.succ_ne_zero q)]
  exact neg_one_pow_smul_smul p _

theorem fam_ext {F G : φ.fib.Fam} (hX : φ.famX F = φ.famX G) (hY : φ.famY F = φ.famY G) :
    F = G := by
  funext ⟨p, q⟩
  apply Subtype.ext
  apply Prod.ext
  · exact congrFun hX (p, q)
  · rcases q with _ | q
    · rw [(F (p, 0)).2 rfl, (G (p, 0)).2 rfl]
    · have := congrArg (fun t ↦ ((-1 : ℤ) ^ p) • t) (congrFun hY (p, q))
      simpa only [famY, neg_one_pow_smul_smul] using this

theorem famX_zero : φ.famX 0 = 0 := rfl

theorem famY_zero : φ.famY 0 = 0 := by
  funext pq
  exact smul_zero _

theorem famX_mem {n : ℕ} {F : φ.fib.Fam} (hF : F ∈ φ.fib.tot n) : φ.famX F ∈ K.tot n := by
  intro pq h
  change (F pq).1.1 = 0
  rw [hF pq h]
  rfl

theorem famY_mem {n : ℕ} {F : φ.fib.Fam} (hF : F ∈ φ.fib.tot n) : φ.famY F ∈ L.tot (n - 1) := by
  rintro ⟨p, q⟩ h
  change ((-1 : ℤ) ^ p) • (F (p, q + 1)).1.2 = 0
  rw [hF (p, q + 1) (by simp only [ne_eq] at h ⊢; omega)]
  exact smul_zero _

theorem famY_eq_zero_of_mem_zero {F : φ.fib.Fam} (hF : F ∈ φ.fib.tot 0) : φ.famY F = 0 := by
  funext ⟨p, q⟩
  change ((-1 : ℤ) ^ p) • (F (p, q + 1)).1.2 = 0
  rw [hF (p, q + 1) (by simp)]
  exact smul_zero _

theorem famMk_mem {n m : ℕ} {x : K.Fam} {y : L.Fam} (hx : x ∈ K.tot n) (hy : y ∈ L.tot m)
    (hnm : n = m + 1) : φ.famMk x y ∈ φ.fib.tot n := by
  rintro ⟨p, q⟩ h
  apply Subtype.ext
  apply Prod.ext
  · exact hx (p, q) h
  · change (if h : q = 0 then 0 else ((-1 : ℤ) ^ p) • y (p, q - 1)) = 0
    split_ifs with hq
    · rfl
    · rw [hy (p, q - 1) (by simp only [ne_eq] at h ⊢; omega), smul_zero]

theorem famMk_zero_mem {n : ℕ} {x : K.Fam} (hx : x ∈ K.tot n) :
    φ.famMk x 0 ∈ φ.fib.tot n := by
  rintro ⟨p, q⟩ h
  apply Subtype.ext
  apply Prod.ext
  · exact hx (p, q) h
  · change (if h : q = 0 then 0 else ((-1 : ℤ) ^ p) • (0 : L.Fam) (p, q - 1)) = 0
    split_ifs <;> simp

/-- The `K`-part of the total differential of the fibre is the total
differential of `K`. -/
theorem famX_dRaw (F : φ.fib.Fam) : φ.famX (φ.fib.dRaw F) = K.dRaw (φ.famX F) := by
  funext ⟨p, q⟩
  change (φ.fib.dRaw F (p, q)).1.1 = _
  rw [dRaw_apply, dRaw_apply]
  change ((φ.fiber.dhRaw (p - 1) p q).hom (F (p - 1, q))).1.1 +
      ((-1 : ℤ) ^ p) • ((φ.fiber.dvRaw p (q - 1) q).hom (F (p, q - 1))).1.1 = _
  congr 1
  · rcases p with _ | p
    · rw [φ.fiber.dhRaw_ne _ (by omega), K.dh_shape_apply (by omega)]
      rfl
    · change ((φ.fiber.dhRaw p (p + 1) q).hom (F (p, q))).1.1 = _
      rw [SuccBi.dhRaw_succ]
      rfl
  · rcases q with _ | q
    · rw [φ.fiber.dvRaw_ne _ (by omega), K.dv_shape_apply (by omega)]
      rfl
    · change ((-1 : ℤ) ^ p) • ((φ.fiber.dvRaw p q (q + 1)).hom (F (p, q))).1.1 = _
      rw [SuccBi.dvRaw_succ]
      rfl

/-- The `L`-part of the total differential of the fibre of `(x, y)` is
`f x - d y`: the total complex of the fibre is the mapping fibre of the total
map. -/
theorem famY_dRaw (F : φ.fib.Fam) :
    φ.famY (φ.fib.dRaw F) = φ.famMap (φ.famX F) - L.dRaw (φ.famY F) := by
  funext ⟨p, q⟩
  change ((-1 : ℤ) ^ p) • (φ.fib.dRaw F (p, q + 1)).1.2 = _
  rw [dRaw_apply, Pi.sub_apply, famMap_apply, dRaw_apply]
  change ((-1 : ℤ) ^ p) • (((φ.fiber.dhRaw (p - 1) p (q + 1)).hom (F (p - 1, q + 1))).1.2 +
      ((-1 : ℤ) ^ p) • ((φ.fiber.dvRaw p q (q + 1)).hom (F (p, q))).1.2) = _
  rw [SuccBi.dvRaw_succ]
  change ((-1 : ℤ) ^ p) • ((show L.M p q from
      ((φ.fiber.dhRaw (p - 1) p (q + 1)).hom (F (p - 1, q + 1))).1.2) +
      ((-1 : ℤ) ^ p) • ((φ.f p q).hom (F (p, q)).1.1 - (L.dv p (q - 1) q).hom (F (p, q)).1.2)) =
    (φ.f p q).hom (F (p, q)).1.1 -
      ((L.dh (p - 1) p q).hom (((-1 : ℤ) ^ (p - 1)) • (F (p - 1, q + 1)).1.2) +
        ((-1 : ℤ) ^ p) • (L.dv p (q - 1) q).hom (((-1 : ℤ) ^ p) • (F (p, q - 1 + 1)).1.2))
  have hdh : ((-1 : ℤ) ^ p) • (show L.M p q from
      ((φ.fiber.dhRaw (p - 1) p (q + 1)).hom (F (p - 1, q + 1))).1.2) =
      -(L.dh (p - 1) p q).hom (((-1 : ℤ) ^ (p - 1)) • (F (p - 1, q + 1)).1.2) := by
    rcases p with _ | p
    · rw [φ.fiber.dhRaw_ne _ (by omega), L.dh_shape_apply (by omega), neg_zero]
      exact smul_zero _
    · change ((-1 : ℤ) ^ (p + 1)) • ((φ.fiber.dhRaw p (p + 1) (q + 1)).hom (F (p, q + 1))).1.2 =
        -(L.dh p (p + 1) q).hom (((-1 : ℤ) ^ p) • (F (p, q + 1)).1.2)
      rw [SuccBi.dhRaw_succ, map_zsmul, pow_succ]
      change ((-1 : ℤ) ^ p * -1) • (L.dh p (p + 1) q).hom (F (p, q + 1)).1.2 = _
      rw [mul_neg_one, neg_smul]
  have hdv : (L.dv p (q - 1) q).hom (F (p, q)).1.2 =
      (L.dv p (q - 1) q).hom (((-1 : ℤ) ^ p) • ((-1 : ℤ) ^ p) • (F (p, q - 1 + 1)).1.2) := by
    rw [neg_one_pow_smul_smul]
    rcases q with _ | q
    · rw [(F (p, 0)).2 rfl, L.dv_shape_apply (by omega)]
      exact (L.dv_shape_apply (by omega) _).symm
    · rfl
  rw [smul_add, hdh, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
    hdv, map_zsmul, map_zsmul]
  abel

/-- The family `famMk x y` of the fibre is a cocycle iff `x` is a cocycle and `f x = d y`. -/
theorem dRaw_famMk_eq_zero_iff (x : K.Fam) (y : L.Fam) :
    φ.fib.dRaw (φ.famMk x y) = 0 ↔ K.dRaw x = 0 ∧ φ.famMap x = L.dRaw y := by
  constructor
  · intro h
    have hX := congrArg φ.famX h
    have hY := congrArg φ.famY h
    rw [famX_dRaw, famX_famMk, famX_zero] at hX
    rw [famY_dRaw, famX_famMk, famY_famMk, famY_zero] at hY
    exact ⟨hX, sub_eq_zero.1 hY⟩
  · rintro ⟨hx, hy⟩
    apply φ.fam_ext
    · rw [famX_dRaw, famX_famMk, hx, famX_zero]
    · rw [famY_dRaw, famX_famMk, famY_famMk, hy, sub_self, famY_zero]

end Hom

/-- Surjectivity of `totMap φ` on cohomology, in elementwise form. -/
theorem totMap_elementwise_surj (hS : φ.ColSurj) (hI : φ.ColInj) (n : ℕ)
    (y : L.totComplex.X n) (hy : (L.totComplex.d n (n + 1)).hom y = 0) :
    ∃ x : K.totComplex.X n, (K.totComplex.d n (n + 1)).hom x = 0 ∧
      ∃ z : L.totComplex.X (n - 1),
        ((totMap φ).f n).hom x = y + (L.totComplex.d (n - 1) n).hom z := by
  have hd : L.dRaw (L.val y) = 0 := by
    rw [← totComplex_d_val, hy, val_zero]
  obtain ⟨G, hG, hGF⟩ := φ.fib.exists_dRaw_eq_of_columnsExact (φ.columnsExact_fib hS hI) n _
    (φ.famMk_mem (Submodule.zero_mem _) (Submodule.neg_mem _ (L.val_mem y)) rfl)
    ((φ.dRaw_famMk_eq_zero_iff _ _).2 ⟨map_zero _, by rw [map_zero, map_neg, hd, neg_zero]⟩)
  have hX : K.dRaw (φ.famX G) = 0 := by
    rw [← Hom.famX_dRaw, hGF, Hom.famX_famMk]
  have hY : φ.famMap (φ.famX G) - L.dRaw (φ.famY G) = -(L.val y) := by
    rw [← Hom.famY_dRaw, hGF, Hom.famY_famMk]
  refine ⟨K.ofFam (-(φ.famX G)) (Submodule.neg_mem _ (φ.famX_mem hG)), ?_, ?_⟩
  · apply K.val_injective
    rw [totComplex_d_val, val_ofFam, map_neg, hX, neg_zero]
    rfl
  · refine ⟨L.ofFam (-(φ.famY G)) (Submodule.neg_mem _ (φ.famY_mem hG)), ?_⟩
    apply L.val_injective
    rw [totMap_val, val_ofFam, map_neg]
    rcases n with _ | n
    · have h0 := φ.famY_eq_zero_of_mem_zero hG
      rw [L.totComplex_d_zero_zero]
      change _ = L.val y + 0
      rw [h0, map_zero, sub_zero] at hY
      rw [hY, neg_neg, add_zero]
    · change _ = L.val y + L.val ((L.totComplex.d n (n + 1)).hom _)
      rw [totComplex_d_val, val_ofFam, map_neg, ← neg_neg (L.val y), ← hY]
      abel

/-- Injectivity of `totMap φ` on cohomology, in elementwise form. -/
theorem totMap_elementwise_inj (hS : φ.ColSurj) (hI : φ.ColInj) (n : ℕ)
    (x : K.totComplex.X n) (hx : (K.totComplex.d n (n + 1)).hom x = 0)
    (z : L.totComplex.X (n - 1))
    (hz : ((totMap φ).f n).hom x = (L.totComplex.d (n - 1) n).hom z) :
    ∃ w : K.totComplex.X (n - 1), (K.totComplex.d (n - 1) n).hom w = x := by
  have hex := φ.columnsExact_fib hS hI
  have hdx : K.dRaw (K.val x) = 0 := by
    rw [← totComplex_d_val, hx, val_zero]
  rcases n with _ | m
  · have hfx : φ.famMap (K.val x) = 0 := by
      have := congrArg L.val hz
      rw [totMap_val, L.totComplex_d_zero_zero] at this
      exact this
    have hF0 := φ.fib.eq_zero_of_columnsExact_of_mem_tot_zero hex _ (φ.famMk_zero_mem (K.val_mem x))
      ((φ.dRaw_famMk_eq_zero_iff _ _).2 ⟨hdx, by rw [hfx, map_zero]⟩)
    have hx0 := congrArg φ.famX hF0
    rw [Hom.famX_famMk, Hom.famX_zero] at hx0
    refine ⟨0, K.val_injective ?_⟩
    rw [map_zero, hx0]
    rfl
  · have hfx : φ.famMap (K.val x) = L.dRaw (L.val z) := by
      have := congrArg L.val hz
      rw [totMap_val, L.totComplex_d_pred_val (m + 1) (by omega)] at this
      exact this
    obtain ⟨G, hG, hGF⟩ := φ.fib.exists_dRaw_eq_of_columnsExact hex m _
      (φ.famMk_mem (K.val_mem x) (L.val_mem z) rfl)
      ((φ.dRaw_famMk_eq_zero_iff _ _).2 ⟨hdx, hfx⟩)
    refine ⟨K.ofFam (φ.famX G) (φ.famX_mem hG), K.val_injective ?_⟩
    rw [K.totComplex_d_pred_val (m + 1) (by omega), val_ofFam, ← Hom.famX_dRaw, hGF,
      Hom.famX_famMk]

/-- **Columnwise quasi-isomorphisms induce quasi-isomorphisms of total
complexes** (first-quadrant bicomplexes of modules). -/
theorem totMap_quasiIso (hS : φ.ColSurj) (hI : φ.ColInj) : QuasiIso (totMap φ) :=
  quasiIso_of_elementwise _ (totMap_elementwise_surj φ hS hI) (totMap_elementwise_inj φ hS hI)

end RawBi

end AffineCrystalline.Homology
