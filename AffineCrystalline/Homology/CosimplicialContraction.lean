/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Homology.Elementwise
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Cosimplicial contractions

A *cosimplicial contraction* of a cosimplicial object `X` in a preadditive
category is a family of endomorphisms `h n α : X[n] ⟶ X[n]`, indexed by the
maps `α : [n] ⟶ [1]` and natural in `([n], α)`, such that `h n α = 0` for the
constant map `α = 0` and `h n α = 𝟙` for the constant map `α = 1`.  This is a
cosimplicial homotopy between `0` and `𝟙` in the sense of Stacks, Tag 019U.
Since the definition only involves composition with the structure maps, it is
preserved by any functor applied levelwise (for instance exterior powers).

Writing `H_t = h (k ↦ [t ≤ k])`, the maps `H_{j+1} ≫ σ_j : X[n+1] ⟶ X[n]` form a
simplicial homotopy, in the sense of Mathlib's `SimplicialObject.Homotopy`,
between `0` and `𝟙` on the opposite simplicial object `X.op`.  Mathlib's
`SimplicialObject.Homotopy.toChainHomotopy` turns it into a chain homotopy on the
alternating face complex, which yields a contracting homotopy of the
alternating coface complex of `X`.

## Main definitions

* `AffineCrystalline.Homology.stepHom`: the maps `[n] ⟶ [1]`, `k ↦ [t ≤ k]`.
* `AffineCrystalline.Homology.CosimplicialContraction`: cosimplicial
  contractions.
* `CosimplicialContraction.toSimplicialHomotopy`: the associated simplicial
  homotopy from `0` to `𝟙` on `X.op`.
* `CosimplicialContraction.contr`: the contracting homotopy
  `X[n+1] ⟶ X[n]` of the alternating coface complex.

## Main results

* `CosimplicialContraction.objD_zero_comp_contr`,
  `CosimplicialContraction.contr_comp_objD_add`: the contracting homotopy
  identities `d⁰ ≫ s⁰ = 𝟙` and `s ≫ d + d ≫ s = 𝟙`.
* `CosimplicialContraction.exactAt`: the alternating coface complex of a
  cosimplicial module admitting a cosimplicial contraction is exact in every
  degree.

## References

* [Stacks Project, Tag 019U](https://stacks.math.columbia.edu/tag/019U)
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u w

namespace AffineCrystalline.Homology

/-- The map `[n] ⟶ [1]` sending `k` to `1` if `t ≤ k` and to `0` otherwise. -/
def stepHom (n t : ℕ) : ⦋n⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom
    ⟨fun k : Fin (n + 1) ↦ if t ≤ (k : ℕ) then (1 : Fin 2) else 0, by
      intro a b hab
      dsimp only
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (le_trans h1 (Fin.le_def.mp hab)) h2
      · exact Fin.zero_le _
      · exact le_rfl⟩

theorem val_stepHom_apply (n t : ℕ) (k : Fin (n + 1)) :
    ((stepHom n t).toOrderHom k : ℕ) = if t ≤ (k : ℕ) then 1 else 0 := by
  change ((if t ≤ (k : ℕ) then (1 : Fin 2) else 0 : Fin 2) : ℕ) = _
  split_ifs <;> rfl

/-- The coface `δ i` skips the value `i`. -/
theorem val_δ_apply {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    ((SimplexCategory.δ i).toOrderHom k : ℕ) = if (k : ℕ) < i then (k : ℕ) else (k : ℕ) + 1 := by
  simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp

/-- The codegeneracy `σ i` repeats the value `i`. -/
theorem val_σ_apply {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) :
    ((SimplexCategory.σ i).toOrderHom k : ℕ) = if (k : ℕ) ≤ i then (k : ℕ) else (k : ℕ) - 1 := by
  simp only [SimplexCategory.σ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change ((i.predAbove k : Fin (n + 1)) : ℕ) = _
  split_ifs with h
  · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]; simp
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]; simp

theorem val_const_apply (n : ℕ) (a : Fin 2) (k : Fin (n + 1)) :
    ((SimplexCategory.const ⦋n⦌ ⦋1⦌ a).toOrderHom k : ℕ) = a := rfl

/-- `stepHom n 0` is the constant map with value `1`. -/
theorem stepHom_zero (n : ℕ) : stepHom n 0 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
  ext k : 3
  rw [Fin.ext_iff, val_stepHom_apply, val_const_apply]
  simp

/-- `stepHom n (n + 1)` is the constant map with value `0`. -/
theorem stepHom_last (n : ℕ) : stepHom n (n + 1) = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
  ext k : 3
  have : (k : ℕ) < n + 1 := k.isLt
  rw [Fin.ext_iff, val_stepHom_apply, val_const_apply]
  simp only [Fin.val_zero]
  split_ifs <;> omega

theorem δ_comp_stepHom_of_le {n : ℕ} (i : Fin (n + 2)) (t : ℕ) (h : t ≤ i) :
    SimplexCategory.δ i ≫ stepHom (n + 1) t = stepHom n t := by
  ext k : 3
  rw [Fin.ext_iff, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_stepHom_apply, val_stepHom_apply]
  have := val_δ_apply i k
  split_ifs at this ⊢ <;> omega

theorem δ_comp_stepHom_of_lt {n : ℕ} (i : Fin (n + 2)) (t : ℕ) (h : (i : ℕ) < t) :
    SimplexCategory.δ i ≫ stepHom (n + 1) t = stepHom n (t - 1) := by
  ext k : 3
  rw [Fin.ext_iff, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_stepHom_apply, val_stepHom_apply]
  have := val_δ_apply i k
  split_ifs at this ⊢ <;> omega

theorem σ_comp_stepHom_of_le {n : ℕ} (j : Fin (n + 1)) (t : ℕ) (h : t ≤ j) :
    SimplexCategory.σ j ≫ stepHom n t = stepHom (n + 1) t := by
  ext k : 3
  rw [Fin.ext_iff, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_stepHom_apply, val_stepHom_apply]
  have := val_σ_apply j k
  split_ifs at this ⊢ <;> omega

theorem σ_comp_stepHom_of_lt {n : ℕ} (j : Fin (n + 1)) (t : ℕ) (h : (j : ℕ) < t) :
    SimplexCategory.σ j ≫ stepHom n t = stepHom (n + 1) (t + 1) := by
  ext k : 3
  rw [Fin.ext_iff, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_stepHom_apply, val_stepHom_apply]
  have := val_σ_apply j k
  split_ifs at this ⊢ <;> omega

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A cosimplicial contraction of `X`: a cosimplicial homotopy from `0` to `𝟙`,
given by endomorphisms `h n α` of `X[n]` indexed by `α : [n] ⟶ [1]`. -/
structure CosimplicialContraction (X : CosimplicialObject C) where
  /-- The homotopy operators. -/
  h : ∀ n : ℕ, (⦋n⦌ ⟶ ⦋1⦌) → (X.obj ⦋n⦌ ⟶ X.obj ⦋n⦌)
  nat : ∀ {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (α : ⦋n⦌ ⟶ ⦋1⦌),
    h m (f ≫ α) ≫ X.map f = X.map f ≫ h n α
  zero : ∀ n, h n (SimplexCategory.const ⦋n⦌ ⦋1⦌ 0) = 0
  one : ∀ n, h n (SimplexCategory.const ⦋n⦌ ⦋1⦌ 1) = 𝟙 _

namespace CosimplicialContraction

variable {X : CosimplicialObject C} (H : CosimplicialContraction X)

/-- The endomorphism `H_t = h (stepHom n t)` of `X[n]`. -/
def step (n t : ℕ) : X.obj ⦋n⦌ ⟶ X.obj ⦋n⦌ := H.h n (stepHom n t)

theorem step_zero (n : ℕ) : H.step n 0 = 𝟙 _ := by
  rw [step, stepHom_zero, H.one]

theorem step_last (n : ℕ) : H.step n (n + 1) = 0 := by
  rw [step, stepHom_last, H.zero]

theorem δ_step_of_le {n : ℕ} (i : Fin (n + 2)) (t : ℕ) (h : t ≤ i) :
    X.δ i ≫ H.step (n + 1) t = H.step n t ≫ X.δ i := by
  have := H.nat (SimplexCategory.δ i) (stepHom (n + 1) t)
  rw [δ_comp_stepHom_of_le i t h] at this
  exact this.symm

theorem δ_step_of_lt {n : ℕ} (i : Fin (n + 2)) (t : ℕ) (h : (i : ℕ) < t) :
    X.δ i ≫ H.step (n + 1) t = H.step n (t - 1) ≫ X.δ i := by
  have := H.nat (SimplexCategory.δ i) (stepHom (n + 1) t)
  rw [δ_comp_stepHom_of_lt i t h] at this
  exact this.symm

theorem σ_step_of_le {n : ℕ} (j : Fin (n + 1)) (t : ℕ) (h : t ≤ j) :
    X.σ j ≫ H.step n t = H.step (n + 1) t ≫ X.σ j := by
  have := H.nat (SimplexCategory.σ j) (stepHom n t)
  rw [σ_comp_stepHom_of_le j t h] at this
  exact this.symm

theorem σ_step_of_lt {n : ℕ} (j : Fin (n + 1)) (t : ℕ) (h : (j : ℕ) < t) :
    X.σ j ≫ H.step n t = H.step (n + 1) (t + 1) ≫ X.σ j := by
  have := H.nat (SimplexCategory.σ j) (stepHom n t)
  rw [σ_comp_stepHom_of_lt j t h] at this
  exact this.symm

/-- The components `k_j = H_{j+1} ≫ σ_j : X[n+1] ⟶ X[n]` of the simplicial
homotopy. -/
def homotopyComponent (n : ℕ) (j : Fin (n + 1)) : X.obj ⦋n + 1⦌ ⟶ X.obj ⦋n⦌ :=
  H.step (n + 1) (j + 1) ≫ X.σ j

/-- First boundary identity of the homotopy: `δ⁰ ≫ k₀ = 𝟙`. -/
theorem δ_zero_comp_homotopyComponent (n : ℕ) :
    X.δ 0 ≫ H.homotopyComponent n 0 = 𝟙 _ := by
  rw [homotopyComponent, ← Category.assoc, H.δ_step_of_lt 0 _ (by simp), Category.assoc,
    show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl, X.δ_comp_σ_self]
  simp [H.step_zero]

/-- Second boundary identity of the homotopy: `δ_{n+1} ≫ k_n = 0`. -/
theorem δ_last_comp_homotopyComponent_last (n : ℕ) :
    X.δ (Fin.last (n + 1)) ≫ H.homotopyComponent n (Fin.last n) = 0 := by
  rw [homotopyComponent, ← Category.assoc, H.δ_step_of_le _ _ (by simp), Category.assoc,
    show Fin.last (n + 1) = (Fin.last n).succ from rfl, X.δ_comp_σ_succ, Fin.val_last,
    H.step_last]
  simp

/-- Commutation of the homotopy with the cofaces `δ i`, `i ≤ j`. -/
theorem δ_castSucc_comp_homotopyComponent_succ_of_le {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    X.δ i.castSucc ≫ H.homotopyComponent (n + 1) j.succ = H.homotopyComponent n j ≫ X.δ i := by
  have hij' := Fin.le_def.1 hij
  rw [Fin.val_castSucc] at hij'
  rw [homotopyComponent, homotopyComponent, ← Category.assoc,
    H.δ_step_of_lt _ _ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega), Category.assoc,
    X.δ_comp_σ_of_le hij]
  simp

/-- The two components `k_{j+1}` and `k_j` agree after the coface `δ_{j+1}`. -/
theorem δ_castSucc_succ_comp_homotopyComponent_succ {n : ℕ} (j : Fin (n + 1)) :
    X.δ j.castSucc.succ ≫ H.homotopyComponent (n + 1) j.succ =
      X.δ j.castSucc.succ ≫ H.homotopyComponent (n + 1) j.castSucc := by
  rw [homotopyComponent, homotopyComponent, ← Category.assoc, H.δ_step_of_lt _ _ (by simp),
    Category.assoc, ← Category.assoc (X.δ _), H.δ_step_of_le _ _ (by simp), Category.assoc,
    show j.castSucc.succ = j.succ.castSucc from rfl, X.δ_comp_σ_self,
    show j.succ.castSucc = j.castSucc.succ from rfl, X.δ_comp_σ_succ]
  simp

/-- Commutation of the homotopy with the cofaces `δ (i + 1)`, `j < i`. -/
theorem δ_succ_comp_homotopyComponent_castSucc_of_lt {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) :
    X.δ i.succ ≫ H.homotopyComponent (n + 1) j.castSucc = H.homotopyComponent n j ≫ X.δ i := by
  have hji' := Fin.lt_def.1 hji
  rw [Fin.val_castSucc] at hji'
  rw [homotopyComponent, homotopyComponent, ← Category.assoc,
    H.δ_step_of_le _ _ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega), Category.assoc,
    X.δ_comp_σ_of_gt hji]
  simp

/-- Commutation of the homotopy with the codegeneracies `σ i`, `i ≤ j`. -/
theorem σ_castSucc_comp_homotopyComponent_of_le {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    X.σ i.castSucc ≫ H.homotopyComponent n j = H.homotopyComponent (n + 1) j.succ ≫ X.σ i := by
  rw [homotopyComponent, homotopyComponent, ← Category.assoc, H.σ_step_of_lt _ _ (by
      rw [Fin.le_def] at hij
      simp only [Fin.val_castSucc]
      omega), Category.assoc, X.σ_comp_σ hij]
  simp

/-- Commutation of the homotopy with the codegeneracies `σ (i + 1)`, `j ≤ i`. -/
theorem σ_succ_comp_homotopyComponent_of_le {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    X.σ i.succ ≫ H.homotopyComponent n j = H.homotopyComponent (n + 1) j.castSucc ≫ X.σ i := by
  rw [homotopyComponent, homotopyComponent, ← Category.assoc, H.σ_step_of_le _ _ (by
      rw [Fin.le_def] at hji
      simp only [Fin.val_succ]
      omega), Category.assoc, ← X.σ_comp_σ hji]
  simp

/-- The simplicial homotopy from `0` to `𝟙` on the opposite simplicial object
`X.op` associated with a cosimplicial contraction. -/
def toSimplicialHomotopy :
    SimplicialObject.Homotopy (X := X.op) (Y := X.op) 0 (𝟙 _) where
  h {n} j := (H.homotopyComponent n j).op
  h_zero_comp_δ_zero n := Quiver.Hom.unop_inj (H.δ_zero_comp_homotopyComponent n)
  h_last_comp_δ_last n := Quiver.Hom.unop_inj (H.δ_last_comp_homotopyComponent_last n)
  h_succ_comp_δ_castSucc_of_lt i j hij :=
    Quiver.Hom.unop_inj (H.δ_castSucc_comp_homotopyComponent_succ_of_le i j hij)
  h_succ_comp_δ_castSucc_succ j :=
    Quiver.Hom.unop_inj (H.δ_castSucc_succ_comp_homotopyComponent_succ j)
  h_castSucc_comp_δ_succ_of_lt i j hji :=
    Quiver.Hom.unop_inj (H.δ_succ_comp_homotopyComponent_castSucc_of_lt i j hji)
  h_comp_σ_castSucc_of_le i j hij :=
    Quiver.Hom.unop_inj (H.σ_castSucc_comp_homotopyComponent_of_le i j hij)
  h_comp_σ_succ_of_lt i j hji :=
    Quiver.Hom.unop_inj (H.σ_succ_comp_homotopyComponent_of_le i j hji)

end CosimplicialContraction

end AffineCrystalline.Homology

namespace AffineCrystalline.Homology.CosimplicialContraction

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X : CosimplicialObject C} (H : CosimplicialContraction X)

/-- The contracting homotopy `X[n+1] ⟶ X[n]` of the alternating coface complex. -/
noncomputable def contr (n : ℕ) : X.obj ⦋n + 1⦌ ⟶ X.obj ⦋n⦌ :=
  -(SimplicialObject.Homotopy.ToChainHomotopy.hom H.toSimplicialHomotopy n (n + 1)).unop

/-- The differential of the alternating face complex of `X.op`, in terms of
`AlgebraicTopology.AlternatingFaceMapComplex.objD`. -/
theorem d_eq_objD (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex Cᵒᵖ).obj X.op).d (n + 1) n =
      AlgebraicTopology.AlternatingFaceMapComplex.objD
        ((cosimplicialSimplicialEquiv C).functor.obj (op X)) n :=
  AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n

/-- The contracting homotopy identity in degree `0`. -/
theorem objD_zero_comp_contr :
    AlgebraicTopology.AlternatingCofaceMapComplex.objD X 0 ≫ H.contr 0 = 𝟙 _ := by
  have h := (H.toSimplicialHomotopy.toChainHomotopy).comm 0
  rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add] at h
  have h' := congrArg Quiver.Hom.unop h
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f, NatTrans.app_zero,
    NatTrans.id_app, unop_add, unop_comp, unop_zero] at h'
  rw [d_eq_objD] at h'
  have key := eq_neg_of_add_eq_zero_left h'.symm
  rw [contr, Preadditive.comp_neg, AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d]
  erw [key]
  simp
  rfl

/-- The contracting homotopy identity in positive degrees. -/
theorem contr_comp_objD_add (n : ℕ) :
    H.contr n ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD X n +
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X (n + 1) ≫ H.contr (n + 1) = 𝟙 _ := by
  have h := (H.toSimplicialHomotopy.toChainHomotopy).comm (n + 1)
  rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp)] at h
  have h' := congrArg Quiver.Hom.unop h
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f, NatTrans.app_zero,
    NatTrans.id_app, unop_add, unop_comp, unop_zero] at h'
  rw [d_eq_objD, d_eq_objD] at h'
  have key := eq_neg_of_add_eq_zero_left h'.symm
  rw [contr, contr, Preadditive.comp_neg, Preadditive.neg_comp,
    AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d]
  rw [← neg_add]
  erw [key]
  simp
  rfl

/-- **Exactness of contractible cosimplicial modules.**  The alternating coface
complex of a cosimplicial module admitting a cosimplicial contraction is exact
in every degree. -/
theorem exactAt {R : Type w} [Ring R] {X : CosimplicialObject (ModuleCat.{v} R)}
    (H : CosimplicialContraction X) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R)).obj X).ExactAt n := by
  rw [exactAt_iff_elementwise]
  intro x hx
  have hd : ∀ m, ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R)).obj X).d
      m (m + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD X m := fun m ↦ by
    simp [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rcases n with _ | m
  · refine ⟨0, ?_⟩
    have h0 :
        (H.contr 0).hom ((AlgebraicTopology.AlternatingCofaceMapComplex.objD X 0).hom x) = x :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom H.objD_zero_comp_contr) x
    rw [hd 0] at hx
    erw [hx, map_zero] at h0
    rw [map_zero]
    exact h0
  · refine ⟨(H.contr m).hom x, ?_⟩
    have h1 : (AlgebraicTopology.AlternatingCofaceMapComplex.objD X m).hom ((H.contr m).hom x) +
        (H.contr (m + 1)).hom ((AlgebraicTopology.AlternatingCofaceMapComplex.objD X (m + 1)).hom x)
        = x :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (H.contr_comp_objD_add m)) x
    rw [hd (m + 1)] at hx
    erw [hx, map_zero, add_zero] at h1
    change ((((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v} R)).obj X).d
      m (m + 1)).hom ((H.contr m).hom x)) = x
    rw [hd m]
    exact h1

end AffineCrystalline.Homology.CosimplicialContraction
