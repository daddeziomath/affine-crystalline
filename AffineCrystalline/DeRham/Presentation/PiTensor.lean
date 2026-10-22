/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Tensor
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Presentation of the tensor product of a (finite) family of modules

Given presentations of a finite family of `R`-modules `M i`, we obtain a
presentation of `⨂[R] i, M i`. Its generators are families `(gᵢ)` of
generators, sent to `⨂ₜ gᵢ`; its relations are obtained by inserting a relation
of `M i₀` in a slot `i₀` while keeping generators fixed in the other slots. The
proof proceeds by induction on the cardinality of the index type, using the
isomorphism `⨂[R] i, M i ≃ M i₀ ⊗[R] ⨂[R] (i ≠ i₀), M i`.

## Main definitions

* `Module.Relations.piTensor`, `Module.Relations.Solution.piTensor`: the
  relations and the canonical solution in `⨂[R] i, M i`.
* `Module.Presentation.piTensor`: the resulting presentation.

## Main results

* `Module.Relations.Solution.IsPresentation.piTensor`: the canonical solution
  is a presentation when the index type is finite.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe w' w v u

open TensorProduct

section

variable {ι : Type*} (G : ι → Type*) [DecidableEq ι]
  (i : ι) (y : (∀ (j : ((Set.singleton i)ᶜ : Set ι)), G j))

/-- The embedding `G i ↪ ∀ j, G j` sending `x` to the family equal to `x` at `i`
and to `y` elsewhere. -/
def embedding : G i ↪ ∀ (j : ι), G j where
  toFun x j := if h : j = i then by rw [h]; exact x else y ⟨j, h⟩
  inj' x₁ x₂ h := by simpa using congr_fun h i

@[simp]
lemma embedding_apply_self (x : G i) : embedding G i y x i = x := dif_pos rfl

lemma embedding_apply_of_neq (x : G i) (j : ι) (h : j ≠ i) :
    embedding G i y x j = y ⟨j, h⟩ :=
  dif_neg h

end

section

variable {ι : Type*} {α : Type*} [DecidableEq ι]
  (i : ι) (y : (∀ (_ : ((Set.singleton i)ᶜ : Set ι)), α)) (x : α)

lemma comp_embedding {β : Type*} (g : α → β) :
    g.comp (embedding (fun _ ↦ α) i y x) =
      embedding (fun _ ↦ β) i (g.comp y) (g x) := by
  ext j
  by_cases h : j = i
  · subst h
    simp only [Function.comp_apply, embedding_apply_self]
  · simp [embedding_apply_of_neq _ _ _ _ _ h, Function.comp_apply]

lemma embedding_eq_update_embedding_zero [Zero α] :
    embedding (fun _ ↦ α) i y x = Function.update (embedding (fun _ ↦ α) i y 0) i x := by
  ext j
  by_cases h : j = i
  · subst h
    simp [Function.update, embedding_apply_self]
  · simp [Function.update, h, embedding_apply_of_neq _ _ _ _ _ h]

end

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀)

/-- Compatibility form of `subtypeNeLift`, indexed by a set complement. -/
def extendComplSingleton (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
lemma extendComplSingleton_self : extendComplSingleton i₀ f x i₀ = x := dif_pos rfl

lemma extendComplSingleton_of_neq (i : ι) (h : i ≠ i₀) :
    extendComplSingleton i₀ f x i = f ⟨i, h⟩ := dif_neg h

@[simp]
lemma extendCompSingleton_restriction (φ : ∀ i, M i) (i₀ : ι) :
    extendComplSingleton i₀ (fun i ↦ φ i) (φ i₀) = φ := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [extendComplSingleton_of_neq _ _ _ _ h]

end Function

namespace PiTensorProduct

/-- Compatibility alias for the orientation used in Riou's original proof. -/
noncomputable def equivTensorPiTensorComplSingleton
    (R : Type*) [CommRing R] {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (i₀ : ι) :
    (⨂[R] i, M i) ≃ₗ[R]
      (M i₀ ⊗[R] (⨂[R] (i : ((Set.singleton i₀)ᶜ : Set ι)), M i)) :=
  (PiTensorProduct.equivPiTensorComplSingletonTensor R M i₀).trans
    (TensorProduct.comm R _ _)

@[simp]
lemma equivTensorPiTensorComplSingleton_symm_tmul
    (R : Type*) [CommRing R] {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (i₀ : ι) (x : M i₀)
    (m : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) :
    (equivTensorPiTensorComplSingleton R M i₀).symm
      (x ⊗ₜ (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j)) =
      (⨂ₜ[R] i, Function.extendComplSingleton i₀ m x i) := by
  apply (equivTensorPiTensorComplSingleton R M i₀).injective
  rw [LinearEquiv.apply_symm_apply]
  change (x ⊗ₜ[R] (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j)) =
    (TensorProduct.comm R _ _)
      (PiTensorProduct.equivPiTensorComplSingletonTensor R M i₀
        (⨂ₜ[R] i, Function.extendComplSingleton i₀ m x i))
  rw [PiTensorProduct.equivPiTensorComplSingletonTensor_tprod]
  simp only [Function.extendComplSingleton_self, TensorProduct.comm_tmul]
  congr
  ext j
  rw [Function.extendComplSingleton_of_neq _ _ _ _ (by
    intro h
    apply j.2
    exact Set.mem_singleton_iff.mpr h)]

end PiTensorProduct

open PiTensorProduct
namespace Module

variable {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v} [DecidableEq ι]
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

namespace Relations

variable (relations : ι → Relations R)

@[simps]
noncomputable def piTensor : Relations R where
  G := ∀ i, (relations i).G
  R := Sigma (fun (i₀ : ι) ↦ (relations i₀).R ×
    (∀ (j : ((Set.singleton i₀)ᶜ : Set ι)), (relations j).G))
  relation := fun ⟨i₀, ⟨r, g⟩⟩ ↦
    Finsupp.embDomain (embedding (fun i ↦ (relations i).G) i₀ g) ((relations i₀).relation r)

namespace Solution

variable {relations} (solution : ∀ (i : ι), (relations i).Solution (M i))

@[simps]
noncomputable def piTensor : (Relations.piTensor relations).Solution (⨂[R] i, M i) where
  var g := ⨂ₜ[R] i, (solution i).var (g i)
  linearCombination_var_relation := by
    rintro ⟨i₀, r, g⟩
    dsimp
    let S := ⨂[R] (i : ((Set.singleton i₀)ᶜ : Set ι)), M i
    rw [Finsupp.linearCombination_embDomain]
    let φ : M i₀ →ₗ[R] ⨂[R] i, M i :=
      (equivTensorPiTensorComplSingleton R M i₀).symm.toLinearMap.comp
        ((TensorProduct.mk (R := R) (M := M i₀) (N := S)).flip (⨂ₜ[R] i, (solution i).var (g i)))
    convert (((solution i₀).postcomp φ).linearCombination_var_relation r)
    ext g
    dsimp [φ]
    erw [equivTensorPiTensorComplSingleton_symm_tmul]
    congr
    ext i
    by_cases hi : i = i₀
    · subst hi
      simp
    · rw [embedding_apply_of_neq, Function.extendComplSingleton_of_neq _ _ _ _ hi]

namespace IsPresentation

variable {solution} (h : ∀ i, (solution i).IsPresentation)

namespace piTensor

lemma isPresentation_of_isEmpty [hι : IsEmpty ι] :
    (Solution.piTensor solution).IsPresentation :=
  IsPresentationCore.isPresentation
    { desc := fun s ↦ PiTensorProduct.lift
        { toFun := fun _ ↦ s.var (IsEmpty.elim hι)
          map_update_add' := fun _ ↦ IsEmpty.elim hι
          map_update_smul' := fun _ ↦ IsEmpty.elim hι }
      postcomp_desc := fun s ↦ by
        ext x
        dsimp
        simp only [lift.tprod, MultilinearMap.coe_mk]
        congr
        funext i
        exact IsEmpty.elim hι i
      postcomp_injective := fun {N _ _ f f'} h ↦ by
        ext x
        have := Solution.congr_var h (IsEmpty.elim hι)
        simp only [postcomp_var, piTensor_var] at this
        simp only [LinearMap.compMultilinearMap_apply]
        convert this }

variable (i₀ : ι)
  (h₀ : (Solution.piTensor (fun (i : ((Set.singleton i₀)ᶜ : Set ι)) ↦ solution i)).IsPresentation)

namespace isPresentationCore_induction_step

variable {N : Type w'} [AddCommGroup N] [Module R N]
  (s : (Relations.piTensor relations).Solution N)

@[simps! G R]
noncomputable def presInd : Presentation R (⨂[R] (i : ι), M i) :=
  Presentation.ofLinearEquiv
    (Presentation.tensor (.ofIsPresentation (h i₀)) (.ofIsPresentation h₀))
    (equivTensorPiTensorComplSingleton R M i₀).symm

lemma presInd_var (g₀ : (relations i₀).G)
    (g : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), (relations i).G) :
      (presInd h i₀ h₀).var ⟨g₀, g⟩ =
      ⨂ₜ[R] (i : ι), (solution i).var
        (Function.extendComplSingleton (M := fun i ↦ (relations i).G) i₀ g g₀ i) := by
  dsimp [presInd]
  erw [equivTensorPiTensorComplSingleton_symm_tmul]
  congr
  ext i
  by_cases hi : i = i₀
  · subst hi
    simp
  · simp only [Function.extendComplSingleton_of_neq _ _ _ _ hi]

lemma eq_presInd_var (g : ∀ i, (relations i).G) :
    (⨂ₜ[R] (i : ι), (solution i).var (g i)) =
      (presInd h i₀ h₀).var ⟨g i₀, fun i ↦ g i⟩ := by
  rw [presInd_var, Function.extendCompSingleton_restriction]

end isPresentationCore_induction_step

open isPresentationCore_induction_step in
include h h₀ in
noncomputable def isPresentationCore_induction_step :
    Solution.IsPresentationCore.{w'} (Solution.piTensor solution) where
  desc {N _ _ } s := (presInd h i₀ h₀).desc
    { var := fun x ↦ s.var (Function.extendComplSingleton i₀
        (fun i ↦ show (relations i).G from x.2 i)
        (show (relations i₀).G from x.1))
      linearCombination_var_relation := by
        rintro (⟨r₀, g⟩ | ⟨g₀, ⟨⟨i₁, h₁⟩, r₁, g⟩⟩)
        · change (∀ i : ((Set.singleton i₀)ᶜ : Set ι), (relations i).G) at g
          have hs := s.linearCombination_var_relation ⟨i₀, r₀, g⟩
          simp only [presInd, Presentation.ofLinearEquiv,
            Presentation.ofIsPresentation, Presentation.tensor]
          rw [Finsupp.linearCombination_embDomain]
          change (Finsupp.linearCombination R
            (fun x : (relations i₀).G =>
              s.var (Function.extendComplSingleton i₀ g x))
              ((relations i₀).relation r₀)) = 0
          have hfun :
              (fun x : (relations i₀).G =>
                s.var (Function.extendComplSingleton i₀ g x)) =
              (fun x : (relations i₀).G =>
                s.var (embedding (fun i => (relations i).G) i₀ g x)) := by
            funext x
            congr 1
          rw [hfun]
          simp only [piTensor_relation, Finsupp.linearCombination_embDomain] at hs
          exact hs
        · change (relations i₀).G at g₀
          have h₁ne : i₁ ≠ i₀ := by
            intro h
            apply h₁
            exact Set.mem_singleton_iff.mpr h
          have := s.linearCombination_var_relation
            ⟨i₁, r₁, Function.extendComplSingleton
              (M := fun (i : ({i₁}ᶜ : Set ι)) ↦ (relations i).G)
                ⟨i₀, by
                  rw [Set.mem_compl_iff]
                  intro hi
                  exact h₁ne.symm (Set.mem_singleton_iff.mp hi)⟩
                (fun ⟨⟨i, hi₁⟩, hi₀⟩ ↦ g ⟨⟨i, by
                  rw [Set.mem_compl_iff] at hi₀ ⊢
                  intro hi
                  apply hi₀
                  have hiEq : i = i₀ := Set.mem_singleton_iff.mp hi
                  exact Set.mem_singleton_iff.mpr (Subtype.ext hiEq)⟩, (by
                  rw [Set.mem_compl_iff]
                  intro hi
                  have hiEq : i = i₁ := congrArg Subtype.val
                    (Set.mem_singleton_iff.mp hi)
                  apply hi₁
                  exact Set.mem_singleton_iff.mpr hiEq)⟩) g₀⟩
          dsimp at this
          rw [Finsupp.linearCombination_embDomain] at this
          dsimp [presInd]
          rw [Finsupp.linearCombination_embDomain, Finsupp.linearCombination_embDomain, ← this]
          apply congrArg (fun f : (relations i₁).G → N =>
            Finsupp.linearCombination R f ((relations i₁).relation r₁))
          funext g₁
          dsimp
          congr 1
          funext i
          by_cases hi₀ : i = i₀
          · subst hi₀
            rw [Function.extendComplSingleton_self,
              embedding_apply_of_neq _ _ _ _ _ h₁ne.symm,
              Function.extendComplSingleton_self]
          · by_cases hi₁ : i = i₁
            · subst hi₁
              rw [embedding_apply_self, Function.extendComplSingleton_of_neq _ _ _ _ h₁ne,
                embedding_apply_self]
            · rw [Function.extendComplSingleton_of_neq _ _ _ _ hi₀,
                embedding_apply_of_neq _ _ _ _ _ (by simpa using hi₁),
                embedding_apply_of_neq _ _ _ _ _ hi₁,
                Function.extendComplSingleton_of_neq _ _ _ _ (by simpa using hi₀)]
            }
  postcomp_desc s:= by
    ext g
    dsimp
    rw [eq_presInd_var h i₀ h₀, desc_var]
    dsimp
    rw [Function.extendCompSingleton_restriction]
  postcomp_injective h' := (presInd h i₀ h₀).postcomp_injective (by
    ext ⟨g₀, g⟩
    dsimp
    rw [presInd_var]
    exact Solution.congr_var h' (Function.extendComplSingleton i₀ g g₀))

include h h₀ in
lemma isPresentation_induction_step :
    (Solution.piTensor solution).IsPresentation :=
  (isPresentationCore_induction_step h i₀ h₀).isPresentation

end piTensor

include h in
lemma piTensor [Finite ι] : (Solution.piTensor solution).IsPresentation := by
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  revert ι
  induction n with
  | zero =>
      intro ι M _ _ _ relations solution _ _ h₀
      have : IsEmpty ι := by
        rw [Nat.card_eq_zero] at h₀
        have := not_finite_iff_infinite (α := ι)
        tauto
      apply piTensor.isPresentation_of_isEmpty
  | succ n hn =>
      intro ι M _ _ _ relations solution h _ hn'
      let i₀ := ((Nat.card_ne_zero (α := ι)).1 (by omega)).1.some
      refine piTensor.isPresentation_induction_step h i₀ (hn (fun _ ↦ h _) ?_)
      have := Fintype.ofFinite ι
      rw [← add_left_inj 1, ← hn', Nat.card_eq_fintype_card (α := ι),
        ← Finset.card_compl_add_card {i₀}, Finset.card_singleton,
        Nat.card_eq_card_finite_toFinset (Set.toFinite _)]
      congr
      ext i
      simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff, Finset.mem_compl,
        Finset.mem_singleton]
      rfl

end IsPresentation

end Solution

end Relations

@[simps! G R var]
noncomputable def Presentation.piTensor [Finite ι] (pres : ∀ i, Presentation R (M i)) :
    Presentation R (⨂[R] i, M i) :=
  Presentation.ofIsPresentation (.piTensor (fun i ↦ (pres i).toIsPresentation))

end Module
