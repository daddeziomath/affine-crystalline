/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.Presentation.Tautological
import AffineCrystalline.DeRham.Presentation.ExteriorPowerExplicit
import Mathlib.Algebra.Module.Presentation.RestrictScalars
import Mathlib.Algebra.Module.Presentation.Tautological
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The algebraic de Rham complex via presentations

Following J. Riou's construction of the de Rham complex through presentations
of modules, we construct the algebraic de Rham complex
`B → Ω[B⁄A] → ⋀[B]^2 Ω[B⁄A] → ⋯` of a commutative `A`-algebra `B`, as a cochain
complex of `A`-modules.

The tautological presentation of the `A`-algebra `B`, with one generator `[b]`
for each `b : B`, induces a `B`-linear presentation of `Ω[B⁄A]` with generators
`db`, hence a `B`-linear presentation `presentationDifferentialsUp n` of
`⋀[B]^n Ω[B⁄A]` with generators `db₁ ∧ ⋯ ∧ dbₙ`. Restricting scalars along the
tautological `A`-linear presentation of `B` gives an `A`-linear presentation
`presentationDifferentialsDown n` with generators `b₀ db₁ ∧ ⋯ ∧ dbₙ`. The
differential `DeRhamComplex.d n` is the `A`-linear map defined on these
generators by
`b₀ db₁ ∧ ⋯ ∧ dbₙ ↦ db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ`;
most of the work consists in checking that this assignment respects all the
relations of the presentation. The identity `d ∘ d = 0` follows since
`d (db₀ ∧ ⋯ ∧ dbₙ) = d1 ∧ db₀ ∧ ⋯ ∧ dbₙ = 0`.

## Main definitions

* `KaehlerDifferential.presentation A B`: the presentation of `Ω[B⁄A]` induced
  by the tautological presentation of `B`.
* `DeRhamComplex.presentationDifferentialsUp A B n`: the `B`-linear
  presentation of `⋀[B]^n Ω[B⁄A]`.
* `DeRhamComplex.presentationDifferentialsDown A B n`: the `A`-linear
  presentation obtained by restriction of scalars.
* `DeRhamComplex.d A B n`: the de Rham differential
  `⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]`.
* `deRhamComplex A B`: the de Rham complex as a cochain complex of `A`-modules.

## Main results

* `DeRhamComplex.d_var`: the generator formula.
* `DeRhamComplex.d_d`: `d (n + 1) ∘ d n = 0`.

## References

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
-/

-- The verification that the restriction-of-scalars data and the de Rham differential respect
-- the relations of the presentations (the `dsimp`, `erw` and `change` steps below) unfolds
-- the structure instances defining these presentations; it relies on the backward-compatible
-- behaviour of definitional unfolding restored by these two options, and fails without them.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

open Function
open ExteriorAlgebra

namespace Module.Presentation

@[simp]
lemma finsupp_π {A N ι : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [DecidableEq ι] [DecidableEq N] (pres : Presentation A N) (i : ι) (g : pres.G) :
    (finsupp pres ι).π (Finsupp.single ⟨i, g⟩ 1) =
      Finsupp.single i (pres.var g) := by
  rw [Module.Relations.Solution.π_single, finsupp_var]

lemma finsupp_π_add {A N ι : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [DecidableEq ι] [DecidableEq N] (pres : Presentation A N)
    (x y : (finsupp pres ι).G →₀ A) :
    (finsupp pres ι).π (x + y) = (finsupp pres ι).π x + (finsupp pres ι).π y :=
  map_add _ _ _

lemma finsupp_π_sub {A N ι : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [DecidableEq ι] [DecidableEq N] (pres : Presentation A N)
    (x y : (finsupp pres ι).G →₀ A) :
    (finsupp pres ι).π (x - y) = (finsupp pres ι).π x - (finsupp pres ι).π y :=
  map_sub _ _ _

lemma finsupp_π_neg {A N ι : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [DecidableEq ι] [DecidableEq N] (pres : Presentation A N)
    (x : (finsupp pres ι).G →₀ A) :
    (finsupp pres ι).π (-x) = -(finsupp pres ι).π x :=
  map_neg _ _

end Module.Presentation

namespace Finsupp

@[simp]
lemma embDomain_sub {R α β : Type*} [Ring R] (f : α ↪ β)
    (x y : α →₀ R) : embDomain f (x - y) = embDomain f x - embDomain f y :=
  (embDomain.addMonoidHom f).map_sub x y

@[simp]
lemma embDomain_neg {R α β : Type*} [Ring R] (f : α ↪ β)
    (x : α →₀ R) : embDomain f (-x) = -embDomain f x :=
  (embDomain.addMonoidHom f).map_neg x

end Finsupp

namespace Module.Relations.Solution

@[simp]
lemma π_single' {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {relations : Module.Relations A} (solution : relations.Solution M)
    (g : relations.G) (a : A) :
    solution.π (Finsupp.single g a) = a • solution.var g := by
  simp [π]

end Module.Relations.Solution

/-! ## The tautological presentation of `B` as an `A`-module -/

/-- The relations of the tautological presentation of `B` as an `A`-module. -/
noncomputable def tautologicalBaseRelation
    (r : Module.Presentation.tautological.R A B) : B →₀ A :=
  (Module.Presentation.tautologicalRelations A B).relation r

lemma tautologicalBaseRelation_add (b₁ b₂ : B) :
    tautologicalBaseRelation A B (.add b₁ b₂) =
      Finsupp.single b₁ 1 + Finsupp.single b₂ 1 - Finsupp.single (b₁ + b₂) 1 := rfl

lemma tautologicalBaseRelation_smul (a : A) (b : B) :
    tautologicalBaseRelation A B (.smul a b) =
      a • Finsupp.single b 1 - Finsupp.single (a • b) 1 := rfl

/-- The relations of the tautological presentation of `B` as an `A`-module. -/
noncomputable abbrev tautologicalBaseRelations : Module.Relations A where
  G := B
  R := Module.Presentation.tautological.R A B
  relation := tautologicalBaseRelation A B

/-- The tautological solution `[b] ↦ b`. -/
noncomputable def tautologicalBaseSolution :
    (tautologicalBaseRelations A B).Solution B :=
  Module.Presentation.tautologicalSolution A B

lemma tautologicalBaseSolution_isPresentation :
    (tautologicalBaseSolution A B).IsPresentation :=
  Module.Presentation.tautologicalSolution_isPresentation A B

@[simp]
lemma tautologicalBaseSolution_var (b : B) :
    (tautologicalBaseSolution A B).var b = b := rfl

/-- The tautological presentation of `B` as an `A`-module, with one generator
for each element of `B`. -/
noncomputable abbrev tautologicalBasePresentation : Module.Presentation A B where
  G := B
  R := Module.Presentation.tautological.R A B
  relation := tautologicalBaseRelation A B
  toSolution := tautologicalBaseSolution A B
  toIsPresentation := tautologicalBaseSolution_isPresentation A B

@[simp]
lemma tautologicalBasePresentation_var (b : B) :
    (tautologicalBasePresentation A B).var b = b := rfl

/-- The presentation of the `B`-module `Ω[B⁄A]` with generators `db`, induced
by the tautological presentation of the `A`-algebra `B`. -/
@[simps! G R var]
noncomputable abbrev KaehlerDifferential.presentation :
    Module.Presentation B (KaehlerDifferential A B) :=
  AffineCrystalline.DeRham.Presentation.Tautological.differentialPresentation
    (A := A) (B := B)

namespace DeRhamComplex

variable {n : ℕ}

section

variable {α : Type*} (x : α) (f : Fin n → α)

/-- The `(n + 1)`-tuple `(x, f 0, …, f (n - 1))`. -/
def finInsert : Fin (n + 1) → α
  | ⟨0, _⟩ => x
  | ⟨n + 1, _⟩ => f ⟨n, by omega⟩

@[simp]
lemma finInsert_zero : finInsert x f 0 = x := rfl

@[simp]
lemma finInsert_succ (i : Fin n) : finInsert x f i.succ = f i := rfl

lemma comp_finInsert {β : Type*} (g : α → β) :
    g.comp (finInsert x f) = finInsert (g x) (g.comp f) := by
  ext ⟨(_ | _), _⟩ <;> rfl

lemma finInsert_eq_update_finInsert_zero [Zero α] :
    finInsert x f = update (finInsert 0 f) 0 x := by
  ext ⟨(_ | _), _⟩ <;> rfl

lemma finInsert_update (i : Fin n) (a : α) :
    finInsert x (update f i a) = update (finInsert x f) i.succ a := by
  ext j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · rfl
  · by_cases h : j = i
    · subst h
      simp only [finInsert_succ, update_same]
    · rw [update_noteq (by simpa using h), finInsert_succ, finInsert_succ,
        update_noteq (by simpa using h)]

lemma finInsert_swapValues (i j : Fin n) :
    finInsert x (swapValues f i j) =
      swapValues (finInsert x f) i.succ j.succ := by
  simp only [swapValues_eq_update_update, finInsert_update, finInsert_succ]

lemma swapValues_finInsert_embedding (i : Fin n)
    (g : ((Set.singleton i)ᶜ : Set (Fin n)) → α) (x y : α) :
    swapValues (finInsert y (embedding (G := fun (_ : Fin n) ↦ α) i g x)) 0 i.succ =
      finInsert x (embedding (G := fun (_ : Fin n) ↦ α) i g y) := by
  ext j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · simp only [swapValues_fst, finInsert_succ, embedding_apply_self, finInsert_zero]
  · simp only [finInsert_succ]
    by_cases h : j = i
    · subst h
      simp only [swapValues_snd, finInsert_zero, embedding_apply_self]
    · rw [embedding_apply_of_neq _ _ _ _ _ h, swapValues_apply _ _ _ _
          (by simp [Fin.ext_iff]) (by simpa using h),
        finInsert_succ, embedding_apply_of_neq _ _ _ _ _ h]

end

variable (n)

/-! ## Presentations of the exterior powers of `Ω[B⁄A]` -/

/-- The relations of the presentation of `⋀[B]^n Ω[B⁄A]` induced by
`KaehlerDifferential.presentation A B`. -/
noncomputable def presentationDifferentialsRelation
    (r : Module.Relations.exteriorPower.Rels
      (KaehlerDifferential.presentation A B).toRelations n) :
    (Fin n → B) →₀ B :=
  ((KaehlerDifferential.presentation A B).toRelations.exteriorPower n).relation r

lemma presentationDifferentialsRelation_piTensor (i₀ : Fin n)
    (r : (KaehlerDifferential.presentation A B).R)
    (g : ∀ (i : Fin n) (_ : i ≠ i₀), (KaehlerDifferential.presentation A B).G) :
    presentationDifferentialsRelation A B n
      (.piTensor i₀ r g) =
      (Module.Relations.piTensor
        (fun _ ↦ (KaehlerDifferential.presentation A B).toRelations)).relation
        ⟨i₀, r, fun ⟨a, ha⟩ ↦ g a (fun h ↦ ha (Set.mem_singleton_of_eq h))⟩ := by
  rfl

lemma presentationDifferentialsRelation_antisymmetry
    (g : Fin n → B) (i j : Fin n) (hij : i ≠ j) :
    presentationDifferentialsRelation A B n (.antisymmetry g i j hij) =
      Finsupp.single (swapValues g i j) 1 + Finsupp.single g 1 := rfl

lemma presentationDifferentialsRelation_alternate
    (g : Fin n → B) (i j : Fin n) (hg : g i = g j) (hij : i ≠ j) :
    presentationDifferentialsRelation A B n (.alternate g i j hg hij) =
      Finsupp.single g 1 := rfl

/-- The relations of the presentation of `⋀[B]^n Ω[B⁄A]` with generators
`db₁ ∧ ⋯ ∧ dbₙ`. -/
noncomputable abbrev presentationDifferentialsRelations : Module.Relations B where
  G := Fin n → B
  R := Module.Relations.exteriorPower.Rels
    (KaehlerDifferential.presentation A B).toRelations n
  relation := presentationDifferentialsRelation A B n

/-- The solution `g ↦ dg₀ ∧ ⋯ ∧ dgₙ₋₁` of `presentationDifferentialsRelations A B n`. -/
noncomputable def presentationDifferentialsSolution :
    (presentationDifferentialsRelations A B n).Solution
      (exteriorPower B n (KaehlerDifferential A B)) :=
  (KaehlerDifferential.presentation A B).toSolution.exteriorPower n

lemma presentationDifferentialsSolution_isPresentation :
    (presentationDifferentialsSolution A B n).IsPresentation :=
  (KaehlerDifferential.presentation A B).toIsPresentation.exteriorPower n

/-- The `B`-linear presentation of `⋀[B]^n Ω[B⁄A]` with generators
`db₁ ∧ ⋯ ∧ dbₙ`. -/
@[simps! G R relation]
noncomputable abbrev presentationDifferentialsUp :
    Module.Presentation B (exteriorPower B n (KaehlerDifferential A B)) where
  G := Fin n → B
  R := Module.Relations.exteriorPower.Rels
    (KaehlerDifferential.presentation A B).toRelations n
  relation := presentationDifferentialsRelation A B n
  toSolution := presentationDifferentialsSolution A B n
  toIsPresentation := presentationDifferentialsSolution_isPresentation A B n

@[simp]
lemma presentationDifferentialsUp_var {n : ℕ} (g : Fin n → B) :
    ((presentationDifferentialsUp A B n).var g) =
      exteriorPower.ιMulti _ _ (KaehlerDifferential.D A B ∘ g) :=
  rfl

lemma presentationDifferentialsUp_relation_alternate
    (g : Fin n → B) (i j : Fin n) (hg : g i = g j) (hij : i ≠ j) :
    (presentationDifferentialsUp A B n).relation
    (Module.Relations.exteriorPower.Rels.alternate g i j hg hij) =
      Finsupp.single g 1 := rfl

open Classical in
/-- Lifts of the relations `b₀ • r` (for `b₀ : B` and `r` a relation of
`presentationDifferentialsUp A B n`) to the free `A`-module on the generators
`(g, b₀)`, used to restrict scalars from `B` to `A`. -/
@[simp]
noncomputable def differentialsRestrictScalarsLift
    (r : (tautologicalBasePresentation A B).G ×
      (presentationDifferentialsUp A B n).R) :
    ((tautologicalBasePresentation A B).finsupp
      (presentationDifferentialsUp A B n).G).G →₀ A :=
  match r with
  | ⟨b₀, .piTensor i₀ (.add b₁ b₂) g⟩ =>
      Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
        (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h))) b₁, b₀⟩ 1 +
        Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
          (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h))) b₂, b₀⟩ 1 -
        Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
          (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h))) (b₁ + b₂), b₀⟩ 1
  | ⟨(b₀ : B), .piTensor i₀ (.mul (b₁ : B) (b₂ : B)) g⟩ =>
      Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
        (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h))) b₂, b₀ * b₁⟩ 1 +
        Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
          (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h))) b₁, b₀ * b₂⟩ 1 -
        Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
          (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h))) (b₁ * b₂), b₀⟩ 1
  | ⟨b₀, .piTensor i₀ (.algebraMap a) g⟩ =>
      -Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
        (fun j ↦ g j (fun h ↦ j.2 (Set.mem_singleton_of_eq h)))
        (algebraMap A B a), b₀⟩ 1
  | ⟨b₀, .alternate g _ _ _ _⟩ => Finsupp.single ⟨g, b₀⟩ 1
  | ⟨b₀, .antisymmetry g i j _⟩ =>
      Finsupp.single ⟨swapValues g i j, b₀⟩ 1 + Finsupp.single ⟨g, b₀⟩ 1

open Classical in
/-- The lift of `b₀` times the additivity relation in slot `i₀`. -/
private lemma differentialsRestrictScalarsLift_π_piTensor_add
    (b₀ : B) (i₀ : Fin n) (b₁ b₂ : B)
    (g : ∀ (i : Fin n) (_ : i ≠ i₀), (KaehlerDifferential.presentation A B).G) :
    ((tautologicalBasePresentation A B).finsupp (presentationDifferentialsUp A B n).G).π
        (differentialsRestrictScalarsLift A B n ⟨b₀, .piTensor i₀ (.add b₁ b₂) g⟩) =
      LinearMap.restrictScalars A (presentationDifferentialsUp A B n).map
        ((tautologicalBasePresentation A B).var b₀ •
          Finsupp.single (.piTensor i₀ (.add b₁ b₂) g) (1 : B)) := by
  letI : DecidableEq B := Classical.decEq _
  simp only [differentialsRestrictScalarsLift]
  simp only [map_sub, map_add]
  erw [Module.Presentation.finsupp_π, Module.Presentation.finsupp_π,
    Module.Presentation.finsupp_π]
  simp only [tautologicalBaseSolution_var]
  change _ = (presentationDifferentialsUp A B n).map _
  rw [map_smul]
  erw [Module.Relations.map_single]
  change _ = b₀ • presentationDifferentialsRelation A B n _
  rw [presentationDifferentialsRelation_piTensor]
  dsimp [Module.Relations.piTensor]
  rw [AffineCrystalline.DeRham.Presentation.Tautological.differentialRelation_add]
  simp only [Finsupp.embDomain_sub, Finsupp.embDomain_add, Finsupp.embDomain_single,
    smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one]

open Classical in
/-- The lift of `b₀` times the Leibniz relation in slot `i₀`. -/
private lemma differentialsRestrictScalarsLift_π_piTensor_mul
    (b₀ : B) (i₀ : Fin n) (b₁ b₂ : B)
    (g : ∀ (i : Fin n) (_ : i ≠ i₀), (KaehlerDifferential.presentation A B).G) :
    ((tautologicalBasePresentation A B).finsupp (presentationDifferentialsUp A B n).G).π
        (differentialsRestrictScalarsLift A B n ⟨b₀, .piTensor i₀ (.mul b₁ b₂) g⟩) =
      LinearMap.restrictScalars A (presentationDifferentialsUp A B n).map
        ((tautologicalBasePresentation A B).var b₀ •
          Finsupp.single (.piTensor i₀ (.mul b₁ b₂) g) (1 : B)) := by
  letI : DecidableEq B := Classical.decEq _
  simp only [differentialsRestrictScalarsLift]
  simp only [map_sub, map_add]
  erw [Module.Presentation.finsupp_π, Module.Presentation.finsupp_π,
    Module.Presentation.finsupp_π]
  simp only [tautologicalBaseSolution_var]
  change _ = (presentationDifferentialsUp A B n).map _
  rw [map_smul]
  erw [Module.Relations.map_single]
  change _ = b₀ • presentationDifferentialsRelation A B n _
  rw [presentationDifferentialsRelation_piTensor]
  dsimp [Module.Relations.piTensor]
  rw [AffineCrystalline.DeRham.Presentation.Tautological.differentialRelation_mul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.embDomain_sub,
    Finsupp.embDomain_add, Finsupp.embDomain_single, smul_sub, smul_add]

open Classical in
/-- The lift of `b₀` times the relation `d (algebraMap A B a) = 0` in slot `i₀`. -/
private lemma differentialsRestrictScalarsLift_π_piTensor_algebraMap
    (b₀ : B) (i₀ : Fin n) (a : A)
    (g : ∀ (i : Fin n) (_ : i ≠ i₀), (KaehlerDifferential.presentation A B).G) :
    ((tautologicalBasePresentation A B).finsupp (presentationDifferentialsUp A B n).G).π
        (differentialsRestrictScalarsLift A B n ⟨b₀, .piTensor i₀ (.algebraMap a) g⟩) =
      LinearMap.restrictScalars A (presentationDifferentialsUp A B n).map
        ((tautologicalBasePresentation A B).var b₀ •
          Finsupp.single (.piTensor i₀ (.algebraMap a) g) (1 : B)) := by
  letI : DecidableEq B := Classical.decEq _
  simp only [differentialsRestrictScalarsLift]
  rw [map_neg]
  erw [Module.Presentation.finsupp_π]
  simp only [tautologicalBaseSolution_var]
  change _ = (presentationDifferentialsUp A B n).map _
  rw [map_smul]
  erw [Module.Relations.map_single]
  change _ = b₀ • presentationDifferentialsRelation A B n _
  rw [presentationDifferentialsRelation_piTensor]
  dsimp [Module.Relations.piTensor]
  rw [AffineCrystalline.DeRham.Presentation.Tautological.differentialRelation_algebraMap]
  simp only [Finsupp.embDomain_neg, Finsupp.embDomain_single, smul_neg,
    Finsupp.smul_single, smul_eq_mul, mul_one]

open Classical in
/-- The lift of `b₀` times an antisymmetry relation. -/
private lemma differentialsRestrictScalarsLift_π_antisymmetry
    (b₀ : B) (g : Fin n → B) (i j : Fin n)
    (hg : i ≠ j) :
    ((tautologicalBasePresentation A B).finsupp (presentationDifferentialsUp A B n).G).π
        (differentialsRestrictScalarsLift A B n ⟨b₀, .antisymmetry g i j hg⟩) =
      LinearMap.restrictScalars A (presentationDifferentialsUp A B n).map
        ((tautologicalBasePresentation A B).var b₀ •
          Finsupp.single (.antisymmetry g i j hg) (1 : B)) := by
  letI : DecidableEq B := Classical.decEq _
  simp only [differentialsRestrictScalarsLift]
  rw [map_add]
  simp only [tautologicalBaseSolution_var]
  change _ = (presentationDifferentialsUp A B n).map _
  rw [map_smul]
  erw [Module.Presentation.finsupp_π, Module.Presentation.finsupp_π,
    Module.Relations.map_single]
  change _ = b₀ • presentationDifferentialsRelation A B n _
  rw [presentationDifferentialsRelation_antisymmetry]
  simp only [tautologicalBaseSolution_var, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one]

open Classical in
/-- The lift of `b₀` times an alternating relation. -/
private lemma differentialsRestrictScalarsLift_π_alternate
    (b₀ : B) (g : Fin n → B) (i j : Fin n)
    (hg : g i = g j) (hij : i ≠ j) :
    ((tautologicalBasePresentation A B).finsupp (presentationDifferentialsUp A B n).G).π
        (differentialsRestrictScalarsLift A B n ⟨b₀, .alternate g i j hg hij⟩) =
      LinearMap.restrictScalars A (presentationDifferentialsUp A B n).map
        ((tautologicalBasePresentation A B).var b₀ •
          Finsupp.single (.alternate g i j hg hij) (1 : B)) := by
  letI : DecidableEq B := Classical.decEq _
  simp only [differentialsRestrictScalarsLift]
  simp only [tautologicalBaseSolution_var]
  change _ = (presentationDifferentialsUp A B n).map _
  rw [map_smul]
  erw [Module.Presentation.finsupp_π, Module.Relations.map_single]
  change _ = b₀ • presentationDifferentialsRelation A B n _
  rw [presentationDifferentialsRelation_alternate]
  simp only [tautologicalBaseSolution_var]
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

open Classical in
/-- The data needed to restrict the scalars of `presentationDifferentialsUp A B n`
from `B` to `A` along `tautologicalBasePresentation A B`. -/
@[simps!]
noncomputable def differentialsRestrictScalarsData :
    (presentationDifferentialsUp A B n).RestrictScalarsData
      (tautologicalBasePresentation A B) where
  lift := differentialsRestrictScalarsLift A B n
  π_lift r := match r with
    | ⟨b₀, .piTensor i₀ (.add b₁ b₂) g⟩ =>
      differentialsRestrictScalarsLift_π_piTensor_add A B n b₀ i₀ b₁ b₂ g
    | ⟨b₀, .piTensor i₀ (.mul b₁ b₂) g⟩ =>
      differentialsRestrictScalarsLift_π_piTensor_mul A B n b₀ i₀ b₁ b₂ g
    | ⟨b₀, .piTensor i₀ (.algebraMap a) g⟩ =>
      differentialsRestrictScalarsLift_π_piTensor_algebraMap A B n b₀ i₀ a g
    | ⟨b₀, .antisymmetry g i j hg⟩ =>
      differentialsRestrictScalarsLift_π_antisymmetry A B n b₀ g i j hg
    | ⟨b₀, .alternate g i j hg hij⟩ =>
      differentialsRestrictScalarsLift_π_alternate A B n b₀ g i j hg hij

-- `Module.Presentation.restrictScalars` is a Mathlib `def`. It is made reducible here so that
-- the generators and relations of `presentationDifferentialsDown` unfold (by `dsimp`) to the
-- explicit form used in the verification of the relations for `d` below.
set_option allowUnsafeReducibility true in
attribute [local reducible]
  Module.Presentation.restrictScalars

open Classical in
/-- The `A`-linear presentation of `⋀[B]^n Ω[B⁄A]` with generators
`b₀ db₁ ∧ ⋯ ∧ dbₙ`, indexed by pairs `(g, b₀)`. -/
@[simps! G R relation]
noncomputable abbrev presentationDifferentialsDown :
    Module.Presentation A (exteriorPower B n (KaehlerDifferential A B)) :=
  (presentationDifferentialsUp A B n).restrictScalars
    (tautologicalBasePresentation A B) (differentialsRestrictScalarsData A B n)

/-- The generator of `presentationDifferentialsDown A B n` indexed by `(g, b₀)`
is `b₀ • (dg₀ ∧ ⋯ ∧ dgₙ₋₁)`. -/
lemma presentationDifferentialsDown_var (b₀ : B) {n : ℕ} (g : Fin n → B) :
    ((presentationDifferentialsDown A B n).var ⟨g, b₀⟩) =
      b₀ • exteriorPower.ιMulti _ _ (KaehlerDifferential.D A B ∘ g) := by
  dsimp [presentationDifferentialsDown, Module.Presentation.restrictScalars,
    Module.Presentation.ofExact]
  simp only [Module.Presentation.finsupp_var, tautologicalBaseSolution_var]
  erw [Module.Relations.Solution.π_single']
  rw [presentationDifferentialsUp_var]

open Classical in
/-- `presentationDifferentialsDown_var`, with the generator written in terms of
`presentationDifferentialsSolution A B n`. -/
lemma presentationDifferentialsDown_var_expanded (b₀ : B) {n : ℕ} (g : Fin n → B) :
    (presentationDifferentialsSolution A B n).π
        (((tautologicalBasePresentation A B).finsupp (Fin n → B)).var ⟨g, b₀⟩) =
      b₀ • exteriorPower.ιMulti _ _ (KaehlerDifferential.D A B ∘ g) := by
  letI : DecidableEq B := Classical.decEq _
  rw [Module.Presentation.finsupp_var, tautologicalBasePresentation_var]
  erw [Module.Relations.Solution.π_single']
  rw [presentationDifferentialsUp_var]

/-! ## The de Rham differential

The de Rham differential is defined on the generators of
`presentationDifferentialsDown A B n` by `b₀ dg₀ ∧ ⋯ ∧ dgₙ₋₁ ↦ db₀ ∧ dg₀ ∧ ⋯ ∧ dgₙ₋₁`.
The following lemmas check that this assignment respects each family of relations of the
presentation.
-/

/-- The assignment respects additivity in `b₀`. -/
private lemma d_relation_tautological_add (g : Fin n → B) (b₁ b₂ : B) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inl ⟨g, .add b₁ b₂⟩)) = 0 := by
  dsimp
  simp only [tautologicalBaseRelation_add, Finsupp.linearCombination_embDomain, map_sub,
    map_add, Finsupp.linearCombination_single, Function.comp_apply,
    Function.Embedding.sigmaMk_apply, one_smul]
  rw [presentationDifferentialsDown_var_expanded, presentationDifferentialsDown_var_expanded,
    presentationDifferentialsDown_var_expanded]
  simp only [comp_finInsert, one_smul, map_add, sub_eq_zero]
  rw [finInsert_eq_update_finInsert_zero]
  nth_rw 2 [finInsert_eq_update_finInsert_zero]
  nth_rw 3 [finInsert_eq_update_finInsert_zero]
  rw [AlternatingMap.map_update_add]

/-- The assignment respects `A`-linearity in `b₀`. -/
private lemma d_relation_tautological_smul (g : Fin n → B) (a : A) (b : B) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inl ⟨g, .smul a b⟩)) = 0 := by
  dsimp
  simp only [tautologicalBaseRelation_smul, Finsupp.linearCombination_embDomain, map_sub,
    map_smul, Finsupp.linearCombination_single, Function.comp_apply,
    Function.Embedding.sigmaMk_apply, one_smul]
  rw [presentationDifferentialsDown_var_expanded, presentationDifferentialsDown_var_expanded]
  simp only [one_smul, comp_finInsert, Derivation.map_smul, sub_eq_zero]
  rw [finInsert_eq_update_finInsert_zero]
  nth_rw 2 [finInsert_eq_update_finInsert_zero]
  rw [algebra_compatible_smul B a, algebra_compatible_smul B a,
    AlternatingMap.map_update_smul]

/-- The assignment respects the additivity of `d` in slot `i`. -/
private lemma d_relation_piTensor_add (b₀ : B) (i : Fin n) (b₁ b₂ : B)
    (g : ∀ (j : Fin n) (_ : j ≠ i), (KaehlerDifferential.presentation A B).G) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inr ⟨b₀, .piTensor i (.add b₁ b₂) g⟩)) = 0 := by
  dsimp
  simp only [map_sub, map_add, Finsupp.linearCombination_single, one_smul, sub_eq_zero]
  rw [presentationDifferentialsDown_var_expanded, one_smul,
    presentationDifferentialsDown_var_expanded, one_smul,
    presentationDifferentialsDown_var_expanded, one_smul]
  simp only [comp_finInsert, comp_embedding, map_add]
  rw [embedding_eq_update_embedding_zero]
  nth_rw 2 [embedding_eq_update_embedding_zero]
  nth_rw 3 [embedding_eq_update_embedding_zero]
  simp only [finInsert_update, AlternatingMap.map_update_add]

/-- The generator formula is compatible with the Leibniz rule:
`d(b₀b₁) ∧ ⋯ ∧ db₂ ∧ ⋯ + d(b₀b₂) ∧ ⋯ ∧ db₁ ∧ ⋯ = db₀ ∧ ⋯ ∧ d(b₁b₂) ∧ ⋯`, where the
factors `db₂`, `db₁` and `d(b₁b₂)` sit in slot `i + 1` and the remaining factors are given
by `h`. -/
private lemma ιMulti_finInsert_embedding_leibniz (i : Fin n)
    (h : ((Set.singleton i)ᶜ : Set (Fin n)) → Ω[B⁄A]) (b₀ b₁ b₂ : B) :
    exteriorPower.ιMulti B (n + 1) (finInsert (KaehlerDifferential.D A B (b₀ * b₁))
        (embedding (G := fun _ ↦ Ω[B⁄A]) i h (KaehlerDifferential.D A B b₂))) +
      exteriorPower.ιMulti B (n + 1) (finInsert (KaehlerDifferential.D A B (b₀ * b₂))
        (embedding (G := fun _ ↦ Ω[B⁄A]) i h (KaehlerDifferential.D A B b₁))) =
    exteriorPower.ιMulti B (n + 1) (finInsert (KaehlerDifferential.D A B b₀)
        (embedding (G := fun _ ↦ Ω[B⁄A]) i h (KaehlerDifferential.D A B (b₁ * b₂)))) := by
  conv_rhs =>
    rw [Derivation.leibniz, embedding_eq_update_embedding_zero,
      finInsert_update, AlternatingMap.map_update_add,
      AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
      ← finInsert_update, ← finInsert_update,
      ← embedding_eq_update_embedding_zero,
      ← embedding_eq_update_embedding_zero]
  rw [finInsert_eq_update_finInsert_zero]
  nth_rw 2 [finInsert_eq_update_finInsert_zero]
  conv_lhs =>
    rw [Derivation.leibniz, AlternatingMap.map_update_add,
      AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
      ← finInsert_eq_update_finInsert_zero]
    rw [Derivation.leibniz, AlternatingMap.map_update_add,
      AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
      ← finInsert_eq_update_finInsert_zero,
      ← finInsert_eq_update_finInsert_zero,
      ← finInsert_eq_update_finInsert_zero]
  have : ∀ (x₁ x₂ x₃ x₄ : (⋀[B]^(n + 1) (Ω[B⁄A]))),
      x₁ = -x₃ → x₁ + x₂ + (x₃ + x₄) = x₂ + x₄ := by
    rintro x₁ x₂ x₃ x₄ rfl; abel
  apply this
  rw [← smul_neg]
  congr
  rw [← AlternatingMap.antisymmetry _ _ 0 i.succ (by simp [Fin.ext_iff]),
    swapValues_finInsert_embedding]

/-- The assignment respects the Leibniz rule in slot `i`. -/
private lemma d_relation_piTensor_mul (b₀ : B) (i : Fin n) (b₁ b₂ : B)
    (g : ∀ (j : Fin n) (_ : j ≠ i), (KaehlerDifferential.presentation A B).G) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inr ⟨b₀, .piTensor i (.mul b₁ b₂) g⟩)) = 0 := by
  dsimp
  simp only [map_sub, map_add, Finsupp.linearCombination_single, one_smul, sub_eq_zero]
  rw [presentationDifferentialsDown_var_expanded, one_smul,
    presentationDifferentialsDown_var_expanded, one_smul,
    presentationDifferentialsDown_var_expanded, one_smul]
  simp only [comp_finInsert, comp_embedding]
  exact ιMulti_finInsert_embedding_leibniz A B n i _ b₀ b₁ b₂

/-- The assignment respects the relation `d (algebraMap A B a) = 0` in slot `i`. -/
private lemma d_relation_piTensor_algebraMap (b₀ : B) (i : Fin n) (a : A)
    (g : ∀ (j : Fin n) (_ : j ≠ i), (KaehlerDifferential.presentation A B).G) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inr ⟨b₀, .piTensor i (.algebraMap a) g⟩)) = 0 := by
  dsimp
  simp only [map_neg, Finsupp.linearCombination_single, one_smul, neg_eq_zero]
  rw [presentationDifferentialsDown_var_expanded, one_smul]
  apply MultilinearMap.map_coord_zero _ i.succ (by simp)

/-- The assignment respects the antisymmetry relations. -/
private lemma d_relation_antisymmetry (b₀ : B) (g : Fin n → B) (i j : Fin n)
    (hij : i ≠ j) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inr ⟨b₀, .antisymmetry g i j hij⟩)) = 0 := by
  dsimp
  simp only [map_add, Finsupp.linearCombination_single, one_smul]
  rw [presentationDifferentialsDown_var_expanded, one_smul, comp_finInsert,
    presentationDifferentialsDown_var_expanded, one_smul, comp_finInsert]
  rw [← comp_finInsert, finInsert_swapValues,
    ← Function.swapValues_comp, ← comp_finInsert,
    AlternatingMap.antisymmetry _ _ _ _ (by simpa using hij), neg_add_cancel]

/-- The assignment respects the alternating relations. -/
private lemma d_relation_alternate (b₀ : B) (g : Fin n → B) (i j : Fin n)
    (hg : g i = g j) (hij : i ≠ j) :
    Finsupp.linearCombination A
      (fun (⟨g, b₀⟩ : (presentationDifferentialsDown A B n).G) ↦
        (presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      ((presentationDifferentialsDown A B n).relation
        (.inr ⟨b₀, .alternate g i j hg hij⟩)) = 0 := by
  dsimp
  simp only [Finsupp.linearCombination_single, one_smul]
  rw [presentationDifferentialsDown_var_expanded, one_smul, comp_finInsert]
  apply AlternatingMap.map_eq_zero_of_eq (i := i.succ) (j := j.succ)
  · simp [hg]
  · simpa using hij

/-- The de Rham differential `⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]`, defined on
the generators of `presentationDifferentialsDown A B n` by
`b₀ dg₀ ∧ ⋯ ∧ dgₙ₋₁ ↦ db₀ ∧ dg₀ ∧ ⋯ ∧ dgₙ₋₁`. The lemmas above check that
this assignment respects every relation of the presentation. -/
noncomputable def d (n : ℕ) : exteriorPower B n (KaehlerDifferential A B) →ₗ[A]
    exteriorPower B (n + 1) (KaehlerDifferential A B) :=
  (presentationDifferentialsDown A B n).desc
    { var := fun ⟨g, b₀⟩ ↦
        ((presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      linearCombination_var_relation := by
        rintro (⟨g, r⟩ | ⟨b₀, r⟩)
        · cases r with
          | add b₁ b₂ => exact d_relation_tautological_add A B n g b₁ b₂
          | smul a b => exact d_relation_tautological_smul A B n g a b
        · cases r with
          | piTensor i r g =>
            cases r with
            | add b₁ b₂ => exact d_relation_piTensor_add A B n b₀ i b₁ b₂ g
            | mul b₁ b₂ => exact d_relation_piTensor_mul A B n b₀ i b₁ b₂ g
            | algebraMap a => exact d_relation_piTensor_algebraMap A B n b₀ i a g
          | antisymmetry g i j hij => exact d_relation_antisymmetry A B n b₀ g i j hij
          | alternate g i j hg hij => exact d_relation_alternate A B n b₀ g i j hg hij }

/-- The generator formula for the de Rham differential. -/
@[simp]
lemma d_var (b₀ : B) {n : ℕ} (g : Fin n → B) :
    d A B n ((presentationDifferentialsDown A B n).var ⟨g, b₀⟩) =
      ((presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩) := by
  apply (presentationDifferentialsDown A B n).desc_var

open Classical in
/-- `d_var`, with the generators written in terms of
`presentationDifferentialsSolution`. -/
lemma d_var_expanded (b₀ : B) {n : ℕ} (g : Fin n → B) :
    d A B n
        ((presentationDifferentialsSolution A B n).π
          (((tautologicalBasePresentation A B).finsupp (Fin n → B)).var ⟨g, b₀⟩)) =
      (presentationDifferentialsSolution A B (n + 1)).π
        (((tautologicalBasePresentation A B).finsupp (Fin (n + 1) → B)).var
          ⟨finInsert b₀ g, (1 : B)⟩) :=
  d_var A B b₀ g

/-- The de Rham differential squares to zero. -/
@[simp]
lemma d_d (n : ℕ) : d A B (n + 1) ∘ₗ d A B n = 0 := by
  apply (presentationDifferentialsDown A B n).postcomp_injective
  ext ⟨g, b₀⟩
  dsimp
  rw [d_var_expanded, d_var_expanded,
    presentationDifferentialsDown_var_expanded, one_smul]
  exact MultilinearMap.map_coord_zero _ 0 (by simp)

@[simp]
lemma d_d_apply {n : ℕ} (x) : d A B (n + 1) (d A B n x) = 0 := DFunLike.congr_fun (d_d A B n) x

end DeRhamComplex

/-- The algebraic de Rham complex `⋀[B]^• Ω[B⁄A]` of `B` over `A`, as a cochain
complex of `A`-modules. -/
noncomputable def deRhamComplex : CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (exteriorPower B n (KaehlerDifferential A B)))
    (fun n ↦ ModuleCat.ofHom (DeRhamComplex.d A B n)) (fun n ↦ by
      apply ModuleCat.hom_ext
      exact DeRhamComplex.d_d A B n)
