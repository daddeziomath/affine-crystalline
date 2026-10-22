/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Homology.TotM
import AffineCrystalline.Cohomology.FunctorCategoryInjectives
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.Additive

/-!
# Čech complexes and derived limits

Let `J` be a category and `X : SimplexCategory ⥤ J` a cosimplicial object whose
`n`-th term corepresents `(n+1)`-tuples of elements of nonempty sets `S Z`:

```text
Hom(X[n], Z) ≃ S(Z)^(n+1),   compatibly with the cosimplicial structure.
```

This is the situation of an object `X[0]` admitting a map to every object of
`J`, together with its iterated coproducts `X[n] = X[0] ⊔ ⋯ ⊔ X[0]`; it is the
dual form of the setting of Stacks, Tag 07JM (a category with a covering
object).

For a diagram `G : J ⥤ ModuleCat R`, the *Čech complex* of `G` is the
alternating coface complex of the cosimplicial module `n ↦ G(X[n])`.  We prove:

* in degree zero, the projection `lim G ⟶ G(X[0])` identifies `lim G` with the
  kernel of the first Čech differential;
* if `G` is injective, its Čech complex is exact in positive degrees.  The proof
  embeds `G` into the diagram `Y ↦ ∏_Z (Hom(Y, Z) → G(Z))`, whose Čech complex
  has an explicit contraction, and uses a retraction of this embedding.

For an injective resolution `F ⟶ I^•`, these facts show that the rows of the
bicomplex `I^q(X[p])`, augmented by `lim I^q`, are exact, while its columns,
augmented by `F(X[p])`, are exact because `I^•` is a resolution.  By augmented
acyclic assembly (`AffineCrystalline.Homology.RawBi.augColι_quasiIso` and
`AffineCrystalline.Homology.RawBi.augRowι_quasiIso`) this gives a zigzag of
quasi-isomorphisms between `lim I^•`, which computes the right-derived limit of
`F`, and the Čech complex of `F`.

## Main definitions

* `CechNerveData`: the data of the cosimplicial object `X` and the
  identifications `Hom(X[n], Z) ≃ S(Z)^(n+1)`.
* `cech`, `cechMap`: the Čech complex of a module diagram, functorial in the
  diagram.
* `bigCoinduced`, `toBig`: the diagram `Y ↦ ∏_Z (Hom(Y, Z) → G(Z))` and the
  embedding of `G` into it.
* `cechBicomplex`: the Čech bicomplex `I^q(X[p])` of an injective resolution.
* `limComplex`: the complex `lim I^•`.
* `Zigzag`, `cechZigzag`: the zigzag of quasi-isomorphisms
  `lim I^• ⟶ Tot ⟵ Č^•(F)`.

## Main results

* `augment_injective`, `exists_limit_of_cocycle`, `augment_comp_d`: the
  sequence `0 ⟶ lim G ⟶ G(X[0]) ⟶ G(X[1])` is exact.
* `big_cocycle_eq`: the Čech complex of `bigCoinduced G` is exact in positive
  degrees.
* `exists_cech_d_eq_of_injective`: the Čech complex of an injective diagram is exact in
  positive degrees.
* `limAug_rowsExact`, `resAug_columnsExact`: exactness of the augmented rows and
  columns of the Čech bicomplex of an injective resolution.

## References

* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace AffineCrystalline.Cohomology.Cech

/-- Čech nerve data on `J`: a cosimplicial object `X` of `J` and nonempty sets
`S Z` such that `X[n]` corepresents `Z ↦ S(Z)^(n+1)`, compatibly with the
cosimplicial structure. -/
structure CechNerveData (J : Type (v + 1)) [Category.{v} J] where
  X : SimplexCategory ⥤ J
  S : J → Type v
  nonempty : ∀ Z, Nonempty (S Z)
  equiv : ∀ (n : ℕ) (Z : J), (X.obj ⦋n⦌ ⟶ Z) ≃ (Fin (n + 1) → S Z)
  equiv_map : ∀ {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (Z : J) (g : X.obj ⦋n⦌ ⟶ Z),
    equiv m Z (X.map f ≫ g) = equiv n Z g ∘ f.toOrderHom

variable {J : Type (v + 1)} [Category.{v} J] (D : CechNerveData J)
variable {R : Type u} [CommRing R]

namespace CechNerveData

/-- The coface `δ i` acts on indices by `Fin.succAbove i`. -/
theorem δ_toOrderHom {n : ℕ} (i : Fin (n + 2)) :
    ⇑(SimplexCategory.δ i).toOrderHom = i.succAbove := rfl

/-- The map `X[n+1] ⟶ Z` corresponding to the tuple obtained by prepending
`s ∈ S(Z)` to the tuple of `g : X[n] ⟶ Z`. -/
noncomputable def cons {n : ℕ} {Z : J} (s : D.S Z) (g : D.X.obj ⦋n⦌ ⟶ Z) :
    D.X.obj ⦋n + 1⦌ ⟶ Z :=
  (D.equiv (n + 1) Z).symm (Fin.cons s (D.equiv n Z g))

/-- Removing the prepended entry recovers the original map. -/
theorem δ_zero_cons {n : ℕ} {Z : J} (s : D.S Z) (g : D.X.obj ⦋n⦌ ⟶ Z) :
    D.X.map (SimplexCategory.δ 0) ≫ D.cons s g = g := by
  apply (D.equiv n Z).injective
  rw [D.equiv_map, cons, Equiv.apply_symm_apply, δ_toOrderHom]
  funext j
  simp

/-- Prepending commutes with the cofaces `δ (i + 1)`. -/
theorem δ_succ_cons {n : ℕ} {Z : J} (s : D.S Z) (g : D.X.obj ⦋n + 1⦌ ⟶ Z)
    (i : Fin (n + 2)) :
    D.X.map (SimplexCategory.δ i.succ) ≫ D.cons s g =
      D.cons s (D.X.map (SimplexCategory.δ i) ≫ g) := by
  apply (D.equiv (n + 1) Z).injective
  rw [D.equiv_map, cons, cons, Equiv.apply_symm_apply, Equiv.apply_symm_apply, D.equiv_map,
    δ_toOrderHom, δ_toOrderHom]
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.succ_succAbove_succ]

/-- Two maps out of `X[0]` are the two faces of a map out of `X[1]`. -/
theorem exists_pair {Z : J} (g g' : D.X.obj ⦋0⦌ ⟶ Z) :
    ∃ h : D.X.obj ⦋1⦌ ⟶ Z, D.X.map (SimplexCategory.δ 1) ≫ h = g ∧
      D.X.map (SimplexCategory.δ 0) ≫ h = g' := by
  refine ⟨(D.equiv 1 Z).symm ![D.equiv 0 Z g 0, D.equiv 0 Z g' 0], ?_, ?_⟩
  · apply (D.equiv 0 Z).injective
    rw [D.equiv_map, Equiv.apply_symm_apply, δ_toOrderHom]
    funext j
    fin_cases j
    rfl
  · apply (D.equiv 0 Z).injective
    rw [D.equiv_map, Equiv.apply_symm_apply, δ_toOrderHom]
    funext j
    fin_cases j
    rfl

end CechNerveData

/-- The cosimplicial module `n ↦ G(X[n])`. -/
abbrev cosimp (G : J ⥤ ModuleCat.{v + 1} R) : CosimplicialObject (ModuleCat.{v + 1} R) :=
  D.X ⋙ G

/-- The Čech complex of a module-valued diagram. -/
noncomputable def cech (G : J ⥤ ModuleCat.{v + 1} R) : CochainComplex (ModuleCat.{v + 1} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v + 1} R)).obj (cosimp D G)

/-- The `n`-th term of the Čech complex is `G(X[n])`. -/
theorem cech_X (G : J ⥤ ModuleCat.{v + 1} R) (n : ℕ) :
    (cech D G).X n = G.obj (D.X.obj ⦋n⦌) := rfl

/-- The Čech differential is the alternating sum of the cofaces. -/
theorem cech_d (G : J ⥤ ModuleCat.{v + 1} R) (n : ℕ) :
    (cech D G).d n (n + 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • G.map (D.X.map (SimplexCategory.δ i)) := by
  exact CochainComplex.of_d (fun n ↦ (cosimp D G).obj ⦋n⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp D G)) n

/-- Elementwise form of `cech_d`. -/
theorem cech_d_apply (G : J ⥤ ModuleCat.{v + 1} R) (n : ℕ) (x : G.obj (D.X.obj ⦋n⦌)) :
    ((cech D G).d n (n + 1)).hom x =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (G.map (D.X.map (SimplexCategory.δ i))).hom x := by
  erw [cech_d, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rfl

/-- The Čech complex is functorial in the diagram. -/
noncomputable def cechMap {G G' : J ⥤ ModuleCat.{v + 1} R} (α : G ⟶ G') : cech D G ⟶ cech D G' :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{v + 1} R)).map
    (Functor.whiskerLeft D.X α)

/-- The components of `cechMap α` are the components of `α`. -/
theorem cechMap_f {G G' : J ⥤ ModuleCat.{v + 1} R} (α : G ⟶ G') (n : ℕ) :
    (cechMap D α).f n = α.app (D.X.obj ⦋n⦌) := rfl

/-! ## Degree zero: the limit is the kernel of the first differential -/

section H0

variable (G : J ⥤ ModuleCat.{v + 1} R)

/-- The first Čech differential is `G(δ 0) - G(δ 1)`. -/
theorem cech_d_zero_apply (x : G.obj (D.X.obj ⦋0⦌)) :
    ((cech D G).d 0 1).hom x =
      (G.map (D.X.map (SimplexCategory.δ 0))).hom x -
        (G.map (D.X.map (SimplexCategory.δ 1))).hom x := by
  rw [cech_d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  exact (sub_eq_add_neg _ _).symm

/-- A degree-zero Čech cocycle has the same image along every map out of `X[0]`. -/
theorem cocycle_map_eq {x : G.obj (D.X.obj ⦋0⦌)} (hx : ((cech D G).d 0 1).hom x = 0)
    {Z : J} (g g' : D.X.obj ⦋0⦌ ⟶ Z) : (G.map g).hom x = (G.map g').hom x := by
  obtain ⟨h, hg, hg'⟩ := D.exists_pair g g'
  rw [cech_d_zero_apply] at hx
  have hx' := (sub_eq_zero.mp hx).symm
  rw [← hg, ← hg', G.map_comp, G.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply]
  exact congrArg (G.map h).hom hx'

/-- The compatible family determined by a degree-zero Čech cocycle `x`: its
component at `Z` is the image of `x` along any map `X[0] ⟶ Z`. -/
noncomputable def cocycleFamily {x : G.obj (D.X.obj ⦋0⦌)} (hx : ((cech D G).d 0 1).hom x = 0) :
    compatibleFamilyLimitObject G :=
  ⟨fun Z ↦ (G.map ((D.equiv 0 Z).symm fun _ ↦ Classical.choice (D.nonempty Z))).hom x,
    by
      intro Y Z f
      change (G.map f).hom ((G.map _).hom x) = _
      rw [← ModuleCat.comp_apply, ← G.map_comp]
      exact cocycle_map_eq D G hx _ _⟩

/-- The limit of `G` is isomorphic to the module of compatible families. -/
noncomputable def limitIso : limit G ≅ compatibleFamilyLimitObject G :=
  limit.isoLimitCone (compatibleFamilyLimitCone G)

/-- The components of the compatible family attached to an element of the limit
are its projections. -/
theorem limitIso_hom_apply (a : (limit G : ModuleCat.{v + 1} R)) (Z : J) :
    ((limitIso G).hom.hom a).1 Z = (limit.π G Z).hom a := by
  change (((limitIso G).hom ≫ compatibleFamilyProjection G Z).hom a) = _
  rw [show (limitIso G).hom ≫ compatibleFamilyProjection G Z = limit.π G Z from
    limit.isoLimitCone_hom_π (compatibleFamilyLimitCone G) Z]

/-- The augmentation `lim G ⟶ G(X[0])` is injective. -/
theorem augment_injective (a : (limit G : ModuleCat.{v + 1} R))
    (ha : (limit.π G (D.X.obj ⦋0⦌)).hom a = 0) : a = 0 := by
  have hall : ∀ Z, (limit.π G Z).hom a = 0 := by
    intro Z
    obtain ⟨s⟩ := D.nonempty Z
    let g : D.X.obj ⦋0⦌ ⟶ Z := (D.equiv 0 Z).symm fun _ ↦ s
    rw [← limit.w G g, ModuleCat.comp_apply, ha, map_zero]
  have h : (limitIso G).hom.hom a = 0 := by
    apply Subtype.ext
    funext Z
    rw [limitIso_hom_apply, hall]
    rfl
  have := congrArg (limitIso G).inv.hom h
  rwa [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply, map_zero] at this

/-- Every degree-zero Čech cocycle comes from the limit. -/
theorem exists_limit_of_cocycle (x : G.obj (D.X.obj ⦋0⦌))
    (hx : ((cech D G).d 0 1).hom x = 0) :
    ∃ a : (limit G : ModuleCat.{v + 1} R), (limit.π G (D.X.obj ⦋0⦌)).hom a = x := by
  refine ⟨(limitIso G).inv.hom (cocycleFamily D G hx), ?_⟩
  rw [← limitIso_hom_apply, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  change (G.map _).hom x = x
  rw [cocycle_map_eq D G hx _ (𝟙 _), G.map_id, ModuleCat.id_apply]

/-- The image of the augmentation `lim G ⟶ G(X[0])` consists of cocycles. -/
theorem augment_comp_d (a : (limit G : ModuleCat.{v + 1} R)) :
    ((cech D G).d 0 1).hom ((limit.π G (D.X.obj ⦋0⦌)).hom a) = 0 := by
  rw [cech_d_zero_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, limit.w, limit.w,
    sub_self]
  rfl

end H0

/-! ## Positive degrees: injective diagrams are Čech-acyclic -/

section Injective

/-- The diagram `Y ↦ ∏_Z (Hom(Y, Z) → G(Z))`.  Every diagram `G` embeds into it
(`toBig`), and its Čech complex is exact in positive degrees
(`big_cocycle_eq`). -/
def bigCoinduced (G : J ⥤ ModuleCat.{v + 1} R) : J ⥤ ModuleCat.{v + 1} R where
  obj Y := ModuleCat.of R (∀ Z : J, (Y ⟶ Z) → G.obj Z)
  map f := ModuleCat.ofHom
    { toFun := fun φ Z g ↦ φ Z (f ≫ g)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id Y := by
    apply ModuleCat.hom_ext
    ext φ Z g
    simp
  map_comp f f' := by
    apply ModuleCat.hom_ext
    ext φ Z g
    simp

/-- The embedding `G ⟶ bigCoinduced G`, `y ↦ (g ↦ G(g) y)`. -/
def toBig (G : J ⥤ ModuleCat.{v + 1} R) : G ⟶ bigCoinduced G where
  app Y := ModuleCat.ofHom
    { toFun := fun y Z g ↦ (G.map g).hom y
      map_add' := fun y y' ↦ by funext Z g; simp
      map_smul' := fun r y ↦ by funext Z g; simp }
  naturality Y Y' f := by
    apply ModuleCat.hom_ext
    ext y
    funext Z g
    change (G.map g).hom ((G.map f).hom y) = (G.map (f ≫ g)).hom y
    rw [G.map_comp, ModuleCat.comp_apply]

/-- The map `toBig G` is a monomorphism, as seen by evaluating at identities. -/
instance mono_toBig (G : J ⥤ ModuleCat.{v + 1} R) : Mono (toBig G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Y
  rw [ModuleCat.mono_iff_injective]
  intro y y' h
  have := congrFun (congrFun h Y) (𝟙 Y)
  change (G.map (𝟙 Y)).hom y = (G.map (𝟙 Y)).hom y' at this
  simpa using this

/-- The contracting homotopy of the Čech complex of `bigCoinduced G`, obtained by
precomposition with `CechNerveData.cons`. -/
noncomputable def bigContraction (G : J ⥤ ModuleCat.{v + 1} R) (n : ℕ)
    (φ : (bigCoinduced G).obj (D.X.obj ⦋n + 1⦌)) : (bigCoinduced G).obj (D.X.obj ⦋n⦌) :=
  fun Z g ↦ φ Z (D.cons (Classical.choice (D.nonempty Z)) g)

/-- Evaluation of an element of `bigCoinduced G` at a map `g : Y ⟶ Z`. -/
def bigEval (G : J ⥤ ModuleCat.{v + 1} R) {Y : J} (Z : J) (g : Y ⟶ Z) :
    (bigCoinduced G).obj Y →ₗ[R] G.obj Z where
  toFun φ := φ Z g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation commutes with the transition maps of `bigCoinduced G`. -/
theorem bigEval_map (G : J ⥤ ModuleCat.{v + 1} R) {Y Y' : J} (f : Y ⟶ Y')
    (φ : (bigCoinduced G).obj Y) (Z : J) (g : Y' ⟶ Z) :
    bigEval G Z g (((bigCoinduced G).map f).hom φ) = bigEval G Z (f ≫ g) φ := rfl

/-- Elements of `bigCoinduced G` are determined by their evaluations. -/
theorem bigEval_ext (G : J ⥤ ModuleCat.{v + 1} R) {Y : J} {φ ψ : (bigCoinduced G).obj Y}
    (h : ∀ Z (g : Y ⟶ Z), bigEval G Z g φ = bigEval G Z g ψ) : φ = ψ := by
  funext Z g
  exact h Z g

/-- The Čech differential of `bigCoinduced G`, after evaluation. -/
theorem big_d_apply (G : J ⥤ ModuleCat.{v + 1} R) (m : ℕ)
    (φ : (bigCoinduced G).obj (D.X.obj ⦋m⦌)) (Z : J) (g : D.X.obj ⦋m + 1⦌ ⟶ Z) :
    bigEval G Z g (((cech D (bigCoinduced G)).d m (m + 1)).hom φ) =
      ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        bigEval G Z (D.X.map (SimplexCategory.δ i) ≫ g) φ := by
  rw [cech_d_apply, map_sum]
  simp only [map_zsmul, bigEval_map]

/-- The contracting homotopy, after evaluation. -/
theorem bigContraction_eval (G : J ⥤ ModuleCat.{v + 1} R) (n : ℕ)
    (φ : (bigCoinduced G).obj (D.X.obj ⦋n + 1⦌)) (Z : J) (g : D.X.obj ⦋n⦌ ⟶ Z) :
    bigEval G Z g (bigContraction D G n φ) =
      bigEval G Z (D.cons (Classical.choice (D.nonempty Z)) g) φ := rfl

/-- The Čech complex of `bigCoinduced G` is exact in positive degrees: every
cocycle `φ` of positive degree is the coboundary of `bigContraction D G n φ`. -/
theorem big_cocycle_eq (G : J ⥤ ModuleCat.{v + 1} R) (n : ℕ)
    (φ : (bigCoinduced G).obj (D.X.obj ⦋n + 1⦌))
    (hφ : ((cech D (bigCoinduced G)).d (n + 1) (n + 2)).hom φ = 0) :
    ((cech D (bigCoinduced G)).d n (n + 1)).hom (bigContraction D G n φ) = φ := by
  apply bigEval_ext
  intro Z g
  have h := congrArg (bigEval G Z (D.cons (Classical.choice (D.nonempty Z)) g)) hφ
  erw [big_d_apply, map_zero] at h
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one,
    neg_smul, Finset.sum_neg_distrib, D.δ_zero_cons, D.δ_succ_cons] at h
  rw [add_neg_eq_zero] at h
  rw [big_d_apply, h]
  simp only [bigContraction_eval]

/-- A retraction of `toBig I`, which exists since `I` is injective. -/
noncomputable def bigRetraction (I : J ⥤ ModuleCat.{v + 1} R) [Injective I] :
    bigCoinduced I ⟶ I :=
  Injective.factorThru (𝟙 I) (toBig I)

/-- `bigRetraction I` is a retraction of `toBig I`. -/
theorem toBig_bigRetraction (I : J ⥤ ModuleCat.{v + 1} R) [Injective I] :
    toBig I ≫ bigRetraction I = 𝟙 I :=
  Injective.comp_factorThru _ _

/-- **Injective diagrams are Čech-acyclic.**  The Čech complex of an injective
diagram is exact in positive degrees. -/
theorem exists_cech_d_eq_of_injective (I : J ⥤ ModuleCat.{v + 1} R) [Injective I] (n : ℕ)
    (c : I.obj (D.X.obj ⦋n + 1⦌)) (hc : ((cech D I).d (n + 1) (n + 2)).hom c = 0) :
    ∃ b : I.obj (D.X.obj ⦋n⦌), ((cech D I).d n (n + 1)).hom b = c := by
  let e := cechMap D (toBig I)
  let r := cechMap D (bigRetraction I)
  have he : ((cech D (bigCoinduced I)).d (n + 1) (n + 2)).hom ((e.f (n + 1)).hom c) = 0 := by
    rw [Homology.hom_comm_apply e (n + 1) (n + 2) c, hc, map_zero]
  refine ⟨(r.f n).hom (bigContraction D I n ((e.f (n + 1)).hom c)), ?_⟩
  refine (Homology.hom_comm_apply r n (n + 1) _).trans ?_
  rw [big_cocycle_eq D I n _ he]
  change ((toBig I).app _ ≫ (bigRetraction I).app _).hom c = c
  rw [← NatTrans.comp_app, toBig_bigRetraction]
  rfl

end Injective

/-! ## The Čech bicomplex of an injective resolution -/

section Comparison

open Homology

variable {F : J ⥤ ModuleCat.{v + 1} R} (I : InjectiveResolution F)

/-- The Čech bicomplex `I^q(X[p])` of an injective resolution `I` of `F`, with
the Čech differential horizontally and the differential of the resolution
vertically. -/
noncomputable def cechBicomplex : RawBi.{v + 1} R where
  M p q := (I.cocomplex.X q).obj (D.X.obj ⦋p⦌)
  dh p p' q := (cech D (I.cocomplex.X q)).d p p'
  dv p q q' := (I.cocomplex.d q q').app (D.X.obj ⦋p⦌)
  dh_shape p p' q h := (cech D (I.cocomplex.X q)).shape p p' (by simpa using h)
  dv_shape p q q' h := by
    rw [I.cocomplex.shape q q' (by simpa using h)]
    rfl
  dh_dh p p' p'' q := (cech D (I.cocomplex.X q)).d_comp_d p p' p''
  dv_dv p q q' q'' := by
    rw [← NatTrans.comp_app, I.cocomplex.d_comp_d]
    rfl
  comm p p' q q' := ((cechMap D (I.cocomplex.d q q')).comm p p').symm

/-- The complex `lim I^•`, which computes the right-derived functors of `lim`
at `F`. -/
noncomputable abbrev limComplex : CochainComplex (ModuleCat.{v + 1} R) ℕ :=
  ((lim : (J ⥤ ModuleCat.{v + 1} R) ⥤ ModuleCat.{v + 1} R).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex

/-- The augmentation of the first column of the Čech bicomplex by `lim I^•`,
given by the projections `lim I^q ⟶ I^q(X[0])`. -/
noncomputable def limAug (q : ℕ) : (limComplex I).X q ⟶ (cechBicomplex D I).M 0 q :=
  limit.π (I.cocomplex.X q) (D.X.obj ⦋0⦌)

/-- The augmentation by `lim I^•` is a morphism of complexes. -/
theorem limAug_comm (q q' : ℕ) :
    (limComplex I).d q q' ≫ limAug D I q' = limAug D I q ≫ (cechBicomplex D I).dv 0 q q' := by
  change limMap (I.cocomplex.d q q') ≫ limit.π _ _ = limit.π _ _ ≫ (I.cocomplex.d q q').app _
  exact limMap_π _ _

/-- The augmentation by `lim I^•` is killed by the first Čech differential. -/
theorem limAug_d (q : ℕ) : limAug D I q ≫ (cechBicomplex D I).dh 0 1 q = 0 := by
  apply ModuleCat.hom_ext
  ext a
  exact augment_comp_d D (I.cocomplex.X q) a

/-- The augmentation of the bottom row of the Čech bicomplex by the Čech complex
of `F`, given by the maps `F(X[p]) ⟶ I^0(X[p])`. -/
noncomputable def resAug (p : ℕ) : (cech D F).X p ⟶ (cechBicomplex D I).M p 0 :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0).app
    (D.X.obj ⦋p⦌)

/-- The augmentation by `Č^•(F)` is a morphism of complexes. -/
theorem resAug_comm (p p' : ℕ) :
    (cech D F).d p p' ≫ resAug D I p' = resAug D I p ≫ (cechBicomplex D I).dh p p' 0 :=
  ((cechMap D ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫
    I.ι.f 0)).comm p p').symm

/-- The augmentation by `Č^•(F)` is killed by the differential of the
resolution. -/
theorem resAug_d (p : ℕ) : resAug D I p ≫ (cechBicomplex D I).dv p 0 1 = 0 := by
  change (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0) ≫
    I.cocomplex.d 0 1).app _ = 0
  rw [Category.assoc, I.ι_f_zero_comp_complex_d, comp_zero]
  rfl

/-- Exactness of the resolution in positive degrees, at every object of `J`. -/
theorem res_exact_succ (Y : J) (q : ℕ) (x : (I.cocomplex.X (q + 1)).obj Y)
    (hx : ((I.cocomplex.d (q + 1) (q + 2)).app Y).hom x = 0) :
    ∃ y : (I.cocomplex.X q).obj Y, ((I.cocomplex.d q (q + 1)).app Y).hom y = x := by
  have hS := (I.exact_succ q).map ((evaluation J (ModuleCat.{v + 1} R)).obj Y)
  exact (ShortComplex.moduleCat_exact_iff _).1 hS x hx

/-- Exactness of the resolution in degree `0`, at every object of `J`. -/
theorem res_exact_zero (Y : J) (x : (I.cocomplex.X 0).obj Y)
    (hx : ((I.cocomplex.d 0 1).app Y).hom x = 0) :
    ∃ y : F.obj Y, (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫
      I.ι.f 0).app Y).hom y = x := by
  let S : ShortComplex (J ⥤ ModuleCat.{v + 1} R) :=
    ShortComplex.mk ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫
      I.ι.f 0) (I.cocomplex.d 0 1) (by rw [Category.assoc, I.ι_f_zero_comp_complex_d, comp_zero])
  have hker : IsLimit (KernelFork.ofι S.f S.zero) := by
    refine IsLimit.ofIsoLimit I.isLimitKernelFork ?_
    exact Fork.ext (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F) (by
      simp [S]
      rfl)
  have hS : S.Exact := S.exact_of_f_is_kernel hker
  have hS' := hS.map ((evaluation J (ModuleCat.{v + 1} R)).obj Y)
  exact (ShortComplex.moduleCat_exact_iff _).1 hS' x hx

/-- The map `F ⟶ I^0` is injective at every object of `J`. -/
theorem res_mono (Y : J) :
    Function.Injective (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫
      I.ι.f 0).app Y).hom := by
  rw [← ModuleCat.mono_iff_injective]
  have : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0) :=
    mono_comp _ _
  exact (NatTrans.mono_iff_mono_app _).1 this Y

/-- The augmented Čech rows `0 ⟶ lim I^q ⟶ I^q(X[0]) ⟶ I^q(X[1]) ⟶ ⋯` are
exact. -/
theorem limAug_rowsExact :
    ((cechBicomplex D I).augCol (limComplex I) (limAug D I) (limAug_comm D I)
      (limAug_d D I)).RowsExact := by
  intro p q x hx
  rcases p with _ | _ | p
  · refine ⟨0, ?_⟩
    have hx' : x = 0 := augment_injective D (I.cocomplex.X q) x hx
    rw [hx', map_zero]
  · exact exists_limit_of_cocycle D (I.cocomplex.X q) x hx
  · exact exists_cech_d_eq_of_injective D (I.cocomplex.X q) p x hx

/-- The augmented resolution columns
`0 ⟶ F(X[p]) ⟶ I^0(X[p]) ⟶ I^1(X[p]) ⟶ ⋯` are exact. -/
theorem resAug_columnsExact :
    ((cechBicomplex D I).augRow (cech D F) (resAug D I) (resAug_comm D I)
      (resAug_d D I)).ColumnsExact := by
  intro p q x hx
  rcases q with _ | _ | q
  · refine ⟨0, ?_⟩
    have hx' : x = 0 := res_mono I _ (hx.trans (map_zero _).symm)
    rw [hx', map_zero]
  · exact res_exact_zero I _ x hx
  · exact res_exact_succ I _ q x hx

/-- A zigzag `A ⟶ mid ⟵ B` of quasi-isomorphisms of cochain complexes of
modules. -/
structure Zigzag (A B : CochainComplex (ModuleCat.{v + 1} R) ℕ) where
  mid : CochainComplex (ModuleCat.{v + 1} R) ℕ
  left : A ⟶ mid
  right : B ⟶ mid
  left_quasiIso : QuasiIso left
  right_quasiIso : QuasiIso right

/-- **The Čech comparison.**  The complex `lim I^•`, which computes the
right-derived limit of `F`, and the Čech complex of `F` are both
quasi-isomorphic to the total complex of the Čech bicomplex of `I`:
`lim I^• ⟶ Tot ⟵ Č^•(F)`. -/
noncomputable def cechZigzag : Zigzag (limComplex I) (cech D F) where
  mid := (cechBicomplex D I).totComplex
  left := (cechBicomplex D I).augColι (limComplex I) (limAug D I) (limAug_comm D I)
    (limAug_d D I)
  right := (cechBicomplex D I).augRowι (cech D F) (resAug D I) (resAug_comm D I)
    (resAug_d D I)
  left_quasiIso := (cechBicomplex D I).augColι_quasiIso _ _ _ _ (limAug_rowsExact D I)
  right_quasiIso := (cechBicomplex D I).augRowι_quasiIso _ _ _ _ (resAug_columnsExact D I)

end Comparison

end AffineCrystalline.Cohomology.Cech
