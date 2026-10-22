/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Injectives and limits in categories of module-valued diagrams

Let `J` be a category with objects in `Type (v + 1)` and morphisms in `Type v`,
and `R` a commutative ring.  This file collects the facts about the functor
category `J ⥤ ModuleCat.{v + 1} R` needed to compute derived limits.

* **Enough injectives.**  For `X : J` and an `R`-module `M`, the *coinduced*
  diagram `coinduced X M` has value `Hom(Y, X) → M` at `Y`; it is the right
  adjoint of evaluation at `X`, written by its elementary formula.  It is
  injective when `M` is, and every diagram `F` embeds into the product, over
  `X : J`, of the coinduced diagrams of injective modules containing `F(X)`.
* **Limits.**  Module-valued diagrams indexed by such a category have limits,
  given concretely by compatible families, and `lim` is an additive functor.
* **Precomposition.**  For an adjunction between `C` and `D`, precomposition
  with the right adjoint is left adjoint to precomposition with the left
  adjoint; consequently precomposition with a left adjoint preserves injective
  objects.

## Main definitions

* `precompositionAdjunction`: the adjunction between precomposition with a
  right adjoint and precomposition with its left adjoint.
* `coinduced`, `coinducedFrom`: coinduced diagrams and the maps into them.
* `coinducedInjectiveEmbedding`: the embedding of a diagram into a product of
  injective coinduced diagrams.
* `compatibleFamilyLimitCone`: the limit cone of compatible families.

## Main results

* `injective_whiskeringLeft_obj_of_adjunction`: precomposition with a left
  adjoint preserves injective objects.
* `injective_coinduced`: coinduced diagrams with injective coefficients are
  injective.
* `hasEnoughInjectivesFunctorCategory`: `J ⥤ ModuleCat.{v + 1} R` has enough
  injectives.
* `hasLimitsOfShapeLargeModuleCat`, `limModuleCatAdditive`: existence and
  additivity of limits of module-valued diagrams indexed by such categories.
-/

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AffineCrystalline.Cohomology

section Precomposition

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Given an adjunction between `C` and `D`, precomposition with the right
adjoint is left adjoint to precomposition with the left adjoint, on functor
categories with values in `E`. -/
noncomputable def precompositionAdjunction
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) :
    ((Functor.whiskeringLeft D C E).obj R) ⊣
      ((Functor.whiskeringLeft C D E).obj L) := by
  apply Adjunction.mkOfHomEquiv
  refine
    { homEquiv := fun F G ↦ {
        toFun := fun α ↦ {
          app := fun X ↦ F.map (adj.unit.app X) ≫ α.app (L.obj X)
          naturality := fun X Y f ↦ by
            have h := α.naturality (L.map f)
            dsimp at h ⊢
            rw [Category.assoc, ← h, ← F.map_comp_assoc, ← F.map_comp_assoc,
              adj.unit_naturality] }
        invFun := fun β ↦ {
          app := fun Y ↦ β.app (R.obj Y) ≫ G.map (adj.counit.app Y)
          naturality := fun X Y f ↦ by
            have h := β.naturality (R.map f)
            dsimp at h ⊢
            rw [← Category.assoc, h, Category.assoc, Category.assoc, ← G.map_comp,
              ← G.map_comp, adj.counit_naturality] }
        left_inv := fun α ↦ by
          ext X
          have h := α.naturality (adj.counit.app X)
          dsimp at h ⊢
          rw [Category.assoc, ← h, ← F.map_comp_assoc, adj.right_triangle_components,
            F.map_id, Category.id_comp]
        right_inv := fun β ↦ by
          ext X
          have h := β.naturality (adj.unit.app X)
          dsimp at h ⊢
          rw [← Category.assoc, h, Category.assoc, ← G.map_comp, adj.left_triangle_components,
            G.map_id, Category.comp_id] }
      homEquiv_naturality_left_symm := fun f g ↦ by
        ext X
        exact Category.assoc _ _ _
      homEquiv_naturality_right := fun f g ↦ by
        ext X
        exact (Category.assoc _ _ _).symm }

/-- Precomposition with a left adjoint preserves injective objects: if `G` is an
injective object of `D ⥤ E`, then so is its precomposition with a left adjoint
`C ⥤ D`.  This holds because precomposition with the right adjoint, which is
left adjoint to precomposition with the left adjoint, preserves
monomorphisms. -/
theorem injective_whiskeringLeft_obj_of_adjunction
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] [HasPullbacks E]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (G : D ⥤ E) [Injective G] :
    Injective (((Functor.whiskeringLeft C D E).obj L).obj G) := by
  let adj' := precompositionAdjunction (C := C) (D := D) (E := E) L R adj
  refine ⟨?_⟩
  intro X Y α f hf
  let f' := ((Functor.whiskeringLeft D C E).obj R).map f
  letI : Mono f' := by
    rw [NatTrans.mono_iff_mono_app]
    intro Z
    exact (NatTrans.mono_iff_mono_app f).mp hf (R.obj Z)
  let α' := (adj'.homEquiv X G).symm α
  let h' := Injective.factorThru α' f'
  let h := (adj'.homEquiv Y G) h'
  refine ⟨h, ?_⟩
  apply (adj'.homEquiv X G).symm.injective
  calc
    (adj'.homEquiv X G).symm (f ≫ h) = f' ≫
        (adj'.homEquiv Y G).symm h :=
          adj'.homEquiv_naturality_left_symm f h
    _ = f' ≫ h' := by simp [h]
    _ = α' := Injective.comp_factorThru α' f'
    _ = (adj'.homEquiv X G).symm α := rfl

end Precomposition

section

variable {J : Type (v + 1)} [Category.{v, v + 1} J]
variable {R : Type u} [CommRing R]

/-- The coinduced module diagram at `X` with coefficients `M`, whose value at `Y`
is the module of functions `Hom(Y, X) → M`.  It is the right adjoint of
evaluation at `X`. -/
def coinduced (X : J) (M : ModuleCat.{v + 1} R) :
    J ⥤ ModuleCat.{v + 1} R where
  obj Y := ModuleCat.of R ((Y ⟶ X) → M)
  map f := ModuleCat.ofHom
    { toFun := fun t g ↦ t (f ≫ g)
      map_add' := by
        intro t s
        ext g
        rfl
      map_smul' := by
        intro r t
        ext g
        rfl }
  map_id Y := by
    apply ModuleCat.hom_ext
    ext t g
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext t h
    simp [Category.assoc]

/-- The natural transformation `F ⟶ coinduced X M` corresponding to a linear map
`g : F(X) ⟶ M`, given at `Y` by `y ↦ (f ↦ g (F(f) y))`. -/
def coinducedFrom (F : J ⥤ ModuleCat.{v + 1} R) (X : J)
    (M : ModuleCat.{v + 1} R) (g : F.obj X ⟶ M) : F ⟶ coinduced X M where
  app Y := ModuleCat.ofHom
    { toFun := fun y f ↦ g (F.map f y)
      map_add' := by
        intro y z
        ext f
        simp
      map_smul' := by
        intro r y
        ext f
        simp }
  naturality {Y Z} f := by
    apply ModuleCat.hom_ext
    ext y
    funext k
    calc
      g (F.map k (F.map f y)) = g ((F.map f ≫ F.map k) y) := by
        simp only [ModuleCat.comp_apply]
      _ = g (F.map (f ≫ k) y) := by rw [F.map_comp]

/-- Evaluation at the identity arrow, `(coinduced X M)(X) ⟶ M`. -/
def coinducedEval (X : J) (M : ModuleCat.{v + 1} R) :
    (coinduced X M).obj X ⟶ M :=
  ModuleCat.ofHom (LinearMap.proj (𝟙 X))

/-- `coinducedFrom F X M g` followed by evaluation at the identity is `g`. -/
@[simp]
theorem coinducedFrom_eval [Small.{v + 1} R] (F : J ⥤ ModuleCat.{v + 1} R) (X : J)
    (M : ModuleCat.{v + 1} R) (g : F.obj X ⟶ M) :
    (coinducedFrom F X M g).app X ≫ coinducedEval X M = g := by
  apply ModuleCat.hom_ext
  ext x
  change g (F.map (𝟙 X) x) = g x
  simp

/-- Naturality of `coinducedFrom` in the diagram: precomposing `coinducedFrom G X M g` with
`f : F ⟶ G` gives `coinducedFrom F X M (f.app X ≫ g)`. -/
theorem comp_coinducedFrom {F G : J ⥤ ModuleCat.{v + 1} R} (f : F ⟶ G) (X : J)
    (M : ModuleCat.{v + 1} R) (g : G.obj X ⟶ M) :
    f ≫ coinducedFrom G X M g = coinducedFrom F X M (f.app X ≫ g) := by
  ext Y y
  funext k
  change g ((f.app Y ≫ G.map k) y) = g ((F.map k ≫ f.app X) y)
  rw [f.naturality]

/-- Every morphism `α : F ⟶ coinduced X M` is recovered by `coinducedFrom` from its
component at `X` followed by evaluation at `𝟙 X`. -/
theorem coinducedFrom_app_comp_eval {F : J ⥤ ModuleCat.{v + 1} R} {X : J}
    {M : ModuleCat.{v + 1} R} (α : F ⟶ coinduced X M) :
    coinducedFrom F X M (α.app X ≫ coinducedEval X M) = α := by
  ext Y y
  funext k
  change (F.map k ≫ α.app X) y (𝟙 X) = α.app Y y k
  rw [α.naturality]
  change α.app Y y (k ≫ 𝟙 X) = α.app Y y k
  rw [Category.comp_id]

variable [Small.{v + 1} R]

/-- A chosen embedding of a module into an injective module. -/
noncomputable def moduleInjectivePresentation (M : ModuleCat.{v + 1} R) :
    InjectivePresentation M :=
  Classical.choice (EnoughInjectives.presentation M)

/-- A coinduced diagram with injective coefficient is injective. -/
instance injective_coinduced (X : J) (M : ModuleCat.{v + 1} R) [Injective M] :
    Injective (coinduced X M) where
  factors α f hf := by
    have : Mono (f.app X) := (NatTrans.mono_iff_mono_app f).mp hf X
    refine ⟨coinducedFrom _ X M (Injective.factorThru (α.app X ≫ coinducedEval X M) (f.app X)),
      ?_⟩
    rw [comp_coinducedFrom, Injective.comp_factorThru, coinducedFrom_app_comp_eval]

/-- The family, indexed by `X : J`, of coinduced diagrams at `X` with
coefficients a chosen injective module containing `F(X)`. -/
noncomputable def coinducedInjectiveFamily (F : J ⥤ ModuleCat.{v + 1} R) :
    J → (J ⥤ ModuleCat.{v + 1} R) := fun X ↦
  coinduced X (moduleInjectivePresentation (F.obj X)).J

/-- The map from a module-valued diagram into the product of the coinduced
injective diagrams `coinducedInjectiveFamily F`; it is a monomorphism. -/
noncomputable def coinducedInjectiveEmbedding (F : J ⥤ ModuleCat.{v + 1} R) :
    F ⟶ ∏ᶜ coinducedInjectiveFamily F :=
  Pi.lift (fun X ↦
    coinducedFrom F X (moduleInjectivePresentation (F.obj X)).J
      (moduleInjectivePresentation (F.obj X)).f)

/-- The `X`-indexed component of `coinducedInjectiveEmbedding F` is the map `coinducedFrom`
associated with the chosen injective embedding of `F(X)`. -/
theorem coinducedInjectiveEmbedding_comp_π (F : J ⥤ ModuleCat.{v + 1} R) (X : J) :
    coinducedInjectiveEmbedding F ≫ Pi.π (coinducedInjectiveFamily F) X =
      coinducedFrom F X _ (moduleInjectivePresentation (F.obj X)).f :=
  Pi.lift_π _ X

/-- Module-valued functor categories have enough injectives.  The embedding
`coinducedInjectiveEmbedding F` is a monomorphism since, at `X`, its composite
with the projection to the `X`-indexed factor and evaluation at `𝟙 X` is the
injective embedding of `F(X)`. -/
instance hasEnoughInjectivesFunctorCategory :
    EnoughInjectives (J ⥤ ModuleCat.{v + 1} R) where
  presentation F := by
    have : ∀ X, Injective (coinducedInjectiveFamily F X) := fun X ↦ injective_coinduced _ _
    refine ⟨⟨∏ᶜ coinducedInjectiveFamily F, inferInstance, coinducedInjectiveEmbedding F, ?_⟩⟩
    rw [NatTrans.mono_iff_mono_app]
    intro X
    have : Mono ((coinducedFrom F X _ (moduleInjectivePresentation (F.obj X)).f).app X) :=
      mono_of_mono_fac (coinducedFrom_eval _ _ _ _)
    rw [← coinducedInjectiveEmbedding_comp_π, NatTrans.comp_app] at this
    exact @mono_of_mono _ _ _ _ _ _ _ this

end

/-! ## Limits of module-valued diagrams indexed by large categories -/

section LargeLimits

universe r s

variable {J : Type (s + 1)} [Category.{s, s + 1} J]
variable {R : Type r} [CommRing R]

/-- The submodule of compatible families in the product of the values of a
module-valued diagram. -/
def compatibleFamilySubmodule (F : J ⥤ ModuleCat.{s + 1} R) :
    Submodule R ((j : J) → F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f (x i) = x j}
  zero_mem' := by
    intro i j f
    simp
  add_mem' := by
    intro x y hx hy i j f
    simp [hx f, hy f]
  smul_mem' := by
    intro a x hx i j f
    simp [hx f]

/-- The module of compatible families, the cone point of the limit cone. -/
def compatibleFamilyLimitObject (F : J ⥤ ModuleCat.{s + 1} R) :
    ModuleCat.{s + 1} R :=
  ModuleCat.of R (compatibleFamilySubmodule F)

/-- The projection from compatible families to a value of the diagram. -/
def compatibleFamilyProjection (F : J ⥤ ModuleCat.{s + 1} R) (j : J) :
    compatibleFamilyLimitObject F ⟶ F.obj j :=
  ModuleCat.ofHom
    ((LinearMap.proj j).comp (compatibleFamilySubmodule F).subtype)

/-- The values of a cone over `F` at an element of its cone point form a compatible family. -/
theorem cone_π_app_mem_compatibleFamilySubmodule {F : J ⥤ ModuleCat.{s + 1} R} (S : Cone F)
    (x : S.pt) : (fun j ↦ S.π.app j x) ∈ compatibleFamilySubmodule F := fun i j f ↦ by
  have h := congrArg (fun t ↦ t x) (NatTrans.naturality S.π f)
  change S.π.app j x = F.map f (S.π.app i x) at h
  exact h.symm

/-- The limit cone of compatible families, for a module diagram indexed by a
category whose objects and morphisms lie in the universe of the modules. -/
def compatibleFamilyLimitCone (F : J ⥤ ModuleCat.{s + 1} R) : LimitCone F where
  cone :=
    { pt := compatibleFamilyLimitObject F
      π :=
        { app := compatibleFamilyProjection F
          naturality := fun i j f ↦ by
            ext x
            exact (x.2 f).symm } }
  isLimit := by
    refine IsLimit.mk (fun S ↦ ModuleCat.ofHom {
      toFun := fun x ↦ ⟨fun j ↦ S.π.app j x, cone_π_app_mem_compatibleFamilySubmodule S x⟩
      map_add' := fun x y ↦ by
        ext j
        simp
      map_smul' := fun a x ↦ by
        ext j
        simp }) (fun _ _ ↦ rfl) ?_
    intro S m hm
    ext x
    apply Subtype.ext
    funext j
    exact congrArg (fun f ↦ f x) (hm j)

/-- Module categories have limits of shape `J`, for categories `J` whose objects
lie in the universe of the modules, such as the categories of thickenings
underlying infinitesimal and crystalline sites. -/
instance hasLimitsOfShapeLargeModuleCat :
    HasLimitsOfShape J (ModuleCat.{s + 1} R) := by
  refine ⟨fun F ↦ ⟨⟨compatibleFamilyLimitCone F⟩⟩⟩

/-- The limit functor on module-valued diagrams is additive. -/
instance limModuleCatAdditive :
    (lim : ((J ⥤ ModuleCat.{s + 1} R) ⥤ ModuleCat.{s + 1} R)).Additive where
  map_add := by
    intro F G f g
    apply limit.hom_ext
    intro j
    change limMap (f + g) ≫ limit.π G j =
      (limMap f + limMap g) ≫ limit.π G j
    simp [limMap_π, Preadditive.add_comp, Preadditive.comp_add]

end LargeLimits

end AffineCrystalline.Cohomology
