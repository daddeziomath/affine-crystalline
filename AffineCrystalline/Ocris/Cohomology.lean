/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris
import AffineCrystalline.Cohomology.FunctorCategoryInjectives
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Derived global sections of `ocris`

We regard the structure sheaf `ocris` of the big infinitesimal site `INF(C/A)`
as a diagram of `A`-modules (`ocrisModule`, and its universe-lifted version
`ocrisModuleLarge`) and as a diagram of cochain complexes concentrated in
degree zero (`ocrisComplex`).  The cohomology of `ocris` on `INF(C/A)` is the
right-derived functor of the limit,

  `RΓ(INF(C/A), Ocris) = R lim Ocris`   (`ocrisDerivedGlobalSections`),

which is cohomology for the chaotic topology, in which every presheaf is a
sheaf; the higher derived limits need not vanish.  All constructions are
independent of the chosen envelope family up to canonical isomorphism.

## Main definitions

* `Cohomology.additiveDerivedIso`, `Cohomology.mapInjectiveResolution`,
  `Cohomology.rightDerivedToHomotopyCategoryCompIso`: general facts on
  right-derived functors.
* `EnvelopeFamily.ocrisModule`, `EnvelopeFamily.ocrisModuleLarge`,
  `EnvelopeFamily.ocrisComplex`: `ocris` as a module diagram and as a diagram
  of complexes.
* `EnvelopeFamily.ocrisGlobalSections`, `EnvelopeFamily.ocrisDerivedGlobalSections`:
  `Γ(INF(C/A), Ocris)` and `RΓ(INF(C/A), Ocris)`.
* `EnvelopeFamily.ocrisModuleLargeIso`, `EnvelopeFamily.ocrisDerivedGlobalSectionsIso`:
  independence of the envelope family.

## References

* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
-/

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AffineCrystalline.Cohomology

universe v₁ u₁ v₂ u₂

/-- A natural isomorphism between additive functors induces an isomorphism
between their right-derived functors to the homotopy category. -/
noncomputable def additiveDerivedIso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.rightDerivedToHomotopyCategory ≅ G.rightDerivedToHomotopyCategory :=
  NatIso.ofComponents (fun X ↦ {
    hom := (NatTrans.rightDerivedToHomotopyCategory e.hom).app X
    inv := (NatTrans.rightDerivedToHomotopyCategory e.inv).app X
    hom_inv_id := by
      have h := congrArg (fun η ↦ η.app X)
        (NatTrans.rightDerivedToHomotopyCategory_comp e.hom e.inv)
      calc
        _ = (NatTrans.rightDerivedToHomotopyCategory (e.hom ≫ e.inv)).app X := h.symm
        _ = _ := by simp
    inv_hom_id := by
      have h := congrArg (fun η ↦ η.app X)
        (NatTrans.rightDerivedToHomotopyCategory_comp e.inv e.hom)
      calc
        _ = (NatTrans.rightDerivedToHomotopyCategory (e.inv ≫ e.hom)).app X := h.symm
        _ = _ := by simp }) (by
    intro X Y f
    exact (NatTrans.rightDerivedToHomotopyCategory e.hom).naturality f)

end AffineCrystalline.Cohomology

namespace AffineCrystalline.Cohomology

universe vC uC vD uD vE uE

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
variable {E : Type uE} [Category.{vE} E] [Abelian E]

/-- An exact additive functor that sends injectives to injectives transports
injective resolutions.  The augmentation is transported through the canonical
identification of the image of a complex concentrated in degree zero with the
complex concentrated in degree zero on the image object. -/
noncomputable def mapInjectiveResolution
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hinj : ∀ (X : C), Injective X → Injective (F.obj X))
    {X : C} (I : InjectiveResolution X) : InjectiveResolution (F.obj X) := by
  let c := ComplexShape.up ℕ
  let Fhc := F.mapHomologicalComplex c
  let singleIso := HomologicalComplex.singleMapHomologicalComplex F c 0
  let mappedι := singleIso.inv.app X ≫ Fhc.map I.ι
  have hpres : F.PreservesHomology := Functor.preservesHomologyOfExact F
  letI := hpres
  have hmap : QuasiIso (Fhc.map I.ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology I.ι F
  have hsingle : QuasiIso (singleIso.inv.app X) := by infer_instance
  exact {
    cocomplex := Fhc.obj I.cocomplex
    injective := fun n ↦ hinj _ (I.injective n)
    ι := mappedι
    quasiIso := by
      dsimp [mappedι]
      letI : QuasiIso (Fhc.map I.ι) := hmap
      letI : QuasiIso (singleIso.inv.app X) := hsingle
      infer_instance }

/-- If `F` is exact and preserves injectives, then `R(F ⋙ G) ≅ RG ∘ F` (as
functors to the homotopy category).  Both sides are computed from the image
under `F` of an injective resolution. -/
noncomputable def rightDerivedToHomotopyCategoryCompIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hinj : ∀ (X : C), Injective X → Injective (F.obj X))
    (G : D ⥤ E) [G.Additive] (X : C) :
    (F ⋙ G).rightDerivedToHomotopyCategory.obj X ≅
      G.rightDerivedToHomotopyCategory.obj (F.obj X) := by
  let I := injectiveResolution X
  let J := mapInjectiveResolution F hinj I
  let ecomp := Functor.mapHomologicalComplexCompIso
      (Iso.refl (F ⋙ G)) (ComplexShape.up ℕ)
  let q := HomotopyCategory.quotient E (ComplexShape.up ℕ)
  exact I.isoRightDerivedToHomotopyCategoryObj (F ⋙ G) ≪≫
    (q.mapIso (ecomp.app I.cocomplex)).symm ≪≫
    (J.isoRightDerivedToHomotopyCategoryObj G).symm

end AffineCrystalline.Cohomology

namespace AffineCrystalline.InfinitesimalSite
namespace EnvelopeFamily

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-- The presheaf of `A`-modules underlying `ocris`.

The restriction maps are the comparison maps between envelopes given by the
universal property, as in `ocrisCommRing`, regarded as `A`-linear maps. -/
noncomputable def ocrisModule
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ ModuleCat.{u} A where
  obj X := ModuleCat.of A (E.envelope X.unop.unop).carrier
  map := fun {X Y} f ↦ ModuleCat.ofHom
    (EnvelopeChoice.comparison f.unop.unop
      (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    exact congrArg AlgHom.toLinearMap
      (EnvelopeChoice.comparison_id (E.envelope X.unop.unop))
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    exact congrArg AlgHom.toLinearMap
      (EnvelopeChoice.comparison_comp f.unop.unop g.unop.unop
        (E.envelope X.unop.unop)
        (E.envelope Y.unop.unop)
        (E.envelope Z.unop.unop))

@[simp]
theorem ocrisModule_obj
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    (X : Site (A := A) (C := C)ᵒᵖ) :
    (ocrisModule E).obj X =
      ModuleCat.of A (E.envelope X.unop.unop).carrier :=
  rfl

@[simp]
theorem ocrisModule_map
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    {X Y : Site (A := A) (C := C)ᵒᵖ} (f : X ⟶ Y) :
    (ocrisModule E).map f = ModuleCat.ofHom
      (EnvelopeChoice.comparison f.unop.unop
        (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).toLinearMap :=
  rfl

/-- Raise a linear map to the next universe.  This is needed because the
category `INF(C/A)` of thickenings with carriers in `Type u` lives in
`Type (u + 1)`, one universe above each envelope. -/
def uliftLinearMap {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    ULift.{u + 1, u} M →ₗ[A] ULift.{u + 1, u} N where
  toFun x := ULift.up (f x.down)
  map_add' x y := by
    apply ULift.down_injective
    exact f.map_add x.down y.down
  map_smul' a x := by
    apply ULift.down_injective
    exact f.map_smul a x.down

/-- The presheaf of `A`-modules underlying `ocris`, with values raised to
`ModuleCat.{u + 1} A`.

The category `INF(C/A)` of thickenings with carriers in `Type u` lives in
`Type (u + 1)`, so limits over it are formed in `ModuleCat.{u + 1} A`. -/
noncomputable def ocrisModuleLarge
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ ModuleCat.{u + 1} A where
  obj X := ModuleCat.of A
    (ULift.{u + 1, u} (E.envelope X.unop.unop).carrier)
  map := fun {X Y} f ↦ ModuleCat.ofHom <| uliftLinearMap
    (EnvelopeChoice.comparison f.unop.unop
      (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    change EnvelopeChoice.comparison (𝟙 X.unop.unop)
        (E.envelope X.unop.unop) (E.envelope X.unop.unop) x.down = x.down
    simpa using congrArg (fun h ↦ h x.down)
      (EnvelopeChoice.comparison_id (E.envelope X.unop.unop))
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    ext x
    change EnvelopeChoice.comparison (f.unop.unop ≫ g.unop.unop)
        (E.envelope X.unop.unop) (E.envelope Z.unop.unop) x.down =
      EnvelopeChoice.comparison g.unop.unop
        (E.envelope Y.unop.unop) (E.envelope Z.unop.unop)
        (EnvelopeChoice.comparison f.unop.unop
          (E.envelope X.unop.unop) (E.envelope Y.unop.unop) x.down)
    exact congrArg (fun h ↦ h x.down)
      (EnvelopeChoice.comparison_comp f.unop.unop g.unop.unop
        (E.envelope X.unop.unop)
        (E.envelope Y.unop.unop)
        (E.envelope Z.unop.unop))

/-- The module diagram `ocrisModuleLarge` is independent of the chosen envelope
family, up to canonical isomorphism. -/
noncomputable def ocrisModuleLargeIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocrisModuleLarge E ≅ ocrisModuleLarge F :=
  NatIso.ofComponents
    (fun X ↦
      { hom := ModuleCat.ofHom <| uliftLinearMap
          (EnvelopeChoice.comparison (𝟙 X.unop.unop)
            (E.envelope X.unop.unop) (F.envelope X.unop.unop)).toLinearMap
        inv := ModuleCat.ofHom <| uliftLinearMap
          (EnvelopeChoice.comparison (𝟙 X.unop.unop)
            (F.envelope X.unop.unop) (E.envelope X.unop.unop)).toLinearMap
        hom_inv_id := by
          apply ModuleCat.hom_ext
          ext x
          exact ULift.ext _ _ <| congrArg (fun h ↦ h x.down)
            (EnvelopeChoice.comparison_comp_comparison_left X.unop.unop
              (E.envelope X.unop.unop) (F.envelope X.unop.unop))
        inv_hom_id := by
          apply ModuleCat.hom_ext
          ext x
          exact ULift.ext _ _ <| congrArg (fun h ↦ h x.down)
            (EnvelopeChoice.comparison_comp_comparison_right X.unop.unop
              (E.envelope X.unop.unop) (F.envelope X.unop.unop)) })
    (fun {X Y} f ↦ by
      apply ModuleCat.hom_ext
      ext x
      exact ULift.ext _ _ <| congrArg (fun h ↦ h x.down)
        (EnvelopeChoice.comparison_id_comp_comparison f.unop.unop (E.envelope X.unop.unop)
          (F.envelope X.unop.unop) (E.envelope Y.unop.unop) (F.envelope Y.unop.unop)))

/-- `ocris`, regarded as a diagram of cochain complexes of
`ModuleCat.{u + 1} A` concentrated in degree zero. -/
noncomputable def ocrisComplex
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℕ :=
  ocrisModuleLarge E ⋙ CochainComplex.single₀ (ModuleCat.{u + 1} A)

@[simp]
theorem ocrisComplex_obj
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    (X : Site (A := A) (C := C)ᵒᵖ) :
    (ocrisComplex E).obj X =
      (CochainComplex.single₀ (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A
          (ULift.{u + 1, u} (E.envelope X.unop.unop).carrier)) :=
  rfl

/-- The global sections `Γ(INF(C/A), Ocris)`, the limit of `ocris` over
`INF(C/A)`. -/
noncomputable def ocrisGlobalSections
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ModuleCat.{u + 1} A :=
  limit (ocrisModuleLarge E)

/-- The derived global sections `RΓ(INF(C/A), Ocris)`: the right-derived
functor of the limit over `INF(C/A)`, applied to `ocris`, as an object of the
homotopy category of cochain complexes. -/
noncomputable def ocrisDerivedGlobalSections
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    HomotopyCategory (ModuleCat.{u + 1} A) (ComplexShape.up ℕ) :=
  ((lim :
      ((InfinitesimalThickening A C) ⥤ ModuleCat.{u + 1} A) ⥤
        ModuleCat.{u + 1} A).rightDerivedToHomotopyCategory).obj
    (CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E)

/-- Derived global sections are independent of the chosen envelope family. -/
noncomputable def ocrisDerivedGlobalSectionsIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocrisDerivedGlobalSections E ≅ ocrisDerivedGlobalSections F :=
  ((lim :
      ((InfinitesimalThickening A C) ⥤ ModuleCat.{u + 1} A) ⥤
        ModuleCat.{u + 1} A).rightDerivedToHomotopyCategory).mapIso
    (Functor.isoWhiskerLeft (CategoryTheory.opOp (InfinitesimalThickening A C))
      (ocrisModuleLargeIso E F))

/-- Global sections are independent of the chosen envelope family. -/
noncomputable def ocrisGlobalSectionsIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocrisGlobalSections E ≅ ocrisGlobalSections F :=
  HasLimit.isoOfNatIso (ocrisModuleLargeIso E F)

/-- The projection from global sections to the value of `ocris` at a
thickening. -/
noncomputable def ocrisGlobalSectionsπ
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    (X : Site (A := A) (C := C)ᵒᵖ) :
    ocrisGlobalSections E ⟶ (ocrisModuleLarge E).obj X :=
  limit.π (ocrisModuleLarge E) X

end EnvelopeFamily
end AffineCrystalline.InfinitesimalSite
