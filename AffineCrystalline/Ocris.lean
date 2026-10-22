/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.Ring.Basic
import AffineCrystalline.InfinitesimalSite.Envelope

/-!
# The structure sheaf `ocris`

Let `E` be an envelope family: a choice, for every object `X = (B → C)` of the
big infinitesimal site `INF(C/A)`, of a compatible divided power envelope
`D_X` of `B` along the kernel `J_X` of `B → C`. A morphism `f : X → Y` induces
a unique divided power morphism `c(f) : D_X → D_Y` compatible with `f`
(`EnvelopeChoice.comparison`), and uniqueness gives `c(id) = id` and
`c(g ∘ f) = c(g) ∘ c(f)`. This defines the structure sheaf `Ocris : X ↦ D_X`,
as a presheaf of types and as a presheaf of commutative rings on the site.
Two envelope families give canonically isomorphic presheaves, so nothing
depends on the choice.

The category `InfinitesimalThickening A C` is written with covariant algebra
maps, and the site is its opposite `Site`. A presheaf on the site is therefore
a functor out of `Siteᵒᵖ`, and the restriction maps of `ocris` are exactly the
comparison maps `c(f)`.

## Main definitions

* `Site`: the site `INF(C/A)ᵒᵖ`.
* `EnvelopeFamily`: a choice of compatible divided power envelope at every
  object; `EnvelopeFamily.ofExistenceData` builds one from existence data.
* `EnvelopeFamily.ocris`, `EnvelopeFamily.ocrisCommRing`: the structure sheaf,
  valued in types and in commutative rings.
* `EnvelopeFamily.IsSheaf`: the sheaf condition for `ocris` with respect to a
  Grothendieck topology.

## Main results

* `EnvelopeFamily.ocris_map_spec`: the restriction maps are compatible with the
  structure maps `B → D_X`.
* `EnvelopeFamily.envelopeFamilyIso`, `EnvelopeFamily.ocrisFamilyIso`:
  independence of the envelope family.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open CategoryTheory

universe u

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-- The big infinitesimal site `INF(C/A)` in the site orientation: the opposite
of the category of thickenings `B → C` and algebra maps over `C`. -/
abbrev Site := (InfinitesimalThickening A C)ᵒᵖ

/-! ## Envelope families -/

/-- An envelope family: a choice of a compatible divided power envelope
(`EnvelopeChoice`) at every object of `INF(C/A)`. -/
structure EnvelopeFamily where
  envelope : ∀ X : InfinitesimalThickening A C, EnvelopeChoice (γ := γ) X

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))

/-- The envelope family obtained by choosing, at every object, an envelope whose
existence is asserted by `H`. All maps between envelopes are then determined
by the universal property. -/
noncomputable def ofExistenceData
    (H : EnvelopeExistenceData (A := A) (C := C) (γ := γ)) :
    EnvelopeFamily (A := A) (C := C) (γ := γ) where
  envelope X :=
    EnvelopeChoice.ofDPEnvelopeChoice X
      (Classical.choice (H.exists_envelope X))

@[simp]
theorem envelope_carrier (X : InfinitesimalThickening A C) :
    (E.envelope X).carrier = (E.envelope X).carrier := rfl

/-! ## The presheaf `ocris` -/

/-- The structure sheaf `ocris` as a presheaf of types on the site. It sends `X`
to the chosen envelope `D_X`, and a morphism `f` to the comparison map
`c(f) : D_X → D_Y` given by the universal property. -/
noncomputable def ocris (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ Type u where
  obj X := (E.envelope X.unop.unop).carrier
  map := fun {X Y} f ↦
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun x ↦
      EnvelopeChoice.comparison f.unop.unop
        (E.envelope X.unop.unop) (E.envelope Y.unop.unop) x))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change EnvelopeChoice.comparison (𝟙 X.unop.unop)
        (E.envelope X.unop.unop) (E.envelope X.unop.unop)
        x = x
    simpa using congrArg (fun f ↦ f x)
      (EnvelopeChoice.comparison_id (E.envelope X.unop.unop))
  map_comp := by
    intro X Y Z f g
    apply ConcreteCategory.hom_ext
    intro x
    change EnvelopeChoice.comparison (f.unop.unop ≫ g.unop.unop)
        (E.envelope X.unop.unop) (E.envelope Z.unop.unop) x =
      EnvelopeChoice.comparison g.unop.unop
          (E.envelope Y.unop.unop) (E.envelope Z.unop.unop)
        (EnvelopeChoice.comparison f.unop.unop
          (E.envelope X.unop.unop) (E.envelope Y.unop.unop) x)
    exact congrArg (fun h ↦ h x)
      (EnvelopeChoice.comparison_comp f.unop.unop g.unop.unop
        (E.envelope X.unop.unop)
        (E.envelope Y.unop.unop)
        (E.envelope Z.unop.unop))

@[simp]
theorem ocris_obj (X : Site (A := A) (C := C)ᵒᵖ) :
    (ocris E).obj X = (E.envelope X.unop.unop).carrier := rfl

/-- The restriction map of `ocris` along `f` sends the image of `x` in `D_X` to the
image of `f x` in `D_Y`. -/
@[simp]
theorem ocris_map_spec
    {X Y : Site (A := A) (C := C)ᵒᵖ} (f : X ⟶ Y) :
    ∀ x,
    (ConcreteCategory.hom ((ocris E).map f)) ((E.envelope X.unop.unop).map x) =
        (E.envelope Y.unop.unop).map (f.unop.unop.toAlgHom x) := by
  intro x
  change EnvelopeChoice.comparison f.unop.unop
      (E.envelope X.unop.unop) (E.envelope Y.unop.unop)
      ((E.envelope X.unop.unop).map x) = _
  exact DFunLike.congr_fun
    (EnvelopeChoice.comparison_spec f.unop.unop
      (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).1 x

/-! ## The ring-valued presheaf -/

/-- The structure sheaf `ocris` as a presheaf of commutative rings: every
restriction map `c(f)` is a ring homomorphism. Its underlying presheaf of
types is `ocris` (`ocris_eq_ocrisCommRing_comp_forget`). -/
noncomputable def ocrisCommRing
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (E.envelope X.unop.unop).carrier
  map := fun {X Y} f ↦
    CommRingCat.ofHom
      (EnvelopeChoice.comparison f.unop.unop
        (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).toRingHom
  map_id X := by
    apply CommRingCat.hom_ext
    change (EnvelopeChoice.comparison (𝟙 X.unop.unop)
        (E.envelope X.unop.unop) (E.envelope X.unop.unop)).toRingHom = _
    rw [EnvelopeChoice.comparison_id]
    rfl
  map_comp := by
    intro X Y Z f g
    apply CommRingCat.hom_ext
    change (EnvelopeChoice.comparison (f.unop.unop ≫ g.unop.unop)
        (E.envelope X.unop.unop) (E.envelope Z.unop.unop)).toRingHom =
      (EnvelopeChoice.comparison g.unop.unop
        (E.envelope Y.unop.unop) (E.envelope Z.unop.unop)).toRingHom.comp
        (EnvelopeChoice.comparison f.unop.unop
          (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).toRingHom
    change
      (EnvelopeChoice.comparison
        (InfinitesimalThickening.Hom.comp f.unop.unop g.unop.unop)
        (E.envelope X.unop.unop) (E.envelope Z.unop.unop)).toRingHom = _
    rw [EnvelopeChoice.comparison_comp]
    rfl

/-- The presheaf `ocris` of the envelope family chosen from existence data `H`. -/
noncomputable def ocrisOfExistenceData
    (H : EnvelopeExistenceData (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ Type u :=
  ocris (ofExistenceData H)

/-- The presheaf of rings `ocrisCommRing` of the envelope family chosen from
existence data `H`. -/
noncomputable def ocrisCommRingOfExistenceData
    (H : EnvelopeExistenceData (A := A) (C := C) (γ := γ)) :
    Site (A := A) (C := C)ᵒᵖ ⥤ CommRingCat.{u} :=
  ocrisCommRing (ofExistenceData H)

@[simp]
theorem ocrisCommRing_obj (X : Site (A := A) (C := C)ᵒᵖ) :
    (ocrisCommRing E).obj X =
      CommRingCat.of (E.envelope X.unop.unop).carrier := rfl

theorem ocrisCommRing_map_spec
    {X Y : Site (A := A) (C := C)ᵒᵖ} (f : X ⟶ Y) :
    (ocrisCommRing E).map f =
      CommRingCat.ofHom
        (EnvelopeChoice.comparison f.unop.unop
          (E.envelope X.unop.unop) (E.envelope Y.unop.unop)).toRingHom := rfl

/-- The envelopes chosen by two families at the same object are canonically
isomorphic, by the comparison maps along the identity in both directions. -/
noncomputable def envelopeIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ))
    (X : InfinitesimalThickening A C) :
    CommRingCat.of (E.envelope X).carrier ≅
      CommRingCat.of (F.envelope X).carrier where
  hom := CommRingCat.ofHom
    (EnvelopeChoice.comparison (𝟙 X) (E.envelope X) (F.envelope X)).toRingHom
  inv := CommRingCat.ofHom
    (EnvelopeChoice.comparison (𝟙 X) (F.envelope X) (E.envelope X)).toRingHom
  hom_inv_id := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg (fun h ↦ CommRingCat.ofHom h.toRingHom)
      (EnvelopeChoice.comparison_comp_comparison_left X
        (E.envelope X) (F.envelope X))
  inv_hom_id := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg (fun h ↦ CommRingCat.ofHom h.toRingHom)
      (EnvelopeChoice.comparison_comp_comparison_right X
        (E.envelope X) (F.envelope X))

/-- The presheaf of rings `ocrisCommRing` is independent of the envelope family,
up to canonical natural isomorphism. Naturality follows from
`EnvelopeChoice.comparison_comp`. -/
noncomputable def envelopeFamilyIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocrisCommRing E ≅ ocrisCommRing F :=
  NatIso.ofComponents (fun X ↦ envelopeIso E F X.unop.unop) fun {X Y} f ↦ by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (EnvelopeChoice.comparison_id_comp_comparison f.unop.unop (E.envelope X.unop.unop)
        (F.envelope X.unop.unop) (E.envelope Y.unop.unop) (F.envelope Y.unop.unop))

/-! ## The underlying presheaf of types -/

/-- `ocris` is the underlying presheaf of types of `ocrisCommRing`. -/
theorem ocris_eq_ocrisCommRing_comp_forget (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocris E =
      ocrisCommRing E ⋙ CategoryTheory.forget CommRingCat := by
  refine CategoryTheory.Functor.ext (F := ocris E)
    (G := ocrisCommRing E ⋙ CategoryTheory.forget CommRingCat) ?_ ?_
  · intro X
    rfl
  · intro X Y f
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- The presheaf of types `ocris` is independent of the envelope family, up to
natural isomorphism. -/
noncomputable def ocrisFamilyIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocris E ≅ ocris F := by
  rw [ocris_eq_ocrisCommRing_comp_forget E, ocris_eq_ocrisCommRing_comp_forget F]
  exact NatIso.ofComponents
    (fun X ↦ (CategoryTheory.forget CommRingCat).mapIso
      (envelopeIso E F X.unop.unop)) (by
      intro X Y f
      change
        (CategoryTheory.forget CommRingCat).map ((ocrisCommRing E).map f) ≫
            (CategoryTheory.forget CommRingCat).map
              ((envelopeFamilyIso E F).hom.app Y) =
          (CategoryTheory.forget CommRingCat).map
              ((envelopeFamilyIso E F).hom.app X) ≫
            (CategoryTheory.forget CommRingCat).map ((ocrisCommRing F).map f)
      rw [← (CategoryTheory.forget CommRingCat).map_comp,
        ← (CategoryTheory.forget CommRingCat).map_comp]
      exact congrArg (fun k ↦ (CategoryTheory.forget CommRingCat).map k)
        ((envelopeFamilyIso E F).hom.naturality f))

/-! ## The sheaf condition -/

/-- The sheaf condition for `ocris` with respect to a Grothendieck topology `J`
on the site. For the chaotic topology it holds for every envelope family
(`TopologyData.isOcrisSheaf_chaotic`). -/
def IsSheaf (J : GrothendieckTopology (Site (A := A) (C := C))) : Prop :=
  Presheaf.IsSheaf J (ocris E)

end EnvelopeFamily

end AffineCrystalline.InfinitesimalSite

namespace AffineCrystalline

/-! ## Root-level names -/

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-- The structure sheaf `ocris` of an envelope family, as a presheaf of types on
the site `INF(C/A)ᵒᵖ`. -/
noncomputable def ocris
    (E : InfinitesimalSite.EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    (InfinitesimalSite.Site (A := A) (C := C))ᵒᵖ ⥤ Type u :=
  InfinitesimalSite.EnvelopeFamily.ocris E

/-- The structure sheaf `ocris` of an envelope family, as a presheaf of
commutative rings on the site `INF(C/A)ᵒᵖ`. -/
noncomputable def ocrisCommRing
    (E : InfinitesimalSite.EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    (InfinitesimalSite.Site (A := A) (C := C))ᵒᵖ ⥤ CommRingCat.{u} :=
  InfinitesimalSite.EnvelopeFamily.ocrisCommRing E

@[simp]
theorem ocris_eq_envelopeFamily (E :
    InfinitesimalSite.EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocris E = InfinitesimalSite.EnvelopeFamily.ocris E := rfl

end AffineCrystalline
