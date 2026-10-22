/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# The big infinitesimal site

Let `A` be a ring and `C` an `A`-algebra. The big infinitesimal site
`INF(C/A)` (`InfinitesimalThickening A C`) has as objects the surjections of
`A`-algebras `π : B → C` whose kernel has a bounded nilpotence exponent:
there is `e` with `x ^ e = 0` for all `x ∈ ker π`. Its morphisms are the
`A`-algebra maps over `C`. Objects carry no divided powers and no chosen
polynomial presentation.

## Main definitions

* `InfinitesimalThickening A C`: the category `INF(C/A)`.
* `InfinitesimalThickening.Hom`: morphisms of `INF(C/A)`.
-/

open scoped CategoryTheory

namespace AffineCrystalline.InfinitesimalSite

universe u

/-! ## Infinitesimal thickenings -/

/-- An object of the big infinitesimal site `INF(C/A)`: a surjection of
`A`-algebras `π : B → C` whose kernel has a bounded nilpotence exponent, that
is, there is `e` with `x ^ e = 0` for every `x ∈ ker π`.

The minimal such `e` is `exp(X)` (`exponent`), and the full subcategories
`INF^{(e)}` of objects of exponent `e` (`Level A C e`) filter the site
(`InfinitesimalSite/Filtration.lean`). -/
structure InfinitesimalThickening (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra A carrier]
  π : carrier →ₐ[A] C
  surjective : Function.Surjective π
  kernel_bounded :
    ∃ e : ℕ, ∀ x : carrier, x ∈ RingHom.ker π.toRingHom → x ^ e = 0

namespace InfinitesimalThickening

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

instance carrierCommRing (X : InfinitesimalThickening A C) : CommRing X.carrier :=
  X.commRing

instance carrierAlgebra (X : InfinitesimalThickening A C) : Algebra A X.carrier :=
  X.algebra

/-- A morphism of `INF(C/A)`: an `A`-algebra map `f : B → B'` with `π' ∘ f = π`. -/
@[ext]
structure Hom (X Y : InfinitesimalThickening A C) where
  toAlgHom : X.carrier →ₐ[A] Y.carrier
  overC : Y.π.comp toAlgHom = X.π

namespace Hom

theorem overC_apply {X Y : InfinitesimalThickening A C} (f : Hom X Y)
    (x : X.carrier) : Y.π (f.toAlgHom x) = X.π x := by
  exact DFunLike.congr_fun f.overC x

/-- Composition of morphisms of `INF(C/A)`. -/
def comp {X Y Z : InfinitesimalThickening A C} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z :=
  { toAlgHom := g.toAlgHom.comp f.toAlgHom
    overC := by rw [← AlgHom.comp_assoc, g.overC, f.overC] }

end Hom

instance : CategoryTheory.Category (InfinitesimalThickening A C) where
  Hom X Y := Hom X Y
  id X :=
    { toAlgHom := AlgHom.id A X.carrier
      overC := by simp }
  comp f g := Hom.comp f g
  id_comp f := by
    apply Hom.ext
    exact AlgHom.id_comp f.toAlgHom
  comp_id f := by
    apply Hom.ext
    exact AlgHom.comp_id f.toAlgHom
  assoc f g h := by
    apply Hom.ext
    exact (AlgHom.comp_assoc h.toAlgHom g.toAlgHom f.toAlgHom).symm

end InfinitesimalThickening

end AffineCrystalline.InfinitesimalSite
