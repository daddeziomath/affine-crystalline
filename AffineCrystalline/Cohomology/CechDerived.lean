/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Cohomology.Cech

/-!
# Čech computation of higher derived limits

Let `J` be a category with Čech nerve data (`CechNerveData`): a cosimplicial
object `X` of `J` with `Hom(X[n], Z) ≃ S(Z)^(n+1)` for nonempty sets `S(Z)`.
Then the right-derived functors of `lim` on module-valued diagrams are computed
by Čech complexes:

```text
Rⁿ lim F ≅ Hⁿ(F(X[0]) ⟶ F(X[1]) ⟶ F(X[2]) ⟶ ⋯).
```

This combines the zigzag of quasi-isomorphisms `cechZigzag`
(`lim I^• ⟶ Tot ⟵ Č^•(F)`) with Mathlib's computation of right-derived functors
by injective resolutions.

## Main definitions

* `Zigzag.homologyIso`: the isomorphism on cohomology induced by a zigzag of
  quasi-isomorphisms.
* `limComplexHomologyIsoCech`: `Hⁿ(lim I^•) ≅ Hⁿ(Č^•(F))` for any injective
  resolution `I` of `F`.
* `rightDerivedLimIsoCech`: `Rⁿ lim F ≅ Hⁿ(Č^•(F))`.
* `limIsoCechHomologyZero`: `lim F ≅ H⁰(Č^•(F))`.

## Main results

* `cech_homology_isZero_of_injective`: the Čech cohomology of an injective
  diagram vanishes in positive degrees.

## References

* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AffineCrystalline.Cohomology.Cech

variable {J : Type (v + 1)} [Category.{v} J] (D : CechNerveData J)
variable {R : Type u} [CommRing R]

/-- A zigzag of quasi-isomorphisms induces isomorphisms on cohomology. -/
noncomputable def Zigzag.homologyIso {A B : CochainComplex (ModuleCat.{v + 1} R) ℕ}
    (z : Zigzag A B) (n : ℕ) : A.homology n ≅ B.homology n :=
  have := z.left_quasiIso
  have := z.right_quasiIso
  isoOfQuasiIsoAt z.left n ≪≫ (isoOfQuasiIsoAt z.right n).symm

/-- For any injective resolution `I` of `F`, the cohomology of `lim I^•` is
isomorphic to the Čech cohomology of `F`. -/
noncomputable def limComplexHomologyIsoCech {F : J ⥤ ModuleCat.{v + 1} R}
    (I : InjectiveResolution F) (n : ℕ) :
    (limComplex I).homology n ≅ (cech D F).homology n :=
  (cechZigzag D I).homologyIso n

variable [Small.{v + 1} R]

/-- **Higher derived limits are Čech cohomology.**  For every module diagram
`F` on a category with Čech nerve data, `Rⁿ lim F ≅ Hⁿ(Č^•(F))` for all `n`. -/
noncomputable def rightDerivedLimIsoCech (F : J ⥤ ModuleCat.{v + 1} R) (n : ℕ) :
    ((lim : (J ⥤ ModuleCat.{v + 1} R) ⥤ ModuleCat.{v + 1} R).rightDerived n).obj F ≅
      (cech D F).homology n :=
  (injectiveResolution F).isoRightDerivedObj (lim : (J ⥤ ModuleCat.{v + 1} R) ⥤ _) n ≪≫
    limComplexHomologyIsoCech D (injectiveResolution F) n

/-- In degree zero: `lim F ≅ H⁰(Č^•(F))`. -/
noncomputable def limIsoCechHomologyZero (F : J ⥤ ModuleCat.{v + 1} R) :
    (lim : (J ⥤ ModuleCat.{v + 1} R) ⥤ ModuleCat.{v + 1} R).obj F ≅
      (cech D F).homology 0 :=
  (asIso ((lim : (J ⥤ ModuleCat.{v + 1} R) ⥤ ModuleCat.{v + 1} R).toRightDerivedZero)).app F ≪≫
    rightDerivedLimIsoCech D F 0

/-- The Čech cohomology of an injective module diagram vanishes in positive
degrees. -/
theorem cech_homology_isZero_of_injective (F : J ⥤ ModuleCat.{v + 1} R) [Injective F]
    (n : ℕ) : IsZero ((cech D F).homology (n + 1)) :=
  (Functor.isZero_rightDerived_obj_injective_succ
    (lim : (J ⥤ ModuleCat.{v + 1} R) ⥤ ModuleCat.{v + 1} R) n F).of_iso
    (rightDerivedLimIsoCech D F (n + 1)).symm

end AffineCrystalline.Cohomology.Cech
