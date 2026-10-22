/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import AffineCrystalline.Ocris

/-!
# The chaotic topology on the infinitesimal site

The big infinitesimal site `INF(C/A)` lives over the fixed affine scheme
`Spec C`, and we equip it with the chaotic topology: Mathlib's bottom
Grothendieck topology on `Site = INF(C/A)ᵒᵖ`, for which only the maximal sieves
cover. Every presheaf is a sheaf for it, in particular `ocris`. This does not
make higher cohomology vanish: cohomology is the right derived functor of the
limit (`Ocris/Cohomology.lean`).

## Main definitions

* `TopologyData`: a Grothendieck topology on the site.
* `TopologyData.chaotic`: the chaotic topology.
* `OcrisSheafData T`: an envelope family whose `ocris` is a sheaf for `T`.

## Main results

* `TopologyData.isOcrisSheaf_chaotic`: `ocris` is a sheaf for the chaotic
  topology, for every envelope family.
-/

open CategoryTheory

universe u

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-! ## Topologies on the site -/

/-- A Grothendieck topology on the site `INF(C/A)ᵒᵖ`. -/
structure TopologyData where
  topology : GrothendieckTopology (Site (A := A) (C := C))

namespace TopologyData

variable (T : TopologyData (A := A) (C := C))

/-! ## The chaotic topology -/

/-- The chaotic Grothendieck topology on `INF(C/A)ᵒᵖ`: only the maximal sieves
cover. -/
noncomputable def chaotic : TopologyData (A := A) (C := C) where
  topology := ⊥

@[simp]
theorem chaotic_topology :
    (chaotic (A := A) (C := C)).topology =
      (⊥ : GrothendieckTopology (Site (A := A) (C := C))) :=
  rfl

/-- The sheaf condition for `ocris` with respect to the topology `T`. -/
def IsOcrisSheaf (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) : Prop :=
  EnvelopeFamily.IsSheaf E T.topology

/-- For every envelope family, `ocris` is a sheaf for the chaotic topology. -/
theorem isOcrisSheaf_chaotic
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    (chaotic (A := A) (C := C)).IsOcrisSheaf E := by
  change Presheaf.IsSheaf (⊥ : GrothendieckTopology (Site (A := A) (C := C)))
    (EnvelopeFamily.ocris E)
  exact Presheaf.isSheaf_bot _

end TopologyData

/-! ## `ocris` as a sheaf -/

/-- An envelope family together with a proof that its presheaf `ocris` is a sheaf
for the topology `T`. For the chaotic topology, every envelope family gives
one (`OcrisSheafData.chaotic`). -/
structure OcrisSheafData (T : TopologyData (A := A) (C := C)) where
  envelopes : EnvelopeFamily (A := A) (C := C) (γ := γ)
  isSheaf : T.IsOcrisSheaf envelopes

namespace OcrisSheafData

variable {T : TopologyData (A := A) (C := C)}

/-- The underlying presheaf `ocris`. -/
noncomputable def presheaf (D : OcrisSheafData (γ := γ) T) :
    Site (A := A) (C := C)ᵒᵖ ⥤ Type u :=
  EnvelopeFamily.ocris D.envelopes

@[simp]
theorem presheaf_eq (D : OcrisSheafData (γ := γ) T) :
    D.presheaf = EnvelopeFamily.ocris D.envelopes := rfl

/-- The sheaf condition, stated with Mathlib's `Presheaf.IsSheaf`. -/
theorem isSheaf_presheaf (D : OcrisSheafData (γ := γ) T) :
    Presheaf.IsSheaf T.topology D.presheaf := by
  exact D.isSheaf

/-- The sheaf `ocris` of an envelope family, for the chaotic topology. -/
noncomputable def chaotic
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    OcrisSheafData (γ := γ) (TopologyData.chaotic (A := A) (C := C)) :=
  { envelopes := E
    isSheaf := TopologyData.isOcrisSheaf_chaotic E }

end OcrisSheafData

end AffineCrystalline.InfinitesimalSite
