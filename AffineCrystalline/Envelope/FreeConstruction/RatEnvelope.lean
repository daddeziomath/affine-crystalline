/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.InfinitesimalSite.Envelope
import AffineCrystalline.Envelope.FreeConstruction.RatAlgebra

/-!
# Envelopes of infinitesimal thickenings over `ℚ`

Let `A` be a `ℚ`-algebra with a divided power ideal `(I, γ)` and `C` an
`A`-algebra. For every infinitesimal thickening `π : X → C` of `C` over `A`, the
divided power envelope of `(X, ker π)` is `X` itself
(`ratAlgebraDPEnvelopeChoice`). Hence the existence hypothesis
`EnvelopeExistenceData` holds over `ℚ`.

## Main results

* `EnvelopeExistenceData.ofRatAlgebra`: envelopes of all infinitesimal
  thickenings exist when `A` is a `ℚ`-algebra.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

namespace EnvelopeExistenceData

/--
If `A` is a `ℚ`-algebra, every infinitesimal thickening `π : X → C` is its own
divided power envelope with respect to `ker π`. The `ℚ`-algebra structure on `X`
is induced from that of `A`.
-/
theorem ofRatAlgebra [Algebra ℚ A] :
    EnvelopeExistenceData (A := A) (C := C) (γ := γ) where
  exists_envelope X := by
    letI : Algebra ℚ X.carrier :=
      Algebra.compHom X.carrier (algebraMap ℚ A)
    exact ⟨AffineCrystalline.Envelope.FreeConstruction.ratAlgebraDPEnvelopeChoice
      γ (RingHom.ker X.π.toRingHom)⟩

end EnvelopeExistenceData

end AffineCrystalline.InfinitesimalSite
