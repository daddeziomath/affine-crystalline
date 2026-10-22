/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.InfinitesimalSite.Envelope
import AffineCrystalline.Envelope.FreeConstruction.UniversalProperty

/-!
# Envelopes of infinitesimal thickenings from the free construction

Let `X = (π : B → C)` be an object of `INF(C/A)` and `J = ker π`. The free
construction of divided power envelopes (after Chambert-Loir and
de Frutos-Fernández) realises the envelope of `B` along the enlarged ideal
`J' = J + I B` (`modifiedBaseIdeal`) as a quotient of the divided power algebra
of `J'`. An `EnvelopeConstructionData X` consists of the data and proofs
from which this envelope is built: divided powers on the augmentation ideal
of the divided power algebra, the quotient, divided powers on the image of
the augmentation ideal in the quotient, and the universal property.

Since `J' D + I D = J D + I D` for every `A`-algebra `D`, an envelope along
`J'` is also an envelope along `J`, with the same divided power ideal. This
gives a `DPEnvelopeChoice` along `J`, and hence `EnvelopeExistenceData` once
such data are given at every object.

## Main definitions

* `EnvelopeConstructionData X`: the data and proofs of the free construction
  of the envelope of `X`.
* `EnvelopeConstructionData.toDPEnvelopeChoice`: the resulting envelope of
  `B` along `ker π`.

## Main results

* `EnvelopeConstructionData.universal_isDPEnvelope`: the quotient is an
  envelope along `J'`.
* `EnvelopeExistenceData.of_envelopeConstructionData`: envelopes exist at every
  object if every object admits such data.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.InfinitesimalSite

open AffineCrystalline.Envelope.FreeConstruction

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-! ## The free construction at one object -/

/-- The data and proofs from which the free construction builds the envelope of
`X = (π : B → C)` along the enlarged ideal `J' = ker π + I B`: divided powers
on the augmentation ideal of the divided power algebra of `J'` (`dpStructure`),
the quotient of that algebra (`quotient`), divided powers on the image of the
augmentation ideal in the quotient (`source`), and the universal property
(`universal`). -/
structure EnvelopeConstructionData
    (X : InfinitesimalThickening A C) where
  dpStructure : PositiveDPStructure
    (R := X.carrier)
    (M := modifiedBaseIdeal (RingHom.ker X.π.toRingHom) γ)
  quotient : GeneralEnvelopeQuotient γ (RingHom.ker X.π.toRingHom) dpStructure
  source : SourceIdealData γ (RingHom.ker X.π.toRingHom)
    dpStructure quotient
  /-- The universal property of the quotient, along the enlarged ideal
  `J' = ker π + I B`. -/
  universal : UniversalPropertyData γ (RingHom.ker X.π.toRingHom)
    dpStructure quotient source

namespace EnvelopeConstructionData

variable {X : InfinitesimalThickening A C}

/-- The quotient is a compatible divided power envelope of `B` along the enlarged
ideal `J' = ker π + I B`. -/
theorem universal_isDPEnvelope
    (K : EnvelopeConstructionData (γ := γ) X) :
    IsDPEnvelope γ (modifiedBaseIdeal (RingHom.ker X.π.toRingHom) γ)
      (GeneralEnvelopeQuotient.carrier γ (RingHom.ker X.π.toRingHom))
      (GeneralEnvelopeQuotient.presentationMap γ
        (RingHom.ker X.π.toRingHom)) _ K.source.dividedPowers := by
  exact K.universal.isDPEnvelope

/-- The envelope along `J' = ker π + I B`, as an `IncludedEnvelopeData`; by
`GeneralEnvelopeQuotient.transported_isEnvelope` it is also an envelope along
`ker π`, with the same divided power ideal. -/
noncomputable def derivedTransport
    (K : EnvelopeConstructionData (γ := γ) X) :
    GeneralEnvelopeQuotient.IncludedEnvelopeData γ
      (RingHom.ker X.π.toRingHom) where
  pdIdeal := _
  dividedPowers := K.source.dividedPowers
  isEnvelope := K.universal.isDPEnvelope

/-- The compatible divided power envelope of `B` along `ker π` built by the free
construction. -/
noncomputable def toDPEnvelopeChoice
    (K : EnvelopeConstructionData (γ := γ) X) :
    DPEnvelopeChoice γ (RingHom.ker X.π.toRingHom) := by
  let T := derivedTransport K
  exact
    { carrier := GeneralEnvelopeQuotient.carrier γ
        (RingHom.ker X.π.toRingHom)
      commRing := inferInstance
      algebra := inferInstance
      map := GeneralEnvelopeQuotient.presentationMap γ
        (RingHom.ker X.π.toRingHom)
      pdIdeal := T.pdIdeal
      dividedPowers := T.dividedPowers
      isEnvelope := GeneralEnvelopeQuotient.transported_isEnvelope γ _ T }

end EnvelopeConstructionData

/-! ## Existence of envelopes -/

namespace EnvelopeExistenceData

/-- If every object of `INF(C/A)` admits the data of the free construction, then
every object has a compatible divided power envelope. -/
theorem of_envelopeConstructionData
    (H : ∀ X : InfinitesimalThickening A C,
      Nonempty (EnvelopeConstructionData (γ := γ) X)) :
    EnvelopeExistenceData (A := A) (C := C) (γ := γ) where
  exists_envelope X := by
    exact ⟨EnvelopeConstructionData.toDPEnvelopeChoice
      (Classical.choice (H X))⟩

end EnvelopeExistenceData

end AffineCrystalline.InfinitesimalSite

