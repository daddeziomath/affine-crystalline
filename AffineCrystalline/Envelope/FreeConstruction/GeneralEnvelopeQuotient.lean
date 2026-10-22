/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.IncludedEnvelopeConstruction
import AffineCrystalline.Envelope.Existence

/-!
# The divided power envelope for an arbitrary ideal

Let `(A, I, γ)` be a divided power ring, `B` an `A`-algebra and `J ⊆ B` an
arbitrary ideal. The construction of
`AffineCrystalline.Envelope.FreeConstruction.IncludedEnvelopeConstruction`
requires `I B ⊆ J`, so we apply it to the enlarged ideal `J' = J + I B`. For any
`A`-algebra `D` with a map `f : B → D` over `A`, we have `J' D + I D = J D + I D`,
so the divided power envelopes of `(B, J)` and `(B, J')` agree.

In this file we set up the quotient `D = Γ_B(J') ⧸ J₁₂`, the map `B → D` and the
ideal identities relating `J` and `J'`.

## Main definitions

* `modifiedBaseIdeal`: the ideal `J' = J + I B`.
* `GeneralEnvelopeQuotient`: the stability hypothesis
  `IncludedEnvelopeConstructionData` for `J'`.
* `GeneralEnvelopeQuotient.carrier`, `GeneralEnvelopeQuotient.presentationMap`:
  the ring `Γ_B(J') ⧸ J₁₂` and the `A`-algebra map `B → Γ_B(J') ⧸ J₁₂`.
* `GeneralEnvelopeQuotient.quotientDP`: the quotient divided powers on the
  image of `Γ⁺`.
* `GeneralEnvelopeQuotient.IncludedEnvelopeData`: a divided power ideal of the
  quotient with divided powers and the universal property for `J'`.

## Main results

* `GeneralEnvelopeQuotient.modifiedIdeal_map_eq`: `J' D + I D = J D + I D` for
  every `A`-algebra map `B → D`.
* `GeneralEnvelopeQuotient.modifiedIdeal_map_le_quotientDP`: the ideal
  `J' D + I D` of the quotient is contained in the image of `Γ⁺`.
* `GeneralEnvelopeQuotient.isDPEnvelope_of_modifiedBaseIdeal`: an envelope of
  `(B, J')` is an envelope of `(B, J)`.

## References

* P. Berthelot and A. Ogus, *Notes on crystalline cohomology*, Mathematical
  Notes 21, Princeton University Press (1978), §3.
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* A. Chambert-Loir and M. I. de Frutos-Fernández, *A formalization of divided
  powers in Lean*, ITP 2025, LIPIcs, 4:1–4:17.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *Formalizing polynomial laws
  and the universal divided power algebra*, arXiv:2512.05750.
-/

open DividedPowerAlgebra DividedPowers Ideal

universe u

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section GeneralEnvelopeQuotient

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {I : Ideal A} (hI : DividedPowers I) (J : Ideal B)

/-! ## The enlarged presentation ideal -/

include hI

/-- The ideal `J' = J + I B` of `B`, which contains `I B`. -/
def modifiedBaseIdeal (_hI : DividedPowers I) : Ideal B :=
  J ⊔ I.map (algebraMap A B)

@[simp]
theorem le_modifiedBaseIdeal :
    J ≤ modifiedBaseIdeal J hI :=
  le_sup_left

@[simp]
theorem map_I_le_modifiedBaseIdeal :
    I.map (algebraMap A B) ≤ modifiedBaseIdeal J hI :=
  le_sup_right

variable (P : PositiveDPStructure
  (R := B) (M := modifiedBaseIdeal J hI))

/-! ## The quotient ring -/

/-- The stability hypothesis `IncludedEnvelopeConstructionData` for the ideal
`J' = J + I B`. -/
structure GeneralEnvelopeQuotient where
  included :
    IncludedEnvelopeConstructionData hI (modifiedBaseIdeal J hI)
      (map_I_le_modifiedBaseIdeal hI J) P

namespace GeneralEnvelopeQuotient

variable (G : GeneralEnvelopeQuotient hI J P)

local notation "J'" => modifiedBaseIdeal J hI
local notation "Γ'" => DividedPowerAlgebra B J'

/-- The ring `Γ_B(J') ⧸ J₁₂`. -/
abbrev carrier : Type u :=
  IncludedEnvelopeConstructionData.dpEnvelopeOfIncluded hI J'
    (map_I_le_modifiedBaseIdeal hI J)

/-- The quotient map `Γ_B(J') → Γ_B(J') ⧸ J₁₂`. -/
def quotientMap : Γ' →+* carrier hI J :=
  IncludedEnvelopeConstructionData.quotientMap hI J'
    (map_I_le_modifiedBaseIdeal hI J)

@[simp]
theorem quotientMap_apply (x : Γ') :
    quotientMap hI J x =
      Ideal.Quotient.mk
        (j12 hI J' (map_I_le_modifiedBaseIdeal hI J)) x :=
  rfl

/-- The structure map `B → Γ_B(J') ⧸ J₁₂` factors through the quotient map. -/
theorem algebraMap_B_eq_quotientMap_comp :
    algebraMap B (carrier hI J) =
      (quotientMap hI J).comp (algebraMap B Γ') :=
  IncludedEnvelopeConstructionData.algebraMap_eq_quotientMap_comp
    hI J' (map_I_le_modifiedBaseIdeal hI J)

/-- The structure map `A → Γ_B(J') ⧸ J₁₂` factors through `B` and the quotient
map. -/
theorem algebraMap_A_eq_quotientMap_comp :
    algebraMap A (carrier hI J) =
      (quotientMap hI J).comp
        ((algebraMap B Γ').comp (algebraMap A B)) :=
  IncludedEnvelopeConstructionData.algebraMap_A_eq_quotientMap_comp
    hI J' (map_I_le_modifiedBaseIdeal hI J)

/-- The structure map `B → Γ_B(J') ⧸ J₁₂`, as an `A`-algebra map. -/
noncomputable def presentationMap : B →ₐ[A] carrier hI J where
  toRingHom := algebraMap B (carrier hI J)
  commutes' := by
    intro a
    change algebraMap B (carrier hI J) (algebraMap A B a) =
      algebraMap A (carrier hI J) a
    rw [algebraMap_A_eq_quotientMap_comp hI J]
    rfl

@[simp]
theorem presentationMap_toRingHom :
    (presentationMap hI J).toRingHom =
      algebraMap B (carrier hI J) :=
  rfl

theorem presentationMap_comp_base :
    (presentationMap hI J).toRingHom.comp (algebraMap A B) =
      algebraMap A (carrier hI J) := by
  ext a
  exact (presentationMap hI J).commutes' a

theorem algebraMap_A_eq_presentationMap_comp :
    algebraMap A (carrier hI J) =
      (presentationMap hI J).toRingHom.comp (algebraMap A B) := by
  symm
  exact presentationMap_comp_base hI J

/-! ## Comparison of the ideals generated by `J` and `J'` -/

/-- For a ring map `f : B → D` compatible with the structure maps from `A`,
`f(J') D + I D = f(J) D + I D`. -/
theorem modifiedIdeal_map_eq
    {D : Type u} [CommRing D] [Algebra A D]
    (f : B →+* D)
    (hf : f.comp (algebraMap A B) = algebraMap A D) :
    (modifiedBaseIdeal J hI).map f ⊔ I.map (algebraMap A D) =
      J.map f ⊔ I.map (algebraMap A D) := by
  simp [modifiedBaseIdeal, Ideal.map_sup, Ideal.map_map, hf]

theorem modifiedEnvelopeIdeal_eq :
    ((J').map (presentationMap hI J).toRingHom ⊔
        I.map (algebraMap A (carrier hI J))) =
      J.map (presentationMap hI J).toRingHom ⊔
        I.map (algebraMap A (carrier hI J)) :=
  modifiedIdeal_map_eq hI J
    (presentationMap hI J).toRingHom
    (presentationMap_comp_base hI J)

theorem J_map_le_modifiedEnvelopeIdeal :
    J.map (presentationMap hI J).toRingHom ≤
      (J').map (presentationMap hI J).toRingHom ⊔
        I.map (algebraMap A (carrier hI J)) :=
  le_sup_of_le_left (Ideal.map_mono (le_modifiedBaseIdeal hI J))

theorem I_map_le_modifiedEnvelopeIdeal :
    I.map (algebraMap A (carrier hI J)) ≤
      (J').map (presentationMap hI J).toRingHom ⊔
        I.map (algebraMap A (carrier hI J)) :=
  le_sup_right

/-! ## The quotient divided powers -/

/-- The quotient divided powers on the image of `Γ⁺` in `Γ_B(J') ⧸ J₁₂`. -/
noncomputable abbrev quotientDP :
    DividedPowers
      ((positiveIdeal (R := B) (M := J')).map
        (quotientMap hI J)) :=
  IncludedEnvelopeConstructionData.quotientDividedPowers hI J'
    (map_I_le_modifiedBaseIdeal hI J) P G.included

theorem quotientMap_isDPMorphism :
    IsDPMorphism P.dividedPowers (quotientDP hI J P G)
      (quotientMap hI J) :=
  IncludedEnvelopeConstructionData.quotientMap_isDPMorphism hI J'
    (map_I_le_modifiedBaseIdeal hI J) P G.included

theorem quotientMap_surjective :
    Function.Surjective (quotientMap hI J) :=
  IncludedEnvelopeConstructionData.quotientMap_surjective hI J'
    (map_I_le_modifiedBaseIdeal hI J)

/-- The ideal `J' D + I D` of `D = Γ_B(J') ⧸ J₁₂` is contained in the image of
`Γ⁺`. -/
theorem modifiedIdeal_map_le_quotientDP :
    (J').map (presentationMap hI J).toRingHom ⊔
        I.map (algebraMap A (carrier hI J)) ≤
      IncludedEnvelopeConstructionData.dpIdealOfIncluded hI J'
        (map_I_le_modifiedBaseIdeal hI J) := by
  apply sup_le
  · exact IncludedEnvelopeConstructionData.sub_ideal_dpIdealOfIncluded
      hI J' (map_I_le_modifiedBaseIdeal hI J)
  · calc
      I.map (algebraMap A (carrier hI J)) =
          (I.map (algebraMap A B)).map
            (presentationMap hI J).toRingHom := by
        rw [Ideal.map_map, presentationMap_comp_base hI J]
      _ ≤ (J').map (presentationMap hI J).toRingHom :=
        Ideal.map_mono (map_I_le_modifiedBaseIdeal hI J)
      _ ≤ IncludedEnvelopeConstructionData.dpIdealOfIncluded hI J'
          (map_I_le_modifiedBaseIdeal hI J) :=
        IncludedEnvelopeConstructionData.sub_ideal_dpIdealOfIncluded
          hI J' (map_I_le_modifiedBaseIdeal hI J)

theorem J_map_le_quotientDP :
    J.map (presentationMap hI J).toRingHom ≤
      IncludedEnvelopeConstructionData.dpIdealOfIncluded hI J'
        (map_I_le_modifiedBaseIdeal hI J) :=
  (J_map_le_modifiedEnvelopeIdeal hI J).trans
    (modifiedIdeal_map_le_quotientDP hI J)

theorem I_map_le_quotientDP :
    I.map (algebraMap A (carrier hI J)) ≤
      IncludedEnvelopeConstructionData.dpIdealOfIncluded hI J'
        (map_I_le_modifiedBaseIdeal hI J) :=
  (I_map_le_modifiedEnvelopeIdeal hI J).trans
    (modifiedIdeal_map_le_quotientDP hI J)

/-! ## Envelopes along `J'` and along `J` -/

/-- A divided power envelope of `(B, J')` is a divided power envelope of `(B, J)`,
with the same divided power ideal: for every `A`-algebra map `φ : B → D` the
ideals `J' D + I D` and `J D + I D` coincide (`modifiedIdeal_map_eq`). -/
theorem isDPEnvelope_of_modifiedBaseIdeal
    {D : Type u} [CommRing D] [Algebra A D] {φ : B →ₐ[A] D}
    {K : Ideal D} {δ : DividedPowers K}
    (h : IsDPEnvelope hI J' D φ K δ) : IsDPEnvelope hI J D φ K δ := by
  have hφ (D' : Type u) [CommRing D'] [Algebra A D'] (φ' : B →ₐ[A] D') :
      φ'.toRingHom.comp (algebraMap A B) = algebraMap A D' := by
    ext a
    exact φ'.commutes a
  refine
    { le := ?_
      compat := h.compat
      isInitial := fun K' φ' δ' hK' hc ↦ h.isInitial K' φ' δ' ?_ hc }
  · rw [← modifiedIdeal_map_eq hI J φ.toRingHom (hφ D φ)]
    exact h.le
  · rw [modifiedIdeal_map_eq hI J φ'.toRingHom (hφ _ φ')]
    exact hK'

/-- An ideal of `D = Γ_B(J') ⧸ J₁₂` with divided powers making `D` a divided power
envelope of `(B, J')`. -/
structure IncludedEnvelopeData where
  pdIdeal : Ideal (carrier hI J)
  dividedPowers : DividedPowers pdIdeal
  isEnvelope :
    IsDPEnvelope hI J' (carrier hI J)
      (presentationMap hI J) pdIdeal dividedPowers

/-- The ring `Γ_B(J') ⧸ J₁₂` is a divided power envelope of `(B, J)`. -/
theorem transported_isEnvelope
    (C : IncludedEnvelopeData hI J) :
    IsDPEnvelope hI J (carrier hI J)
      (presentationMap hI J) C.pdIdeal C.dividedPowers :=
  isDPEnvelope_of_modifiedBaseIdeal hI J C.isEnvelope

end GeneralEnvelopeQuotient

end GeneralEnvelopeQuotient

end FreeConstruction
end Envelope
end AffineCrystalline
