/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.PositiveDPStructure
import AffineCrystalline.Envelope.FreeConstruction.RelationGenerators

/-!
# The divided power envelope when `I B ⊆ J`

Let `(A, I, γ)` be a divided power ring, `B` an `A`-algebra and `J ⊆ B` an ideal
with `I B ⊆ J`. Let `δ` be Roby's divided powers on the positive ideal `Γ⁺` of
`Γ_B(J)` (`PositiveDPStructure`) and assume that `J₁₂ ⊓ Γ⁺` is a
sub-divided power ideal of `(Γ⁺, δ)` (`IncludedEnvelopeConstructionData`). We
construct the candidate envelope `D = Γ_B(J) ⧸ J₁₂`, its algebra structures, the
quotient divided powers on the image `Γ⁺ D` of `Γ⁺`, and show `J D ⊆ Γ⁺ D`. The
universal property is treated in
`AffineCrystalline.Envelope.FreeConstruction.UniversalProperty`.

## Main definitions

* `IncludedEnvelopeConstructionData`: the condition that `J₁₂ ⊓ Γ⁺` is a
  sub-divided power ideal.
* `IncludedEnvelopeConstructionData.dpEnvelopeOfIncluded`: the ring
  `Γ_B(J) ⧸ J₁₂`.
* `IncludedEnvelopeConstructionData.dpIdealOfIncluded`: the image of `Γ⁺` in it.
* `IncludedEnvelopeConstructionData.quotientDividedPowers`: the quotient divided
  powers on this image.

## Main results

* `IncludedEnvelopeConstructionData.quotientMap_isDPMorphism`: the quotient map
  is a divided power morphism.
* `IncludedEnvelopeConstructionData.quotient_dpow_generator`: Roby's formula in
  the quotient.
* `IncludedEnvelopeConstructionData.sub_ideal_dpIdealOfIncluded`: the image of
  `J` is contained in the divided power ideal.

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

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section Included

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {B : Type v} [CommRing B] [Algebra A B] (J : Ideal B)
  (hIJ : I.map (algebraMap A B) ≤ J)

local notation "Γ" => DividedPowerAlgebra B J

variable (P : PositiveDPStructure (R := B) (M := J))

/-! ## The stability hypothesis -/

/--
The condition that `J₁₂ ⊓ Γ⁺` is a sub-divided power ideal of `(Γ⁺, δ)`, under
which `δ` descends to `Γ_B(J) ⧸ J₁₂`. See `J12CompatibilityData` for a
reduction of this condition.
-/
structure IncludedEnvelopeConstructionData where
  j12_isSubDPIdeal :
    IsSubDPIdeal P.dividedPowers
      (j12 hI J hIJ ⊓ positiveIdeal (R := B) (M := J))

namespace IncludedEnvelopeConstructionData

variable (D : IncludedEnvelopeConstructionData hI J hIJ P)

/-! ## The quotient ring and its algebra structures -/

/-- The relation ideal `J₁₂` of `Γ_B(J)`. -/
abbrev relationIdeal : Ideal Γ := j12 hI J hIJ

/-- The ring `Γ_B(J) ⧸ J₁₂`. -/
abbrev dpEnvelopeOfIncluded : Type v := Γ ⧸ relationIdeal hI J hIJ

noncomputable instance commRing : CommRing (dpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.commRing (relationIdeal hI J hIJ)

noncomputable instance algebraOfIncluded : Algebra B (dpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.algebra _

noncomputable instance algebraOfIncludedFromGamma :
    Algebra Γ (dpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.algebra _

noncomputable instance algebraOfIncludedFromA :
    Algebra A (dpEnvelopeOfIncluded hI J hIJ) :=
  ((algebraMap B (dpEnvelopeOfIncluded hI J hIJ)).comp (algebraMap A B)).toAlgebra

/-- The quotient map `Γ_B(J) → Γ_B(J) ⧸ J₁₂`. -/
def quotientMap : Γ →+* dpEnvelopeOfIncluded hI J hIJ :=
  Ideal.Quotient.mk (relationIdeal hI J hIJ)

@[simp]
theorem quotientMap_apply (x : Γ) :
    quotientMap hI J hIJ x =
      Ideal.Quotient.mk (relationIdeal hI J hIJ) x :=
  rfl

theorem algebraMap_eq_quotientMap_comp :
    algebraMap B (dpEnvelopeOfIncluded hI J hIJ) =
      (quotientMap hI J hIJ).comp (algebraMap B Γ) :=
  rfl

theorem algebraMap_A_eq_quotientMap_comp :
    algebraMap A (dpEnvelopeOfIncluded hI J hIJ) =
      (quotientMap hI J hIJ).comp
        ((algebraMap B Γ).comp (algebraMap A B)) :=
  rfl

/-! ## The quotient divided powers -/

/-- The image of `Γ⁺` in `Γ_B(J) ⧸ J₁₂`. -/
noncomputable def dpIdealOfIncluded :
    Ideal (dpEnvelopeOfIncluded hI J hIJ) :=
  (positiveIdeal (R := B) (M := J)).map
    (quotientMap hI J hIJ)

/-- The quotient divided powers on the image of `Γ⁺` in `Γ_B(J) ⧸ J₁₂`. -/
noncomputable def quotientDividedPowers :
    DividedPowers (dpIdealOfIncluded hI J hIJ) :=
  DividedPowers.Quotient.dividedPowers P.dividedPowers
    D.j12_isSubDPIdeal

theorem quotientMap_isDPMorphism :
    IsDPMorphism P.dividedPowers (quotientDividedPowers hI J hIJ P D)
      (quotientMap hI J hIJ) :=
  DividedPowers.Quotient.isDPMorphism P.dividedPowers D.j12_isSubDPIdeal

theorem quotient_dpow_apply {n : ℕ} {x : Γ}
    (hx : x ∈ positiveIdeal (R := B) (M := J)) :
    (quotientDividedPowers hI J hIJ P D).dpow n
        ((quotientMap hI J hIJ) x) =
      (quotientMap hI J hIJ) (P.dividedPowers.dpow n x) :=
  DividedPowers.Quotient.dpow_apply P.dividedPowers D.j12_isSubDPIdeal hx

theorem quotient_dpow_generator {n k : ℕ} (hk : k ≠ 0) (m : J) :
    (quotientDividedPowers hI J hIJ P D).dpow n
        ((quotientMap hI J hIJ) (DividedPowerAlgebra.dp B k m)) =
      (quotientMap hI J hIJ)
        (generatorDpow (R := B) (M := J) n k m) := by
  rw [quotient_dpow_apply hI J hIJ P D
    (dp_mem_positiveIdeal (R := B) (M := J) hk m)]
  exact congrArg (quotientMap hI J hIJ) (P.generator_formula hk)

/-! ## The image of `J` -/

/--
The image of `J` in `Γ_B(J) ⧸ J₁₂` is contained in the image of `Γ⁺`: for `x ∈ J`,
`x ≡ [1](x) mod J₁`.
-/
theorem sub_ideal_dpIdealOfIncluded :
    J.map (algebraMap B (dpEnvelopeOfIncluded hI J hIJ)) ≤
      dpIdealOfIncluded hI J hIJ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change algebraMap B (dpEnvelopeOfIncluded hI J hIJ) x ∈
    dpIdealOfIncluded hI J hIJ
  rw [dpIdealOfIncluded,
    Ideal.mem_map_iff_of_surjective (quotientMap hI J hIJ)
      (Ideal.Quotient.mk_surjective)]
  refine ⟨DividedPowerAlgebra.embed B J ⟨x, hx⟩, ?_, ?_⟩
  · rw [DividedPowerAlgebra.embed_def]
    exact dp_mem_positiveIdeal (R := B) (M := J) one_ne_zero ⟨x, hx⟩
  · change
      (quotientMap hI J hIJ)
          (DividedPowerAlgebra.embed B J ⟨x, hx⟩) =
        algebraMap B (dpEnvelopeOfIncluded hI J hIJ) x
    rw [algebraMap_eq_quotientMap_comp hI J hIJ]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    exact rel1_mem_j12 hI J hIJ ⟨x, hx⟩

theorem positive_generator_mem_dpIdealOfIncluded
    {n : ℕ} (hn : n ≠ 0) (m : J) :
    (quotientMap hI J hIJ) (DividedPowerAlgebra.dp B n m) ∈
      dpIdealOfIncluded hI J hIJ := by
  rw [dpIdealOfIncluded, Ideal.mem_map_iff_of_surjective
    (quotientMap hI J hIJ) Ideal.Quotient.mk_surjective]
  exact ⟨DividedPowerAlgebra.dp B n m,
    dp_mem_positiveIdeal (R := B) (M := J) hn m, rfl⟩

theorem quotientMap_surjective :
    Function.Surjective (quotientMap hI J hIJ) :=
  Ideal.Quotient.mk_surjective

end IncludedEnvelopeConstructionData

end Included

end FreeConstruction
end Envelope
end AffineCrystalline
