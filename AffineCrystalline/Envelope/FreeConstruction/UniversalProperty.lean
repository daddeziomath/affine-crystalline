/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.GeneralEnvelopeQuotient

/-!
# The universal property of the divided power envelope

Let `(A, I, γ)` be a divided power ring, `B` an `A`-algebra, `J ⊆ B` an ideal and
`J' = J + I B`. Let `D₀ = Γ_B(J') ⧸ J₁₂` be the quotient constructed in
`AffineCrystalline.Envelope.FreeConstruction.GeneralEnvelopeQuotient`, with
quotient map `q : Γ_B(J') → D₀`. This file studies the universal property of
`D₀` in terms of the following data.

* `SourceIdealData`: divided powers on the image `q(Γ⁺)` of the augmentation
  ideal, compatible with `γ`, for which `q` is a divided power morphism. The
  ideal `q(Γ⁺)` contains `J' D₀ + I D₀`
  (`GeneralEnvelopeQuotient.modifiedIdeal_map_le_quotientDP`).
* `TargetLawData`: for an `A`-algebra `D` with a map `φ : B → D` and divided
  powers `δ` on `J' D + I D`, the statements that the map
  `f : Γ_B(J') → D` with `f([n](m)) = δ_n(φ(m))`, given by the universal property
  of `Γ_B(J')`, is a divided power morphism and vanishes on `J₁₂`.

Given these data, `f` factors through a divided power `A`-algebra map `D₀ → D`
lying over `B`, and every such map coincides with it. Finally,
`UniversalPropertyData` collects target data for all such `(D, δ, φ)`
together with the initiality statement of `IsDPEnvelope`, in which the divided
power ideal of the target may be larger than `J' D + I D`; from it we deduce
that `D₀` is a divided power envelope of `(B, J')`.

## Main definitions

* `SourceIdealData`: the divided powers on `D₀`.
* `TargetLawData`: the data attached to a target `(D, δ, φ)`.
* `QuotientUniversalProperty.quotientMap`: the induced map `D₀ → D`.
* `UniversalPropertyData`: target data for all `(D, δ, φ)` and the
  initiality statement of `IsDPEnvelope`.

## Main results

* `QuotientUniversalProperty.quotientMap_comp_presentation`: the induced map lies
  over `B`.
* `QuotientUniversalProperty.quotientMap_isDPMorphism`: it is a divided power
  morphism.
* `QuotientUniversalProperty.compatible_map_eq_quotientMap`: it is the unique
  such map.
* `UniversalPropertyData.isDPEnvelope`: `D₀` is a divided power envelope
  of `(B, J')`.

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

section UniversalProperty

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {I : Ideal A} (hI : DividedPowers I) (J : Ideal B)
  (P : PositiveDPStructure
    (R := B) (M := modifiedBaseIdeal J hI))

variable (G : GeneralEnvelopeQuotient hI J P)

local notation "J'" => modifiedBaseIdeal J hI
local notation "Γ'" => DividedPowerAlgebra B (modifiedBaseIdeal J hI)
local notation "D₀" => GeneralEnvelopeQuotient.carrier hI J
local notation "q" => GeneralEnvelopeQuotient.quotientMap hI J

/-! ## Divided powers on the quotient -/

/-- Divided powers on the image `q(Γ⁺)` of the augmentation ideal that are
compatible with `γ` and for which the quotient map `q` is a divided power
morphism. -/
structure SourceIdealData
    (hI : DividedPowers I) (J : Ideal B)
    (P : PositiveDPStructure
      (R := B) (M := modifiedBaseIdeal J hI))
    (G : GeneralEnvelopeQuotient hI J P) where
  dividedPowers :
    DividedPowers
      ((positiveIdeal (R := B) (M := modifiedBaseIdeal J hI)).map
        (GeneralEnvelopeQuotient.quotientMap hI J))
  compat :
    IsDPMorphism hI dividedPowers
      (algebraMap A (GeneralEnvelopeQuotient.carrier hI J))
  quotient_map_isDPMorphism :
    IsDPMorphism P.dividedPowers dividedPowers
      (GeneralEnvelopeQuotient.quotientMap hI J)

namespace SourceIdealData

variable (S : SourceIdealData hI J P G)

theorem quotientMap_isDPMorphism :
    IsDPMorphism P.dividedPowers S.dividedPowers q :=
  S.quotient_map_isDPMorphism

omit S in
/-- The ideal `J' D₀ + I D₀` is contained in `q(Γ⁺)`. -/
theorem le_ideal :
    (modifiedBaseIdeal J hI).map
          (GeneralEnvelopeQuotient.presentationMap hI J).toRingHom ⊔
        I.map (algebraMap A (GeneralEnvelopeQuotient.carrier hI J)) ≤
      (positiveIdeal (R := B) (M := modifiedBaseIdeal J hI)).map
        (GeneralEnvelopeQuotient.quotientMap hI J) :=
  GeneralEnvelopeQuotient.modifiedIdeal_map_le_quotientDP hI J

end SourceIdealData

/-! ## Data attached to a target -/

/-- Data attached to an `A`-algebra `D` with a map `φ : B → D` and divided powers
`δ` on `J' D + I D`: the `B`-linear map `generator : J' → D` (equal to `φ` on
`J'`), defining a `B`-algebra map `f : Γ_B(J') → D` with `f([n](m)) = δ_n(φ(m))`,
together with the statements that `f` is a divided power morphism and that `f`
vanishes on `J₁₂`. -/
structure TargetLawData
    (hI : DividedPowers I) (J : Ideal B)
    (P : PositiveDPStructure
      (R := B) (M := modifiedBaseIdeal J hI))
    (G : GeneralEnvelopeQuotient hI J P)
    {D : Type u} [CommRing D] [Algebra A D] [Algebra B D]
    [IsScalarTower A B D]
    (φ : B →ₐ[A] D)
    (δ : DividedPowers
      ((modifiedBaseIdeal J hI).map φ.toRingHom ⊔
        I.map (algebraMap A D))) where
  presentation_eq_algebraMap : φ.toRingHom = algebraMap B D
  generator : modifiedBaseIdeal J hI →ₗ[B] D
  generator_mem : ∀ m, generator m ∈
    ((modifiedBaseIdeal J hI).map φ.toRingHom ⊔
      I.map (algebraMap A D))
  generator_eq : ∀ m, generator m = φ (m : B)

  /-- The map `Γ_B(J') → D` determined by `generator` is a divided power
  morphism. -/
  freeLift_isDPMorphism :
    let freeLift : DividedPowerAlgebra B (modifiedBaseIdeal J hI) →ₐ[B] D :=
      DividedPowerAlgebra.lift δ generator generator_mem
    IsDPMorphism P.dividedPowers δ freeLift.toRingHom

  /-- The map `Γ_B(J') → D` determined by `generator` vanishes on `J₁₂`. -/
  relation_annihilation :
    ∀ x, x ∈ j12 hI (modifiedBaseIdeal J hI)
        (map_I_le_modifiedBaseIdeal hI J) →
      (DividedPowerAlgebra.lift δ generator generator_mem) x = 0

namespace TargetLawData

variable {D : Type u} [CommRing D] [Algebra A D] [Algebra B D]
  [IsScalarTower A B D]
  {φ : B →ₐ[A] D}
  {δ : DividedPowers
    ((modifiedBaseIdeal J hI).map φ.toRingHom ⊔
      I.map (algebraMap A D))}
  (T : TargetLawData hI J P G φ δ)

/-- The `B`-algebra map `f : Γ_B(J') → D` with `f([n](m)) = δ_n(generator m)`. -/
noncomputable abbrev freeLift :
    DividedPowerAlgebra B (modifiedBaseIdeal J hI) →ₐ[B] D :=
  DividedPowerAlgebra.lift δ T.generator T.generator_mem

theorem freeLift_isDPMorphism_spec :
    IsDPMorphism P.dividedPowers δ
      (TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T).toRingHom :=
  TargetLawData.freeLift_isDPMorphism (hI := hI) (J := J) (P := P)
    (G := G) T

theorem freeLift_apply_dp
    (n : ℕ) (m : modifiedBaseIdeal J hI) :
    TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T
      (DividedPowerAlgebra.dp B n m) =
      δ.dpow n (T.generator m) :=
  DividedPowerAlgebra.lift_apply_dp δ T.generator_mem n m

end TargetLawData

/-! ## The induced map on the quotient -/

namespace QuotientUniversalProperty

variable (S : SourceIdealData hI J P G)
variable {D : Type u} [CommRing D] [Algebra A D] [Algebra B D]
  [IsScalarTower A B D]
  {φ : B →ₐ[A] D}
  {δ : DividedPowers
    ((modifiedBaseIdeal J hI).map φ.toRingHom ⊔ I.map (algebraMap A D))}
  (T : TargetLawData hI J P G φ δ)

/-- The `B`-algebra map `D₀ → D` induced by `f : Γ_B(J') → D`, which vanishes on
`J₁₂`. -/
noncomputable def quotientMapB : D₀ →ₐ[B] D :=
  Ideal.Quotient.liftₐ
    (j12 hI (modifiedBaseIdeal J hI) (map_I_le_modifiedBaseIdeal hI J))
    (TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T)
    T.relation_annihilation

theorem quotientMapB_comp :
    (QuotientUniversalProperty.quotientMapB (hI := hI) (J := J) (P := P)
      (G := G) T).comp
        (Ideal.Quotient.mkₐ B
          (j12 hI J' (map_I_le_modifiedBaseIdeal hI J))) =
      TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The induced map `D₀ → D`, as an `A`-algebra map. -/
noncomputable def quotientMap : D₀ →ₐ[A] D :=
  { toRingHom := (QuotientUniversalProperty.quotientMapB (hI := hI) (J := J)
      (P := P) (G := G) T).toRingHom
    commutes' := by
      intro a
      have hB := (QuotientUniversalProperty.quotientMapB (hI := hI) (J := J)
        (P := P) (G := G) T).commutes
        (algebraMap A B a)
      change
        (QuotientUniversalProperty.quotientMapB (hI := hI) (J := J)
          (P := P) (G := G) T)
            (algebraMap B D₀ (algebraMap A B a)) =
          algebraMap A D a
      rw [hB]
      exact (IsScalarTower.algebraMap_apply A B D a).symm }

/-- The induced map `D₀ → D` lies over `B`. -/
theorem quotientMap_comp_presentation :
    (QuotientUniversalProperty.quotientMap (hI := hI) (J := J) (P := P)
      (G := G) T).comp (GeneralEnvelopeQuotient.presentationMap hI J) = φ := by
  apply AlgHom.ext
  intro b
  change
    (QuotientUniversalProperty.quotientMapB (hI := hI) (J := J) (P := P)
      (G := G) T)
        (algebraMap B D₀ b) = φ b
  rw [(QuotientUniversalProperty.quotientMapB (hI := hI) (J := J) (P := P)
    (G := G) T).commutes]
  exact (congrArg (fun f ↦ f b)
    T.presentation_eq_algebraMap).symm

/-! ## Divided powers and uniqueness -/

/-- The induced map `D₀ → D` is a divided power morphism: its composite with the
divided power morphism `q`, which is surjective, is the divided power morphism `f`. -/
theorem quotientMap_isDPMorphism :
    IsDPMorphism S.dividedPowers δ
      (QuotientUniversalProperty.quotientMap (hI := hI) (J := J) (P := P)
        (G := G) T).toRingHom := by
  refine IsDPMorphism.of_comp (hK := δ) (f := q) (g := _) (heq := rfl)
    (hf := S.quotientMap_isDPMorphism hI J P G) (hh := ?_)
  have hψq :
      (QuotientUniversalProperty.quotientMap (hI := hI) (J := J)
        (P := P) (G := G) T).toRingHom.comp q =
        (TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T).toRingHom :=
    congrArg (fun f ↦ f.toRingHom)
      (QuotientUniversalProperty.quotientMapB_comp (hI := hI) (J := J) (P := P) (G := G) T)
  rw [hψq]
  exact TargetLawData.freeLift_isDPMorphism (hI := hI) (J := J) (P := P) (G := G) T

/-- In `D₀`, the image of `[1](m)` equals the image of `m ∈ J'`. -/
theorem quotientMap_dp_one :
    ∀ m : modifiedBaseIdeal J hI,
      q (DividedPowerAlgebra.dp B 1 m) =
        algebraMap B D₀ (m : B) := by
  intro m
  have hrel :
      q (DividedPowerAlgebra.embed B (modifiedBaseIdeal J hI) m) =
        algebraMap B D₀ (m : B) := by
    rw [GeneralEnvelopeQuotient.algebraMap_B_eq_quotientMap_comp hI J]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    exact rel1_mem_j12 hI (modifiedBaseIdeal J hI)
      (map_I_le_modifiedBaseIdeal hI J) m
  simpa [DividedPowerAlgebra.embed_def] using hrel

omit [IsScalarTower A B D] in
/-- If `ψ : D₀ → D` lies over `B` and `φ` is the structure map of `D`, then
`ψ ∘ q : Γ_B(J') → D` is compatible with the structure maps of `B`. -/
theorem compatible_quotientMap_algebraMap (ψ : D₀ →ₐ[A] D)
    (hψ : ψ.comp (GeneralEnvelopeQuotient.presentationMap hI J) = φ)
    (hφ : φ.toRingHom = algebraMap B D) (b : B) :
    ψ (q (algebraMap B Γ' b)) = algebraMap B D b :=
  calc
    ψ (q (algebraMap B Γ' b)) = ψ (algebraMap B D₀ b) :=
      congrArg ψ (congrArg (fun f ↦ f b)
        (GeneralEnvelopeQuotient.algebraMap_B_eq_quotientMap_comp hI J)).symm
    _ = φ b := AlgHom.congr_fun hψ b
    _ = algebraMap B D b := congrArg (fun f ↦ f b) hφ

/-- If `ψ : D₀ → D` lies over `B`, then `ψ` sends the image of `[1](m)` to
`generator m`. -/
theorem compatible_quotientMap_dp_one (ψ : D₀ →ₐ[A] D)
    (hψ : ψ.comp (GeneralEnvelopeQuotient.presentationMap hI J) = φ)
    (m : modifiedBaseIdeal J hI) :
    ψ (q (DividedPowerAlgebra.dp B 1 m)) = T.generator m := by
  rw [quotientMap_dp_one hI J m, T.generator_eq m]
  exact AlgHom.congr_fun hψ (m : B)

/-- If `ψ : D₀ → D` is a divided power `A`-algebra map lying over `B`, then
`ψ ∘ q = f`. Both maps send `[n](m) = δ'_n([1](m))` to `δ_n(φ(m))`, where `δ'`
denotes Roby's divided powers on `Γ⁺`. -/
theorem compatible_comp_quotientMap_eq_freeLift
    (ψ : D₀ →ₐ[A] D)
    (hψ : ψ.comp (GeneralEnvelopeQuotient.presentationMap hI J) = φ)
    (hψdp : IsDPMorphism S.dividedPowers δ ψ.toRingHom) :
    ψ.toRingHom.comp q =
      (TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T).toRingHom := by
  let ψB : DividedPowerAlgebra B (modifiedBaseIdeal J hI) →ₐ[B] D :=
    { toRingHom := ψ.toRingHom.comp q
      commutes' := compatible_quotientMap_algebraMap hI J ψ hψ T.presentation_eq_algebraMap }
  have hfree : IsDPMorphism P.dividedPowers δ ψB.toRingHom := by
    simpa [ψB] using DividedPowers.IsDPMorphism.comp δ hψdp (S.quotientMap_isDPMorphism hI J P G)
  have hgen : ψB = TargetLawData.freeLift (hI := hI) (J := J) (P := P) (G := G) T := by
    refine DividedPowerAlgebra.lift_unique _ _ fun n m ↦ ?_
    by_cases hn : n = 0
    · subst n
      rw [DividedPowerAlgebra.dp_zero]
      simp [δ.dpow_zero (T.generator_mem m)]
    · have hdp := hfree.dpow_comp (n := n) (DividedPowerAlgebra.dp B 1 m)
        (dp_mem_positiveIdeal (R := B) (M := modifiedBaseIdeal J hI) one_ne_zero m)
      calc
        ψB (DividedPowerAlgebra.dp B n m) =
            ψB (P.dividedPowers.dpow n (DividedPowerAlgebra.dp B 1 m)) := by
          rw [P.generator_formula one_ne_zero, generatorDpow_one_right]
        _ = δ.dpow n (ψB (DividedPowerAlgebra.dp B 1 m)) := hdp.symm
        _ = δ.dpow n (T.generator m) := by
          rw [← compatible_quotientMap_dp_one hI J P G T ψ hψ m]
          rfl
  exact congrArg (fun f ↦ f.toRingHom) hgen

/-- A divided power `A`-algebra map `D₀ → D` lying over `B` is the induced
map. -/
theorem compatible_map_eq_quotientMap
    (ψ : D₀ →ₐ[A] D)
    (hψ : ψ.comp (GeneralEnvelopeQuotient.presentationMap hI J) = φ)
    (hψdp : IsDPMorphism S.dividedPowers δ ψ.toRingHom) :
    ψ = QuotientUniversalProperty.quotientMap (hI := hI) (J := J)
        (P := P) (G := G) T := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    GeneralEnvelopeQuotient.quotientMap_surjective hI J x
  have hcomp := compatible_comp_quotientMap_eq_freeLift
    hI J P G S T ψ hψ hψdp
  have hqcomp := quotientMapB_comp (hI := hI) (J := J) (P := P)
    (G := G) T
  have hqcomp' := congrArg (fun f ↦ f.toRingHom) hqcomp
  exact congrArg (fun f ↦ f y) (hcomp.trans hqcomp'.symm)

end QuotientUniversalProperty

/-! ## The universal property -/

/-- Target data for every divided power `A`-algebra `(D, δ)` with a map
`φ : B → D` such that `δ` lives on `J' D + I D`, together with the initiality
statement of `IsDPEnvelope` for `D₀`. -/
structure UniversalPropertyData (S : SourceIdealData hI J P G) where
  target_data : ∀ {D : Type u} [CommRing D] [Algebra A D]
    (φ : B →ₐ[A] D)
    (δ : DividedPowers
      ((modifiedBaseIdeal J hI).map φ.toRingHom ⊔
        I.map (algebraMap A D)))
    (_ : IsDPMorphism hI δ (algebraMap A D)),
    @TargetLawData A B _ _ _ I hI J P G D _ _
      (φ.toRingHom.toAlgebra) (IsScalarTower.of_algHom φ) φ δ
  /-- Initiality of `D₀` among divided power `A`-algebras `(D, K, δ)` with a map
  `φ : B → D` such that `J' D + I D ⊆ K`. Unlike `target_data`, the divided power
  ideal `K` may be larger than `J' D + I D`; this generality is needed, for
  instance, for square-zero extensions. -/
  initiality : ∀ {D : Type u} [CommRing D] [Algebra A D]
      (K : Ideal D) (φ : B →ₐ[A] D) (δ : DividedPowers K),
      (modifiedBaseIdeal J hI).map φ.toRingHom ⊔
          I.map (algebraMap A D) ≤ K →
      IsDPMorphism hI δ (algebraMap A D) →
      ∃! ψ : GeneralEnvelopeQuotient.carrier hI J →ₐ[A] D,
        ψ.comp (GeneralEnvelopeQuotient.presentationMap hI J) = φ ∧
          IsDPMorphism S.dividedPowers δ ψ.toRingHom

namespace UniversalPropertyData

variable (S : SourceIdealData hI J P G)
variable (C : UniversalPropertyData hI J P G S)

/-- Given a `UniversalPropertyData`, the ring `D₀ = Γ_B(J') ⧸ J₁₂` is a
divided power envelope of `(B, J')`. -/
theorem isDPEnvelope (C : UniversalPropertyData hI J P G S) :
    @IsDPEnvelope A _ I hI B _ _ (modifiedBaseIdeal J hI)
      (GeneralEnvelopeQuotient.carrier hI J) _ _
      (GeneralEnvelopeQuotient.presentationMap hI J) _
      S.dividedPowers :=
  { le := SourceIdealData.le_ideal hI J, compat := S.compat, isInitial := C.initiality }

end UniversalPropertyData

end UniversalProperty

end FreeConstruction
end Envelope
end AffineCrystalline
