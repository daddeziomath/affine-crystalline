/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.PDDifferentials
import AffineCrystalline.DeRham.PDDescent
import AffineCrystalline.Envelope.PDKaehlerComparison

/-!
# The module of PD differentials as a quotient, and base change

Let `D` be a `B`-algebra and `δ` a divided-power structure on an ideal of `D`.
The module `PDKaehler δ` is the quotient of `Ω[D⁄A]` by the submodule
`pdRelations δ` (Stacks Project, Tag 07HQ). Composing the quotient map with the
base-change map `D ⊗[B] Ω[B⁄A] → Ω[D⁄A]` gives the canonical comparison map
`D ⊗[B] Ω[B⁄A] → PDKaehler δ`, which is `pdKaehlerDpEnvelopeComparison`. We
show that this composite is surjective when `B → D` is surjective, and record
the universal property of the quotient.

When `D` is a divided-power envelope, the comparison map is bijective by
`pdKaehler_dpEnvelope`. The structure `PDKaehlerEnvelopeComparisonData`
packages surjectivity of `B → D` together with this bijectivity, and yields
the corresponding `D`-linear equivalence.

## Main definitions

* `pdKaehlerQuotientMap δ`: the quotient map `Ω[D⁄A] → PDKaehler δ`.
* `pdKaehlerBaseChangeMap`: the base-change map `D ⊗[B] Ω[B⁄A] → Ω[D⁄A]`.
* `pdKaehlerQuotientBaseChangeMap δ`: the composite of the two.
* `PDKaehlerQuotientBaseChangeData δ`: surjectivity data for these maps,
  constructed from surjectivity of `B → D` by
  `PDKaehlerQuotientBaseChangeData.of_surjective`.
* `pdKaehlerQuotientLift δ g h`: the map `PDKaehler δ → M` induced by a
  `D`-linear map `g : Ω[D⁄A] → M` vanishing on `pdRelations δ`.
* `PDKaehlerEnvelopeComparisonData γ hD`: surjectivity of `B → D` and
  bijectivity of the comparison map, for a divided-power envelope `D`.
* `PDKaehlerEnvelopeComparisonData.equiv`: the resulting `D`-linear
  equivalence `D ⊗[B] Ω[B⁄A] ≃ PDKaehler δ`.

## Main results

* `pdKaehlerQuotientBaseChangeMap_eq_comparison`: the composite is the
  canonical comparison map.
* `pdKaehlerQuotientBaseChangeMap_surjective`: the composite is surjective when
  `B → D` is surjective.
* `pdKaehlerQuotientLift_comp_quotient`, `pdKaehlerQuotientLift_unique`: the
  universal property of the quotient.

## References

* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
-/

open scoped TensorProduct
open DividedPowers

universe u

namespace AffineCrystalline.DeRham

noncomputable section

section QuotientBaseChange

variable {A B D : Type u}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra A D] [Algebra B D]
variable [IsScalarTower A B D]
variable {J_D : Ideal D} (δ : DividedPowers J_D)

/-! ## The quotient map, base change, and their composite -/

/-- The quotient map `Ω[D⁄A] → PDKaehler δ`. -/
noncomputable def pdKaehlerQuotientMap :
    Ω[D⁄A] →ₗ[D] PDKaehler (A := A) δ :=
  (pdRelations (A := A) δ).mkQ

/-- The ordinary Kähler base-change map from `D ⊗[B] Ω[B/A]` to `Ω[D/A]`. -/
noncomputable def pdKaehlerBaseChangeMap :
    (D ⊗[B] Ω[B⁄A]) →ₗ[D] Ω[D⁄A] :=
  KaehlerDifferential.mapBaseChange A B D

/-- The composite `D ⊗[B] Ω[B⁄A] → Ω[D⁄A] → PDKaehler δ`. -/
noncomputable def pdKaehlerQuotientBaseChangeMap :
    (D ⊗[B] Ω[B⁄A]) →ₗ[D] PDKaehler (A := A) δ :=
  (pdKaehlerQuotientMap δ).comp
    (pdKaehlerBaseChangeMap (A := A) (B := B) (D := D))

/-- The composite is, by definition, the canonical comparison map
`pdKaehlerDpEnvelopeComparison`. -/
theorem pdKaehlerQuotientBaseChangeMap_eq_comparison :
    pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ =
      pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ := by
  rfl

/-- The quotient map `Ω[D⁄A] → PDKaehler δ` is surjective. -/
theorem pdKaehlerQuotientMap_surjective :
    Function.Surjective (pdKaehlerQuotientMap (A := A) δ) :=
  Submodule.mkQ_surjective _

/-- The base-change map is surjective when the algebra map `B → D` is
surjective. -/
theorem pdKaehlerBaseChangeMap_surjective
    (hBD : Function.Surjective (algebraMap B D)) :
    Function.Surjective
      (pdKaehlerBaseChangeMap (A := A) (B := B) (D := D)) :=
  KaehlerDifferential.mapBaseChange_surjective A B D hBD

/-- The composite `D ⊗[B] Ω[B⁄A] → PDKaehler δ` is surjective when the algebra
map `B → D` is surjective. -/
theorem pdKaehlerQuotientBaseChangeMap_surjective
    (hBD : Function.Surjective (algebraMap B D)) :
    Function.Surjective
      (pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ) := by
  intro η
  obtain ⟨ω, hω⟩ := pdKaehlerQuotientMap_surjective (A := A) δ η
  obtain ⟨x, hx⟩ := pdKaehlerBaseChangeMap_surjective
    (A := A) (B := B) (D := D) hBD ω
  refine ⟨x, ?_⟩
  simp only [pdKaehlerQuotientBaseChangeMap, LinearMap.comp_apply, hx, hω]

/-! ## Surjectivity data -/

/-- Surjectivity data for the quotient map, the base-change map and their
composite. All fields follow from `algebraMap_surjective` (see
`PDKaehlerQuotientBaseChangeData.of_surjective`); they are recorded so that they
can be used directly. -/
structure PDKaehlerQuotientBaseChangeData where
  algebraMap_surjective : Function.Surjective (algebraMap B D)
  baseChange_surjective :
    Function.Surjective
      (pdKaehlerBaseChangeMap (A := A) (B := B) (D := D))
  quotient_surjective :
    Function.Surjective (pdKaehlerQuotientMap (A := A) δ)
  comparison_surjective :
    Function.Surjective
      (pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ)

/-- Construct `PDKaehlerQuotientBaseChangeData` from surjectivity of the
algebra map `B → D`. -/
theorem PDKaehlerQuotientBaseChangeData.of_surjective
    (hBD : Function.Surjective (algebraMap B D)) :
    PDKaehlerQuotientBaseChangeData (A := A) (B := B) δ :=
  { algebraMap_surjective := hBD
    baseChange_surjective := pdKaehlerBaseChangeMap_surjective
      (A := A) (B := B) (D := D) hBD
    quotient_surjective := pdKaehlerQuotientMap_surjective
      (A := A) δ
    comparison_surjective := pdKaehlerQuotientBaseChangeMap_surjective
      (A := A) (B := B) δ hBD }

/-! ## Universal properties -/

/-- The map `PDKaehler δ → M` induced by a `D`-linear map `g : Ω[D⁄A] → M`
vanishing on `pdRelations δ`. -/
noncomputable def pdKaehlerQuotientLift
    {M : Type u} [AddCommGroup M] [Module D M]
    (g : Ω[D⁄A] →ₗ[D] M)
    (hrelations : pdRelations (A := A) δ ≤ LinearMap.ker g) :
    PDKaehler (A := A) δ →ₗ[D] M :=
  Submodule.liftQ (pdRelations (A := A) δ) g hrelations

/-- The induced map `pdKaehlerQuotientLift δ g h` composed with the quotient map
is `g`. -/
@[simp]
theorem pdKaehlerQuotientLift_comp_quotient
    {M : Type u} [AddCommGroup M] [Module D M]
    (g : Ω[D⁄A] →ₗ[D] M)
    (hrelations : pdRelations (A := A) δ ≤ LinearMap.ker g) :
    (pdKaehlerQuotientLift δ g hrelations).comp
        (pdKaehlerQuotientMap (A := A) δ) = g := by
  change
    (Submodule.liftQ (pdRelations (A := A) δ) g hrelations).comp
        (pdRelations (A := A) δ).mkQ = g
  exact (pdRelations (A := A) δ).liftQ_mkQ g hrelations

/-- Uniqueness of the induced map `pdKaehlerQuotientLift δ g h`. -/
theorem pdKaehlerQuotientLift_unique
    {M : Type u} [AddCommGroup M] [Module D M]
    (g : Ω[D⁄A] →ₗ[D] M)
    (hrelations : pdRelations (A := A) δ ≤ LinearMap.ker g)
    (f : PDKaehler (A := A) δ →ₗ[D] M)
    (hf : f.comp (pdKaehlerQuotientMap (A := A) δ) = g) :
    f = pdKaehlerQuotientLift δ g hrelations := by
  apply Submodule.linearMap_qext
  change f.comp (pdKaehlerQuotientMap (A := A) δ) =
    (pdKaehlerQuotientLift δ g hrelations).comp
      (pdKaehlerQuotientMap (A := A) δ)
  rw [hf, pdKaehlerQuotientLift_comp_quotient]

/-- The map `PDKaehler.lift δ M θ hθ` induced by a divided-power derivation
`θ : D → M` satisfies `PDKaehler.lift δ M θ hθ ∘ pdD δ = θ`. -/
theorem pdKaehler_lift_restrictScalars_comp_pdD
    {M : Type u} [AddCommGroup M] [Module A M] [Module D M]
    [IsScalarTower A D M]
    (θ : D →ₗ[A] M) (hθ : IsPDDerivation δ M θ) :
    (PDKaehler.lift δ M θ hθ).restrictScalars A ∘ₗ
        pdD δ = θ :=
  PDKaehler.lift_comp δ M θ hθ

/-- Uniqueness in the universal property of `PDKaehler δ`: a `D`-linear map
`g : PDKaehler δ → M` with `g ∘ pdD δ = θ` is `PDKaehler.lift δ M θ hθ`. -/
theorem pdKaehler_lift_eq_of_comp_pdD
    {M : Type u} [AddCommGroup M] [Module A M] [Module D M]
    [IsScalarTower A D M]
    (θ : D →ₗ[A] M) (hθ : IsPDDerivation δ M θ)
    (g : PDKaehler (A := A) δ →ₗ[D] M)
    (hg : (g.restrictScalars A) ∘ₗ pdD δ = θ) :
    g = PDKaehler.lift δ M θ hθ :=
  PDKaehler.lift_unique δ M θ hθ g hg

end QuotientBaseChange

section EnvelopeComparison

variable {A B D : Type u}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra A D] [Algebra B D]
variable [IsScalarTower A B D]
variable {I : Ideal A} {J : Ideal B} (γ : DividedPowers I)
variable {K : Ideal D} {δ : DividedPowers K}

/-- For a divided-power envelope `D` (witnessed by `hD`), surjectivity of the
algebra map `B → D` together with bijectivity of the comparison map
`D ⊗[B] Ω[B⁄A] → PDKaehler δ`. Bijectivity holds by `pdKaehler_dpEnvelope`;
see `PDKaehlerEnvelopeComparisonData.of_comparison`. -/
structure PDKaehlerEnvelopeComparisonData
    (hD : IsDPEnvelope γ J D (IsScalarTower.toAlgHom A B D) K δ) where
  algebraMap_surjective : Function.Surjective (algebraMap B D)
  bijective :
    Function.Bijective
      (pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ)

/-- The map under consideration is the canonical comparison map
`pdKaehlerDpEnvelopeComparison`. -/
theorem PDKaehlerEnvelopeComparisonData.map_eq_comparison
    {hD : IsDPEnvelope γ J D (IsScalarTower.toAlgHom A B D) K δ}
    (_C : PDKaehlerEnvelopeComparisonData γ hD) :
    pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ =
      pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ :=
  pdKaehlerQuotientBaseChangeMap_eq_comparison (A := A) (B := B) δ

/-- The `D`-linear equivalence `D ⊗[B] Ω[B⁄A] ≃ PDKaehler δ` given by the
comparison map. -/
noncomputable def PDKaehlerEnvelopeComparisonData.equiv
    {hD : IsDPEnvelope γ J D (IsScalarTower.toAlgHom A B D) K δ}
    (C : PDKaehlerEnvelopeComparisonData γ hD) :
    (D ⊗[B] Ω[B⁄A]) ≃ₗ[D] PDKaehler (A := A) δ :=
  LinearEquiv.ofBijective
    (pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ) C.bijective

/-- The underlying map of `PDKaehlerEnvelopeComparisonData.equiv` is the
comparison map. -/
theorem PDKaehlerEnvelopeComparisonData.equiv_spec
    {hD : IsDPEnvelope γ J D (IsScalarTower.toAlgHom A B D) K δ}
    (C : PDKaehlerEnvelopeComparisonData γ hD) :
    (C.equiv γ).toLinearMap =
      pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ := by
  rfl

/-- Surjectivity of the comparison map, deduced from surjectivity of
`B → D` alone. -/
theorem PDKaehlerEnvelopeComparisonData.surjective
    {hD : IsDPEnvelope γ J D (IsScalarTower.toAlgHom A B D) K δ}
    (C : PDKaehlerEnvelopeComparisonData γ hD) :
    Function.Surjective
      (pdKaehlerQuotientBaseChangeMap (A := A) (B := B) δ) :=
  pdKaehlerQuotientBaseChangeMap_surjective
    (A := A) (B := B) δ C.algebraMap_surjective

/-- Construct the data from surjectivity of `B → D` and bijectivity of
`pdKaehlerDpEnvelopeComparison`, as provided by `pdKaehler_dpEnvelope hD`. -/
theorem PDKaehlerEnvelopeComparisonData.of_comparison
    {hD : IsDPEnvelope γ J D (IsScalarTower.toAlgHom A B D) K δ}
    (hBD : Function.Surjective (algebraMap B D))
    (hbijective : Function.Bijective
      (pdKaehlerDpEnvelopeComparison (A := A) (B := B) δ)) :
    PDKaehlerEnvelopeComparisonData γ hD :=
  { algebraMap_surjective := hBD
    bijective := by
      rw [pdKaehlerQuotientBaseChangeMap_eq_comparison (A := A) (B := B) δ]
      exact hbijective }

end EnvelopeComparison

end

end AffineCrystalline.DeRham
