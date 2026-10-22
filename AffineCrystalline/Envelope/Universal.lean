/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.PDDifferentials
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-!
# The universal property of divided power envelopes

Let `(A, I, γ)` be a divided power ring, `P` an `A`-algebra and `J ⊆ P` an ideal.
The predicate `IsDPEnvelope γ J D φ K δ`, defined in
`AffineCrystalline.PDDifferentials`, states that `φ : P → D` together with an
ideal `K ⊇ J D + I D` and divided powers `δ` on `K` is initial among divided
power `A`-algebras `(D', K', δ')` with a map `P → D'` sending `J` into `K'`. This file derives the
formal consequences of this universal property: the comparison map out of an
envelope, its uniqueness, and its behaviour under identities and composition.
We also record two facts on quotient divided powers.

## Main definitions

* `IsDPEnvelope.comparison`: the divided power `A`-algebra map `D → D'` lying
  over `P`, given by the universal property.
* `DividedPowers.Quotient.quotientDPMorphism`: the quotient map `A → A ⧸ J` as a
  bundled divided power morphism, when `J ⊓ I` is a sub-divided power ideal.

## Main results

* `IsDPEnvelope.comparison_spec`, `IsDPEnvelope.eq_comparison`,
  `IsDPEnvelope.eq_of_comparison`: existence and uniqueness of comparison maps.
* `IsDPEnvelope.identity_spec`, `IsDPEnvelope.comp_spec`: identities and
  composites of compatible divided power maps are compatible.
* `DividedPowers.Quotient.dividedPowers_eq_of_isDPMorphism`: the quotient
  divided powers are the only ones making the quotient map a divided power
  morphism.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open DividedPowers

universe u

namespace IsDPEnvelope

/-! ### The comparison map and its uniqueness -/

/-- The comparison map `D → D'` supplied by the initiality clause of the
envelope `(D, φ, K, δ)`, for a divided power `A`-algebra `(D', K', δ')` with a
map `φ' : P → D'` sending `J` into `K'`. -/
noncomputable def comparison
    {A P D D' : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    [CommRing P] [Algebra A P] (J : Ideal P)
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    (hD : _root_.IsDPEnvelope γ J D φ K δ)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    (hK' : J.map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K')
    (hφ' : IsDPMorphism γ δ' (algebraMap A D')) : D →ₐ[A] D' :=
  Classical.choose (hD.isInitial
    K' φ' δ' hK' hφ')

/-- The comparison map commutes with the presentation map and is a DP map. -/
theorem comparison_spec
    {A P D D' : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    [CommRing P] [Algebra A P] (J : Ideal P)
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    (hD : _root_.IsDPEnvelope γ J D φ K δ)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    (hK' : J.map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K')
    (hφ' : IsDPMorphism γ δ' (algebraMap A D')) :
    (comparison γ J φ δ hD φ' δ' hK' hφ').comp φ = φ' ∧
      IsDPMorphism δ δ' (comparison γ J φ δ hD φ' δ' hK' hφ').toRingHom :=
  (Classical.choose_spec (hD.isInitial
    K' φ' δ' hK' hφ')).1

/-- Two compatible DP comparison maps out of an envelope are equal. -/
theorem eq_of_comparison
    {A P D D' : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    [CommRing P] [Algebra A P] (J : Ideal P)
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    (hD : _root_.IsDPEnvelope γ J D φ K δ)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    (hK' : J.map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K')
    (hφ' : IsDPMorphism γ δ' (algebraMap A D'))
    (ψ₁ ψ₂ : D →ₐ[A] D')
    (hψ₁ : ψ₁.comp φ = φ' ∧ IsDPMorphism δ δ' ψ₁.toRingHom)
    (hψ₂ : ψ₂.comp φ = φ' ∧ IsDPMorphism δ δ' ψ₂.toRingHom) :
    ψ₁ = ψ₂ :=
  (hD.isInitial
    K' φ' δ' hK' hφ').unique hψ₁ hψ₂

/-- A compatible comparison map is equal to the chosen comparison map. -/
theorem eq_comparison
    {A P D D' : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    [CommRing P] [Algebra A P] (J : Ideal P)
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    (hD : _root_.IsDPEnvelope γ J D φ K δ)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    (hK' : J.map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K')
    (hφ' : IsDPMorphism γ δ' (algebraMap A D'))
    (ψ : D →ₐ[A] D')
    (hψ : ψ.comp φ = φ' ∧ IsDPMorphism δ δ' ψ.toRingHom) :
    ψ = comparison γ J φ δ hD φ' δ' hK' hφ' :=
  eq_of_comparison γ J φ δ hD φ' δ' hK' hφ'
    ψ (comparison γ J φ δ hD φ' δ' hK' hφ') hψ
    (comparison_spec γ J φ δ hD φ' δ' hK' hφ')

/-! ### Identity and composition -/

/-- The identity algebra map is a DP map and lies over the presentation map. -/
theorem identity_spec
    {A P D : Type u} [CommRing A]
    [CommRing P] [Algebra A P]
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K) :
    (AlgHom.id A D).comp φ = φ ∧
      IsDPMorphism δ δ (AlgHom.id A D).toRingHom := by
  constructor
  · exact AlgHom.id_comp φ
  · simpa [DividedPowers.DPMorphism.id] using
      (DividedPowers.DPMorphism.id δ).isDPMorphism

/-- DP morphisms over a fixed base compose, with the expected algebra-map law. -/
theorem comp_spec
    {A P D D' D'' : Type u} [CommRing A]
    [CommRing P] [Algebra A P]
    [CommRing D] [Algebra A D] (φ : P →ₐ[A] D)
    {K : Ideal D} (δ : DividedPowers K)
    [CommRing D'] [Algebra A D'] (φ' : P →ₐ[A] D')
    {K' : Ideal D'} (δ' : DividedPowers K')
    [CommRing D''] [Algebra A D''] (φ'' : P →ₐ[A] D'')
    {K'' : Ideal D''} (δ'' : DividedPowers K'')
    (ψ : D →ₐ[A] D') (χ : D' →ₐ[A] D'')
    (hψ : ψ.comp φ = φ' ∧ IsDPMorphism δ δ' ψ.toRingHom)
    (hχ : χ.comp φ' = φ'' ∧ IsDPMorphism δ' δ'' χ.toRingHom) :
    (χ.comp ψ).comp φ = φ'' ∧
      IsDPMorphism δ δ'' (χ.comp ψ).toRingHom := by
  constructor
  · rw [AlgHom.comp_assoc, hψ.1, hχ.1]
  · exact DividedPowers.IsDPMorphism.comp _ hχ.2 hψ.2

end IsDPEnvelope

/-! ### Quotient divided powers -/

namespace DividedPowers.Quotient

/-- If `J ⊓ I` is a sub-divided power ideal of `(I, hI)`, the quotient map
`A → A ⧸ J` is a bundled divided power morphism to the quotient divided
powers. -/
noncomputable def quotientDPMorphism
    {A : Type u} [CommRing A] {I J : Ideal A} (hI : DividedPowers I)
    (hIJ : IsSubDPIdeal hI (J ⊓ I)) :
    DPMorphism hI (dividedPowers hI hIJ) :=
  DPMorphism.mk' (isDPMorphism hI hIJ)

/-- Any divided powers on `I · (A ⧸ J)` making the quotient map a divided power
morphism are the quotient divided powers. -/
theorem dividedPowers_eq_of_isDPMorphism
    {A : Type u} [CommRing A] {I J : Ideal A} (hI : DividedPowers I)
    (hIJ : IsSubDPIdeal hI (J ⊓ I))
    (hquot : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (hm : IsDPMorphism hI hquot (Ideal.Quotient.mk J)) :
    hquot = dividedPowers hI hIJ :=
  DividedPowers.Quotient.dividedPowers_unique hI hIJ hquot hm

/-- Variant of `dividedPowers_eq_of_isDPMorphism` for a bundled `DPMorphism`
whose underlying ring map is the quotient map. -/
theorem dividedPowers_eq_of_bundledDPMorphism
    {A : Type u} [CommRing A] {I J : Ideal A} (hI : DividedPowers I)
    (hIJ : IsSubDPIdeal hI (J ⊓ I))
    (hquot : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (φ : DPMorphism hI hquot)
    (hφ : φ.toRingHom = Ideal.Quotient.mk J) :
    hquot = dividedPowers hI hIJ := by
  apply dividedPowers_eq_of_isDPMorphism hI hIJ hquot
  simpa [hφ] using φ.isDPMorphism

end DividedPowers.Quotient
