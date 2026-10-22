/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import AffineCrystalline.Envelope.Existence

/-!
# Divided power envelopes over `ℚ`

If `R` is a `ℚ`-algebra, every ideal `I` of `R` carries a unique divided power
structure, given by `γ_n(x) = xⁿ / n!` (`RatAlgebra.dividedPowers`), and every ring
map between `ℚ`-algebras sending `I` into `J` is a divided power morphism.
Consequently, if `A` and `P` are `ℚ`-algebras and `J ⊆ P` is an ideal, the divided
power envelope of `(P, J)` is `P` itself, with the divided powers on `J + I P`.

## Main definitions

* `ratAlgebraDPEnvelopeChoice`: the envelope `(P, id)` as a `DPEnvelopeChoice`.

## Main results

* `ratAlgebra_isDPMorphism`: a ring map between `ℚ`-algebras sending `I` into `J`
  is a divided power morphism.
* `ratAlgebra_identity_isDPEnvelope`: `(P, id)` is a divided power envelope of
  `(P, J)`.
* `ratAlgebra_hasDPEnvelope`: divided power envelopes exist over `ℚ`.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
-/

open DividedPowers
open scoped Ring

universe u

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

/-- Classical decidability of propositions, used for the decidability of membership in
ideals required by `RatAlgebra.dividedPowers`. -/
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Divided power morphisms over `ℚ` -/

/-- A ring map `f : R → S` between `ℚ`-algebras with `f(I) ⊆ J` is a divided
power morphism for the divided powers `xⁿ / n!` on `I` and `J`. -/
theorem ratAlgebra_isDPMorphism
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S]
    {I : Ideal R} {J : Ideal S} (f : R →+* S)
    (hIJ : I.map f ≤ J) :
    IsDPMorphism (RatAlgebra.dividedPowers I)
      (RatAlgebra.dividedPowers J) f := by
  refine ⟨hIJ, ?_⟩
  intro n x hx
  rw [RatAlgebra.dpow_apply, if_pos (hIJ (Ideal.mem_map_of_mem f hx)),
    RatAlgebra.dpow_apply, if_pos hx, map_mul, map_pow]
  have hfacR : IsUnit (n.factorial : R) :=
    IsUnit.natCast_factorial_of_algebra ℚ n
  have hfacS : IsUnit (n.factorial : S) :=
    IsUnit.natCast_factorial_of_algebra ℚ n
  have hfac_map : f (n.factorial : R) = (n.factorial : S) := by
    simp
  have hinv : f ((n.factorial : R)⁻¹ʳ) = (n.factorial : S)⁻¹ʳ := by
    rw [← one_mul ((n.factorial : S)⁻¹ʳ)]
    apply (Ring.eq_mul_inverse_iff_mul_eq
      (f ((n.factorial : R)⁻¹ʳ)) 1 (n.factorial : S) hfacS).2
    calc
      f ((n.factorial : R)⁻¹ʳ) * (n.factorial : S) =
          f ((n.factorial : R)⁻¹ʳ) * f (n.factorial : R) := by rw [hfac_map]
      _ = f ((n.factorial : R)⁻¹ʳ * (n.factorial : R)) := by
        rw [map_mul]
      _ = f 1 := by rw [Ring.inverse_mul_cancel _ hfacR]
      _ = 1 := map_one f
  rw [hinv]

/-! ## The envelope over `ℚ` -/

/-- If `A` and `P` are `ℚ`-algebras, the identity of `P`, with the divided powers
`xⁿ / n!` on `J + I P`, is a divided power envelope of `(P, J)`. -/
theorem ratAlgebra_identity_isDPEnvelope
    {A P : Type u} [CommRing A] [CommRing P]
    [Algebra ℚ A] [Algebra A P] [Algebra ℚ P]
    {I : Ideal A} (γ : DividedPowers I) (J : Ideal P) :
    let φ : P →ₐ[A] P := AlgHom.id A P
    let K : Ideal P := J.map φ.toRingHom ⊔ I.map (algebraMap A P)
    @IsDPEnvelope A _ I γ P _ _ J P _ _ φ K
      (RatAlgebra.dividedPowers K) := by
  dsimp only
  refine
    { le := le_rfl
      compat := ?_
      isInitial := fun {D'} _ _ K' φ' δ' hcontain _ ↦ ?_ }
  · rw [RatAlgebra.dividedPowers_unique γ]
    exact ratAlgebra_isDPMorphism (algebraMap A P) le_sup_right
  letI : Algebra ℚ D' := Algebra.compHom D' (algebraMap ℚ A)
  have hKL : (J.map (AlgHom.id A P).toRingHom ⊔ I.map (algebraMap A P)).map φ'.toRingHom ≤ K' := by
    rw [map_sup_map_algebraMap_eq, AlgHom.comp_id]
    exact hcontain
  refine ⟨φ', ⟨AlgHom.comp_id φ', ?_⟩, fun ψ hψ ↦ ?_⟩
  · rw [RatAlgebra.dividedPowers_unique δ']
    exact ratAlgebra_isDPMorphism φ'.toRingHom hKL
  · rw [← hψ.1, AlgHom.comp_id]

/-! ## Existence of envelopes over `ℚ` -/

/-- The envelope `(P, id)` of `(P, J)` over `ℚ`, as a `DPEnvelopeChoice`. -/
noncomputable def ratAlgebraDPEnvelopeChoice
    {A P : Type u} [CommRing A] [CommRing P]
    [Algebra ℚ A] [Algebra A P] [Algebra ℚ P]
    {I : Ideal A} (γ : DividedPowers I) (J : Ideal P) :
    DPEnvelopeChoice γ J where
  carrier := P
  commRing := inferInstance
  algebra := inferInstance
  map := AlgHom.id A P
  pdIdeal := J.map (AlgHom.id A P).toRingHom ⊔ I.map (algebraMap A P)
  dividedPowers :=
    RatAlgebra.dividedPowers
      (J.map (AlgHom.id A P).toRingHom ⊔ I.map (algebraMap A P))
  isEnvelope := ratAlgebra_identity_isDPEnvelope γ J

/-- If `A` and `P` are `ℚ`-algebras, the divided power envelope of `(P, J)`
exists. -/
theorem ratAlgebra_hasDPEnvelope
    {A P : Type u} [CommRing A] [CommRing P]
    [Algebra ℚ A] [Algebra A P] [Algebra ℚ P]
    {I : Ideal A} (γ : DividedPowers I) (J : Ideal P) :
    HasDPEnvelope γ J :=
  ⟨⟨ratAlgebraDPEnvelopeChoice γ J⟩⟩

end FreeConstruction
end Envelope
end AffineCrystalline
