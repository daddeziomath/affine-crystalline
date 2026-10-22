/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Envelope.FreeConstruction.RatAlgebra
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Divided power differentials in characteristic zero

Let `A → B` be a map of `ℚ`-algebras and `J ⊆ B` an ideal. Then `J` carries the
canonical divided powers `x^[n] = x^n / n!`, and the ordinary Kähler derivation
`d : B → Ω[B⁄A]` already satisfies `d(x^[n]) = x^[n-1] dx`. Consequently the
quotient map `Ω[B⁄A] → Ω_{B,δ}` is an isomorphism: over `ℚ`, divided power
Kähler differentials coincide with ordinary Kähler differentials.

We also record that, over `ℚ`, the identity of `B` is a divided power envelope of
`(B, J)` relative to `(A, 0)`.

## Main definitions

* `ordinaryPDKaehlerEquiv`: the `B`-linear isomorphism `Ω[B⁄A] ≃ Ω_{B,δ}` for the
  canonical divided powers on `J`.
* `identityEnvelope`: the divided power envelope of `(B, J)` given by `B` itself.

## Main results

* `isPDDerivation_kaehlerDifferential_D`: the Kähler derivation `B → Ω[B⁄A]` is a divided
  power derivation for the canonical divided powers.
* `identityEnvelope_isDPEnvelope`: `identityEnvelope` satisfies `IsDPEnvelope`.

## References

* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open DividedPowers
open Ring
open scoped Ring

universe u

noncomputable section

namespace AffineCrystalline.DeRham.CharacteristicZero

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra ℚ A] [Algebra ℚ B] [IsScalarTower ℚ A B]
variable {J : Ideal B}

local notation "δ₀" => RatAlgebra.dividedPowers J
local notation "Ω₀" => Ω[B⁄A]
local notation "PDΩ₀" => PDKaehler (A := A) δ₀

/-! ## The Kähler derivation is a divided power derivation -/

/-- `(n!)⁻¹ * n = ((n - 1)!)⁻¹` in `ℚ` for `n ≠ 0`. -/
theorem inverse_factorial_mul_natCast {n : ℕ} (hn0 : n ≠ 0) :
    inverse (n.factorial : ℚ) * n = inverse ((n - 1).factorial : ℚ) := by
  rw [← Nat.mul_factorial_pred hn0, Nat.cast_mul]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  rw [Ring.inverse_mul (Or.inl (isUnit_iff_ne_zero.mpr hnq))]
  rw [mul_assoc, Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.mpr hnq), mul_one]

/-- The Kähler derivation `d : B → Ω[B⁄A]` is a divided power derivation for the
canonical divided powers `x^[n] = x^n / n!` on an ideal of a `ℚ`-algebra. -/
theorem isPDDerivation_kaehlerDifferential_D :
    IsPDDerivation δ₀ Ω₀ (KaehlerDifferential.D A B).toLinearMap := by
  refine { leibniz := ?_, dpow := ?_ }
  · intro b b'
    exact (KaehlerDifferential.D A B).leibniz b b'
  · intro n hn x hx
    rw [RatAlgebra.dpow_eq_inv_fact_smul (I := J) δ₀ hx,
      RatAlgebra.dpow_eq_inv_fact_smul (I := J) δ₀ hx]
    simp only [Algebra.smul_def]
    change (KaehlerDifferential.D A B)
        ((algebraMap ℚ B) (inverse (n.factorial : ℚ)) * x ^ n) = _
    rw [(KaehlerDifferential.D A B).leibniz,
      IsScalarTower.algebraMap_apply ℚ A B,
      (KaehlerDifferential.D A B).map_algebraMap, smul_zero, add_zero]
    rw [show (KaehlerDifferential.D A B) (x ^ n) =
        n • x ^ (n - 1) • (KaehlerDifferential.D A B) x by
      exact (KaehlerDifferential.D A B).leibniz_pow n (a := x)]
    rw [← inverse_factorial_mul_natCast (Nat.ne_of_gt hn)]
    rw [← Nat.cast_smul_eq_nsmul B n]
    simp only [smul_smul]
    rw [← IsScalarTower.algebraMap_apply ℚ A B]
    simp only [map_mul, map_natCast]
    rw [mul_assoc]
    rfl

/-! ## The comparison isomorphism -/

/-- The quotient map `Ω[B⁄A] → Ω_{B,δ}` for the canonical divided powers `δ` on `J`. -/
noncomputable def ordinaryToPD : Ω₀ →ₗ[B] PDΩ₀ :=
  (pdRelations (A := A) δ₀).mkQ

/-- The map `Ω_{B,δ} → Ω[B⁄A]` induced, via the universal property of `Ω_{B,δ}`,
by the divided power derivation `d : B → Ω[B⁄A]`. -/
noncomputable def pdToOrdinary : PDΩ₀ →ₗ[B] Ω₀ :=
  PDKaehler.lift δ₀ Ω₀ (KaehlerDifferential.D A B).toLinearMap
    isPDDerivation_kaehlerDifferential_D

/-- `Ω_{B,δ} → Ω[B⁄A]` sends the class of `db` to `db`. -/
theorem pdToOrdinary_pdD (b : B) :
    pdToOrdinary (pdD δ₀ b) = KaehlerDifferential.D A B b :=
  LinearMap.congr_fun
    (PDKaehler.lift_comp δ₀ Ω₀ (KaehlerDifferential.D A B).toLinearMap
      isPDDerivation_kaehlerDifferential_D) b

/-- `Ω[B⁄A] → Ω_{B,δ} → Ω[B⁄A]` is the identity. -/
theorem pdToOrdinary_comp_ordinaryToPD :
    (pdToOrdinary (A := A) (B := B) (J := J)).comp (ordinaryToPD (A := A) (B := B) (J := J)) =
      LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext b
  exact pdToOrdinary_pdD b

/-- `Ω_{B,δ} → Ω[B⁄A] → Ω_{B,δ}` is the identity. -/
theorem ordinaryToPD_comp_pdToOrdinary :
    (ordinaryToPD (A := A) (B := B) (J := J)).comp (pdToOrdinary (A := A) (B := B) (J := J)) =
      LinearMap.id := by
  apply Submodule.linearMap_qext
  apply Derivation.liftKaehlerDifferential_unique
  ext b
  change ordinaryToPD (pdToOrdinary (pdD δ₀ b)) = pdD δ₀ b
  rw [pdToOrdinary_pdD]
  rfl

/-- Over a `ℚ`-algebra, the module of divided power Kähler differentials for the
canonical divided powers is canonically isomorphic to the module of ordinary Kähler
differentials. -/
noncomputable def ordinaryPDKaehlerEquiv : Ω₀ ≃ₗ[B] PDΩ₀ where
  toLinearMap := ordinaryToPD
  invFun := pdToOrdinary
  left_inv ω := LinearMap.congr_fun pdToOrdinary_comp_ordinaryToPD ω
  right_inv ω := LinearMap.congr_fun ordinaryToPD_comp_pdToOrdinary ω

@[simp]
theorem ordinaryPDKaehlerEquiv_apply (ω : Ω₀) :
    ordinaryPDKaehlerEquiv (J := J) ω = ordinaryToPD ω :=
  rfl

@[simp]
theorem ordinaryPDKaehlerEquiv_symm_apply (ω : PDΩ₀) :
    (ordinaryPDKaehlerEquiv (J := J)).symm ω = pdToOrdinary ω :=
  rfl

/-! ## The identity envelope -/

/-- Over `ℚ`, the identity of `B`, with the canonical divided powers, is a divided
power envelope of `(B, J)` relative to `(A, 0)`. -/
noncomputable def identityEnvelope :
    DPEnvelopeChoice (RatAlgebra.dividedPowers (⊥ : Ideal A)) J :=
  Envelope.FreeConstruction.ratAlgebraDPEnvelopeChoice
    (RatAlgebra.dividedPowers (⊥ : Ideal A)) J

omit [IsScalarTower ℚ A B] in
/-- `identityEnvelope` satisfies the universal property of the divided power
envelope. -/
theorem identityEnvelope_isDPEnvelope :
    let E := identityEnvelope (A := A) (B := B) (J := J)
    @IsDPEnvelope A _ (⊥ : Ideal A) (RatAlgebra.dividedPowers (⊥ : Ideal A))
      B _ _ J E.carrier E.commRing E.algebra E.map E.pdIdeal E.dividedPowers :=
  (identityEnvelope (A := A) (B := B) (J := J)).isEnvelope

end AffineCrystalline.DeRham.CharacteristicZero
