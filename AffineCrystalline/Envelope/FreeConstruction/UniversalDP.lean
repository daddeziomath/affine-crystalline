/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.RobyDpowConstruction

/-!
# The divided power algebra and divided powers on its positive ideal

Let `R` be a commutative ring and `M` an `R`-module. This file collects the
properties of the divided power algebra `Γ_R(M)` provided by Mathlib (the
relations between the generators `[n](m)`, induction on `Γ_R(M)`, and the
universal property of `Γ_R(M)` with respect to maps `M → I` into divided power
ideals), and packages the data from which Roby's divided powers on the positive
ideal `Γ⁺` are constructed: a `RobyBasisData` together with a
`RobyDpowLawData`.

## Main definitions

* `universalCarrier`, `universalGenerator`: the ring `Γ_R(M)` and its generators
  `[n](m)`.
* `UniversalDPInput`: a `RobyBasisData` together with a
  `RobyDpowLawData`.
* `UniversalDPInput.dividedPowers`: the resulting divided powers on `Γ⁺`.

## Main results

* `universalGenerator_mul`, `universalGenerator_add`: the relations
  `[n](m) [p](m) = C(n + p, n) [n + p](m)` and
  `[n](x + y) = ∑_{i + j = n} [i](x) [j](y)`.
* `universalLift_generator_formula`, `universalLift_unique`: the universal
  property of `Γ_R(M)`.
* `UniversalDPInput.generator_formula`: the resulting divided powers
  satisfy Roby's formula.
* `UniversalDPInput.generator_formula_is_forced`: they are the only
  divided powers on `Γ⁺` satisfying Roby's formula.

## References

* N. Roby, *Lois polynômes et lois formelles en théorie des modules*,
  Ann. Sci. École Norm. Sup. (3) 80 (1963), 213–348.
* N. Roby, *Les algèbres à puissances divisées*, Bull. Sci. Math. (2) 89 (1965),
  75–91.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *A formalization of divided
  powers in Lean*, ITP 2025, LIPIcs, 4:1–4:17.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *Formalizing polynomial laws
  and the universal divided power algebra*, arXiv:2512.05750.
-/

open DividedPowers

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section UniversalAlgebra

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-! ## The divided power algebra -/

/-- The divided power algebra `Γ_R(M)`. -/
abbrev universalCarrier : Type u := DividedPowerAlgebra R M

/-- The structure map `R → Γ_R(M)`. -/
abbrev universalAlgebraMap : R →+* universalCarrier (R := R) (M := M) :=
  algebraMap R (DividedPowerAlgebra R M)

/-- The generator `[n](m)` of `Γ_R(M)`. -/
abbrev universalGenerator (n : ℕ) (m : M) : universalCarrier (R := R) (M := M) :=
  DividedPowerAlgebra.dp R n m

/-- Induction on `Γ_R(M)`: a property of scalars, stable under sums and under
multiplication by generators, holds for every element. -/
theorem universalCarrier_induction
    {P : Γ → Prop} (x : Γ)
    (h_scalar : ∀ r : R, P (algebraMap R Γ r))
    (h_add : ∀ x y : Γ, P x → P y → P (x + y))
    (h_generator : ∀ (x : Γ) (n : ℕ) (m : M), P x →
      P (x * DividedPowerAlgebra.dp R n m)) :
    P x :=
  DividedPowerAlgebra.induction_on x h_scalar h_add h_generator

theorem universalGenerator_mul
    {n p : ℕ} {m : M} :
    universalGenerator (R := R) (M := M) n m *
        universalGenerator (R := R) (M := M) p m =
      (Nat.choose (n + p) n : Γ) *
        universalGenerator (R := R) (M := M) (n + p) m := by
  simpa [universalGenerator, nsmul_eq_mul] using
    (DividedPowerAlgebra.dp_mul (R := R) (M := M) (n := n) (p := p) (m := m))

theorem universalGenerator_add
    {n : ℕ} {x y : M} :
    universalGenerator (R := R) (M := M) n (x + y) =
      (Finset.antidiagonal n).sum fun k ↦
        universalGenerator (R := R) (M := M) k.1 x *
          universalGenerator (R := R) (M := M) k.2 y :=
  DividedPowerAlgebra.dp_add

theorem universalGenerator_zero (m : M) :
    universalGenerator (R := R) (M := M) 0 m = 1 :=
  DividedPowerAlgebra.dp_zero

/-! ## The universal property of `Γ_R(M)` -/

/-- For divided powers `δ` on an ideal `I` of an `R`-algebra `A` and an `R`-linear
map `g : M → A` with values in `I`, the induced map `Γ_R(M) → A` sends `[n](m)` to
`δ_n(g(m))`. -/
theorem universalLift_generator_formula
    {A : Type v} [CommRing A] [Algebra R A]
    {I : Ideal A} (δ : DividedPowers I)
    (g : M →ₗ[R] A) (hg : ∀ m, g m ∈ I)
    (n : ℕ) (m : M) :
    DividedPowerAlgebra.lift δ g hg
        (universalGenerator (R := R) (M := M) n m) = δ.dpow n (g m) :=
  DividedPowerAlgebra.lift_apply_dp (g := g) δ hg n m

/-- An `R`-algebra map `Γ_R(M) → A` sending `[n](m)` to `δ_n(g(m))` is the
induced map. -/
theorem universalLift_unique
    {A : Type v} [CommRing A] [Algebra R A]
    {I : Ideal A} (δ : DividedPowers I)
    (g : M →ₗ[R] A) (hg : ∀ m, g m ∈ I)
    {f : Γ →ₐ[R] A}
    (hf : ∀ n m, f (universalGenerator (R := R) (M := M) n m) =
      δ.dpow n (g m)) :
    f = DividedPowerAlgebra.lift δ g hg :=
  DividedPowerAlgebra.lift_unique (g := g) δ hg hf

/-! ## Divided powers on the positive ideal -/

/--
The data defining Roby's divided powers on `Γ⁺`: a `RobyBasisData`
(bases of `M` and of `Γ_R(M)` by Roby monomials) and a `RobyDpowLawData`
(the divided power axioms for the explicit formula `robyDpow`).
-/
structure UniversalDPInput where
  basis : RobyBasisData (R := R) (M := M) (ι := ι)
  laws : RobyDpowLawData basis

namespace UniversalDPInput

variable (C : UniversalDPInput (R := R) (M := M) (ι := ι))

/-- The divided powers on `Γ⁺` defined by `robyDpow`. -/
def dividedPowers : DividedPowers (positiveIdeal (R := R) (M := M)) :=
  AffineCrystalline.Envelope.FreeConstruction.dividedPowers C.basis C.laws

@[simp]
theorem dividedPowers_apply (n : ℕ) (x : Γ) :
    (C.dividedPowers).dpow n x =
      robyDpow C.basis.moduleBasis C.basis.totalBasis n x :=
  AffineCrystalline.Envelope.FreeConstruction.dividedPowers_apply C.basis C.laws n x

/-- Roby's formula `γ_n([k](m)) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`. -/
theorem generator_formula {n k : ℕ} {m : M} (hk : k ≠ 0) :
    C.dividedPowers.dpow n (DividedPowerAlgebra.dp R k m) =
      generatorDpow (R := R) (M := M) n k m :=
  AffineCrystalline.Envelope.FreeConstruction.dividedPowers_generator_formula
    C.basis C.laws hk

/-- Any divided powers on `Γ⁺` satisfying Roby's formula coincide with
`UniversalDPInput.dividedPowers`. -/
theorem generator_formula_is_forced
    (H : DividedPowers (positiveIdeal (R := R) (M := M)))
    (hH : ∀ {n k : ℕ} {m : M}, k ≠ 0 →
      H.dpow n (DividedPowerAlgebra.dp R k m) =
        generatorDpow (R := R) (M := M) n k m) :
    H = C.dividedPowers :=
  AffineCrystalline.Envelope.FreeConstruction.dividedPowers_unique C.basis C.laws H hH

end UniversalDPInput

/-- A structure wrapping a `UniversalDPInput`. -/
structure UniversalDPRequirement where
  input : UniversalDPInput (R := R) (M := M) (ι := ι)

/-- The divided powers on `Γ⁺` defined by a `UniversalDPRequirement`. -/
noncomputable def dpStructureOfRequirement
    (O : UniversalDPRequirement (R := R) (M := M) (ι := ι)) :
    DividedPowers (positiveIdeal (R := R) (M := M)) :=
  O.input.dividedPowers

/-- Roby's formula for `dpStructureOfRequirement`. -/
theorem dpStructure_generator_formula_of_requirement
    (O : UniversalDPRequirement (R := R) (M := M) (ι := ι))
    {n k : ℕ} {m : M} (hk : k ≠ 0) :
    (dpStructureOfRequirement O).dpow n (DividedPowerAlgebra.dp R k m) =
      generatorDpow (R := R) (M := M) n k m := by
  simpa [dpStructureOfRequirement] using
    (O.input.generator_formula (n := n) (k := k) (m := m) hk)

/-- Restatement of Roby's formula for divided powers `H` on `Γ⁺` satisfying it. -/
theorem dpow_dp_eq_generatorDpow_of_formula
    (H : DividedPowers (positiveIdeal (R := R) (M := M)))
    (hformula : ∀ {n k : ℕ} {m : M}, k ≠ 0 →
      H.dpow n (DividedPowerAlgebra.dp R k m) =
        generatorDpow (R := R) (M := M) n k m) :
    ∀ {n k : ℕ} {m : M}, k ≠ 0 →
      H.dpow n (DividedPowerAlgebra.dp R k m) =
        generatorDpow (R := R) (M := M) n k m :=
  hformula

end UniversalAlgebra

end FreeConstruction
end Envelope
end AffineCrystalline
