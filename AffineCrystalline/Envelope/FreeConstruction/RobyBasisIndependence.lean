/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.RobyIndependence
import AffineCrystalline.SquareZero
import Mathlib.RingTheory.PolynomialLaw.Basic

/-!
# Linear independence of Roby monomials via coordinate functionals

Let `M` be a free `R`-module with basis `b`. To prove that the Roby monomials of
degree `n` are linearly independent, it suffices to find linear forms
`c_d : Γ_R(M) → R` with `c_d(b^[e]) = δ_{d,e}`. In Roby's theory such forms are
obtained from polynomial laws; the structure
`RobyPolynomialLawCoefficientData` records them as ground maps of
polynomial laws.

In degree `1` we construct these forms directly. For `i ∈ ι`, the divided power
algebra `R[ε] = R ⊕ R ε` with `ε² = 0` (with the divided powers of
`sqZeroDividedPowers`, so that `γ_k(ε) = 0` for `k ≥ 2`) receives the map
`Γ_R(M) → R[ε]` induced by `m ↦ b_i^*(m) ε`, which sends `[1](b_j)` to
`δ_{i,j} ε`. This proves that the Roby monomials of degree `1` are linearly
independent.

## Main definitions

* `RobyPolynomialLawCoefficientData`: polynomial laws whose ground maps
  are coordinate functionals for the Roby monomials of degree `n`.
* `degreeOneCoordinateSeparator`: the map `Γ_R(M) → R[ε]` induced by
  `m ↦ b_i^*(m) ε`.

## Main results

* `robyGradeIndependence_of_polynomialLawCoefficientData`: coordinate
  functionals imply linear independence.
* `robyGradeMonomial_degree_one_linearIndependent`: the Roby monomials of
  degree `1` are linearly independent.

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
open Module
open scoped BigOperators

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section CoefficientData

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/--
Polynomial laws `law d : Γ_R(M) → R`, indexed by the exponents `d` of degree
`n`, whose ground maps `coefficient d` are linear forms satisfying
`coefficient d (b^[e]) = δ_{d,e}`.
-/
structure RobyPolynomialLawCoefficientData
    (b : Basis ι R M) (n : ℕ) where
  coefficient : robyDegreeIndex ι n → Γ →ₗ[R] R
  law : robyDegreeIndex ι n → Γ →ₚₗ[R] R
  law_ground : ∀ d, (law d).ground = coefficient d
  diagonal_eq : ∀ d,
    coefficient d (robyGradeMonomial b n d).1 = 1
  diagonal_ne : ∀ d e, d ≠ e →
    coefficient d (robyGradeMonomial b n e).1 = 0

/-- Let `ℓ : Γ_R(M) → R` be a linear form with `ℓ (b^[d]) = 1` and `ℓ (b^[e]) = 0`
for all other exponents `e` of degree `n`. Then the coefficient of `b^[d]` in a
vanishing finite linear combination of the Roby monomials of degree `n` is zero. -/
theorem coeff_eq_zero_of_coordinate (b : Basis ι R M) (n : ℕ) {d : robyDegreeIndex ι n}
    (ℓ : Γ →ₗ[R] R) (hℓd : ℓ (robyGradeMonomial b n d).1 = 1)
    (hℓ : ∀ e, e ≠ d → ℓ (robyGradeMonomial b n e).1 = 0) (c : robyDegreeIndex ι n →₀ R)
    (hc : c.support.sum (fun e ↦ c e • robyGradeMonomial b n e) = 0) : c d = 0 := by
  classical
  have hc' : c.support.sum (fun e ↦ c e • (robyGradeMonomial b n e).1) = 0 := by
    simpa using congrArg (robyGrade b n).subtype hc
  have h := congrArg ℓ hc'
  rw [map_sum, map_zero, Finset.sum_eq_single d] at h
  · rwa [map_smul, hℓd, smul_eq_mul, mul_one] at h
  · intro e _ he
    rw [map_smul, hℓ e he, smul_zero]
  · intro hd
    rw [Finsupp.notMem_support_iff.mp hd, zero_smul, map_zero]

/-- Coordinate functionals for the Roby monomials of degree `n` show that these
monomials admit no nontrivial finite linear relation. -/
theorem robyGradeIndependence_of_polynomialLawCoefficientData
    (b : Basis ι R M) (n : ℕ)
    (C : RobyPolynomialLawCoefficientData b n) :
    RobyFiniteSupportIndependenceData b n where
  zero_of_finite_sum c hc := Finsupp.ext fun d ↦
    coeff_eq_zero_of_coordinate b n (C.coefficient d) (C.diagonal_eq d)
      (fun e he ↦ C.diagonal_ne d e (Ne.symm he)) c hc

end CoefficientData

section DegreeOneSeparator

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-- The map `Γ_R(M) → R[ε]`, `ε² = 0`, induced by the linear map
`m ↦ b_i^*(m) ε` into the divided power ideal `R ε`. -/
noncomputable def degreeOneCoordinateSeparator
    (b : Basis ι R M) (i : ι) : Γ →ₐ[R] TrivSqZeroExt R R :=
  DividedPowerAlgebra.lift
    (sqZeroDividedPowers (dividedPowersBot R) R)
    ((TrivSqZeroExt.inrHom R R).comp (b.coord i))
    (by
      intro m
      rw [mem_sqZeroIdeal]
      rfl)

/-- The map `degreeOneCoordinateSeparator b i` sends `[1](m)` to `b_i^*(m) ε`. -/
@[simp]
theorem degreeOneCoordinateSeparator_dp_one
    (b : Basis ι R M) (i : ι) (m : M) :
    degreeOneCoordinateSeparator b i (DividedPowerAlgebra.dp R 1 m) =
      TrivSqZeroExt.inr (b.coord i m) := by
  rw [degreeOneCoordinateSeparator, DividedPowerAlgebra.lift_apply_dp]
  change sqZeroDpow (dividedPowersBot R) R 1
      ((TrivSqZeroExt.inrHom R R) (b.coord i m)) = _
  rw [sqZeroDpow_one]
  · rfl
  · rw [mem_sqZeroIdeal]
    rfl

/-- The Roby monomial of the exponent `eᵢ` is `[1](bᵢ)`. -/
theorem robyMonomial_single_one
    (b : Basis ι R M) (i : ι) :
    robyMonomial b (Finsupp.single i 1) =
      DividedPowerAlgebra.dp R 1 (b i) := by
  classical
  rw [robyMonomial]
  rw [Finsupp.prod_of_support_subset (Finsupp.single i 1)
    Finsupp.support_single_subset]
  · simp
  · intro j hj
    have hji : j = i := by simpa using hj
    subst j
    change DividedPowerAlgebra.dp R 0 (b i) = 1
    exact DividedPowerAlgebra.dp_zero

/-- Every exponent of degree `1` is of the form `eᵢ = Finsupp.single i 1`. -/
theorem exists_single_eq_of_robyDegreeIndex_one (d : robyDegreeIndex ι 1) :
    ∃ i, Finsupp.single i 1 = d.1 := by
  have hd : d.1 ∈ Set.range (fun i : ι ↦ Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact d.2
  exact hd

/-- The `ε`-coordinate of `degreeOneCoordinateSeparator b i [1](bⱼ)` is
`b_i^*(b_j) = δ_{i,j}`. -/
theorem snd_degreeOneCoordinateSeparator_robyMonomial_single (b : Basis ι R M) (i j : ι) :
    (degreeOneCoordinateSeparator b i (robyMonomial b (Finsupp.single j 1))).snd =
      Finsupp.single j 1 i := by
  rw [robyMonomial_single_one, degreeOneCoordinateSeparator_dp_one, TrivSqZeroExt.snd_inr,
    Basis.coord_apply, Basis.repr_self]

/-- The Roby monomials of degree `1`, namely the `[1](bᵢ)`, are linearly
independent. -/
theorem robyGradeMonomial_degree_one_linearIndependent
    (b : Basis ι R M) :
    LinearIndependent R (robyGradeMonomial b 1) := by
  refine (robyGrade_linearIndependent_iff_finiteSupport b 1).2 fun c hc ↦ Finsupp.ext fun d ↦ ?_
  obtain ⟨i, hi⟩ := exists_single_eq_of_robyDegreeIndex_one d
  let ℓ : Γ →ₗ[R] R :=
    (TrivSqZeroExt.sndHom R R).comp (degreeOneCoordinateSeparator b i).toLinearMap
  have hℓ (j : ι) : ℓ (robyMonomial b (Finsupp.single j 1)) = Finsupp.single j (1 : R) i :=
    snd_degreeOneCoordinateSeparator_robyMonomial_single b i j
  refine coeff_eq_zero_of_coordinate b 1 ℓ ?_ (fun e he ↦ ?_) c hc
  · rw [robyGradeMonomial_apply_val, ← hi, hℓ, Finsupp.single_eq_same]
  · obtain ⟨j, hj⟩ := exists_single_eq_of_robyDegreeIndex_one e
    rw [robyGradeMonomial_apply_val, ← hj, hℓ, Finsupp.single_eq_of_ne]
    rintro rfl
    exact he (Subtype.ext (hj.symm.trans hi))

/-- The Roby monomials of degree `1` admit no nontrivial finite linear
relation. -/
theorem robyGradeDegreeOneIndependenceData
    (b : Basis ι R M) :
    RobyFiniteSupportIndependenceData b 1 :=
  robyFiniteSupportIndependenceData_of_linearIndependent b 1
    (robyGradeMonomial_degree_one_linearIndependent b)

end DegreeOneSeparator

end FreeConstruction
end Envelope
end AffineCrystalline
