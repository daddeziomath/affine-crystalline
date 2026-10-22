/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.DPAlgebraAugmentation
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-!
# Roby's divided powers on `Γ⁺` and their quotients

Let `P : PositiveDPStructure` be divided powers `γ` on the positive ideal
`Γ⁺` of the divided power algebra `Γ_R(M)` satisfying Roby's formula
`γ_n([k](m)) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`. We prove that such a
structure is unique, compute the divided powers of generators, and show that
`γ` descends to the quotient `Γ_R(M) ⧸ K` for any ideal `K` such that `K ⊓ Γ⁺` is
a sub-divided power ideal.

## Main definitions

* `PositiveDPQuotientData`: an ideal `K` of `Γ_R(M)` together with a proof
  that `K ⊓ Γ⁺` is a sub-divided power ideal of `(Γ⁺, γ)`.
* `PositiveDPQuotientData.quotientDividedPowers`: the induced divided
  powers on the image of `Γ⁺` in `Γ_R(M) ⧸ K`.

## Main results

* `PositiveDPStructure.ext`: two such structures are equal.
* `PositiveDPStructure.dpow_generator_comp`: the value of
  `γ_n(γ_k([l](m)))`.
* `PositiveDPQuotientData.quotientMap_isDPMorphism`: the quotient map is a
  divided power morphism.
* `PositiveDPQuotientData.quotient_dpow_generator_formula`: Roby's formula
  in the quotient.

## References

* N. Roby, *Les algèbres à puissances divisées*, Bull. Sci. Math. (2) 89 (1965),
  75–91.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *A formalization of divided
  powers in Lean*, ITP 2025, LIPIcs, 4:1–4:17.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *Formalizing polynomial laws
  and the universal divided power algebra*, arXiv:2512.05750.
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section PositiveDPStructure

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

local notation "Γ" => DividedPowerAlgebra R M

/-! ## Uniqueness and generator consequences -/

/-- Divided powers on `Γ⁺` satisfying Roby's formula are unique: two of them
agree on the generators `[k](m)`, `k > 0`, which generate `Γ⁺`. -/
theorem PositiveDPStructure.ext
    (P Q : PositiveDPStructure (R := R) (M := M)) : P = Q := by
  obtain ⟨p, hp⟩ := P
  obtain ⟨q, hq⟩ := Q
  obtain rfl : q = p := dividedPowers_eq_of_positiveGenerator_agreement (R := R) (M := M)
    (hgen := by
      rintro n _ ⟨k, hk, m, rfl⟩
      exact (hp hk).trans (hq hk).symm)
  rfl

@[simp]
theorem PositiveDPStructure.dpow_generator_zero
    (P : PositiveDPStructure (R := R) (M := M))
    {k : ℕ} (hk : k ≠ 0) (m : M) :
    P.dividedPowers.dpow 0 (DividedPowerAlgebra.dp R k m) = 1 :=
  P.dividedPowers.dpow_zero
    (dp_mem_positiveIdeal (R := R) (M := M) hk m)

@[simp]
theorem PositiveDPStructure.dpow_generator_one
    (P : PositiveDPStructure (R := R) (M := M))
    {k : ℕ} (hk : k ≠ 0) (m : M) :
    P.dividedPowers.dpow 1 (DividedPowerAlgebra.dp R k m) =
      DividedPowerAlgebra.dp R k m := by
  calc
    P.dividedPowers.dpow 1 (DividedPowerAlgebra.dp R k m) =
        generatorDpow (R := R) (M := M) 1 k m := P.generator_formula hk
    _ = DividedPowerAlgebra.dp R k m :=
      generatorDpow_one_left (R := R) (M := M) k m

theorem PositiveDPStructure.dpow_generator_mem
    (P : PositiveDPStructure (R := R) (M := M))
    {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) (m : M) :
    P.dividedPowers.dpow n (DividedPowerAlgebra.dp R k m) ∈
      positiveIdeal (R := R) (M := M) :=
  P.dividedPowers.dpow_mem hn
    (dp_mem_positiveIdeal (R := R) (M := M) hk m)

/-- For `k, l > 0`,
`γ_n(γ_k([l](m))) = (nk)!/(n!(k!)ⁿ) · (nkl)!/((nk)!(l!)^{nk}) · [nkl](m)`. -/
theorem PositiveDPStructure.dpow_generator_comp
    (P : PositiveDPStructure (R := R) (M := M))
    {n k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (m : M) :
    P.dividedPowers.dpow n
        (P.dividedPowers.dpow k (DividedPowerAlgebra.dp R l m)) =
      (Nat.uniformBell n k : Γ) *
        (Nat.uniformBell (n * k) l : Γ) *
          DividedPowerAlgebra.dp R (n * k * l) m := by
  calc
    P.dividedPowers.dpow n
          (P.dividedPowers.dpow k (DividedPowerAlgebra.dp R l m)) =
        (Nat.uniformBell n k : Γ) *
          P.dividedPowers.dpow (n * k) (DividedPowerAlgebra.dp R l m) :=
      P.dividedPowers.dpow_comp hk
        (dp_mem_positiveIdeal (R := R) (M := M) hl m)
    _ = (Nat.uniformBell n k : Γ) *
          (Nat.uniformBell (n * k) l : Γ) *
            DividedPowerAlgebra.dp R (n * k * l) m := by
      rw [P.generator_formula hl]
      simp only [generatorDpow, mul_assoc]

/-! ## Quotients -/

/-- An ideal `K` of `Γ_R(M)` such that `K ⊓ Γ⁺` is a sub-divided power ideal of
`(Γ⁺, γ)`. This is the condition under which `γ` descends to `Γ_R(M) ⧸ K`. -/
structure PositiveDPQuotientData
    (P : PositiveDPStructure (R := R) (M := M)) where
  relationIdeal : Ideal Γ
  relation_isSubDPIdeal :
    IsSubDPIdeal P.dividedPowers
      (relationIdeal ⊓ positiveIdeal (R := R) (M := M))

namespace PositiveDPQuotientData

variable (P : PositiveDPStructure (R := R) (M := M))
variable (Q : PositiveDPQuotientData (R := R) (M := M) P)

/-- The quotient ring `Γ_R(M) ⧸ K`. -/
abbrev quotient : Type u := Γ ⧸ Q.relationIdeal

/-- The quotient map `Γ_R(M) → Γ_R(M) ⧸ K`. -/
def quotientMap : Γ →+* quotient P Q := Ideal.Quotient.mk Q.relationIdeal

/-- The quotient divided powers on the image of `Γ⁺` in `Γ_R(M) ⧸ K`. -/
noncomputable def quotientDividedPowers :
    DividedPowers
      ((positiveIdeal (R := R) (M := M)).map (quotientMap P Q)) :=
  DividedPowers.Quotient.dividedPowers P.dividedPowers
    Q.relation_isSubDPIdeal

theorem quotientMap_isDPMorphism :
    IsDPMorphism P.dividedPowers (quotientDividedPowers P Q) (quotientMap P Q) :=
  DividedPowers.Quotient.isDPMorphism P.dividedPowers Q.relation_isSubDPIdeal

theorem quotient_dpow_generator
    {n k : ℕ} (hk : k ≠ 0) (m : M) :
    (quotientDividedPowers P Q).dpow n
        ((quotientMap P Q) (DividedPowerAlgebra.dp R k m)) =
      (quotientMap P Q)
        (P.dividedPowers.dpow n (DividedPowerAlgebra.dp R k m)) :=
  DividedPowers.Quotient.dpow_apply P.dividedPowers
    Q.relation_isSubDPIdeal
    (dp_mem_positiveIdeal (R := R) (M := M) hk m)

/-- Roby's formula for the images of the generators in `Γ_R(M) ⧸ K`. -/
theorem quotient_dpow_generator_formula
    {n k : ℕ} (hk : k ≠ 0) (m : M) :
    (quotientDividedPowers P Q).dpow n
        ((quotientMap P Q) (DividedPowerAlgebra.dp R k m)) =
      (quotientMap P Q)
        (generatorDpow (R := R) (M := M) n k m) := by
  rw [quotient_dpow_generator P Q hk m, P.generator_formula hk]

end PositiveDPQuotientData

end PositiveDPStructure

end FreeConstruction
end Envelope
end AffineCrystalline
