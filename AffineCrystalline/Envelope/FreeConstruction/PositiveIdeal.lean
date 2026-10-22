/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.PositiveDPStructure
import AffineCrystalline.Envelope.FreeConstruction.RelationGenerators

/-!
# Divided powers on the positive ideal and quotient data

Let `γ` be divided powers on the positive ideal `Γ⁺` of the divided power
algebra `Γ_R(M)` satisfying Roby's formula (`PositiveDPStructure`). This
file restates the axioms of divided powers for `γ` on `Γ⁺`, and introduces
quotient data: an ideal `K` of `Γ_R(M)` such that `K ⊓ Γ⁺` is a sub-divided power
ideal. For the envelope construction, `K` is the relation ideal `J₁₂` of
`AffineCrystalline.Envelope.FreeConstruction.RelationGenerators`.

## Main definitions

* `PositiveAugmentationData`: the statement that `Γ⁺` is a sub-divided power
  ideal of itself.
* `PositiveAugmentationQuotientData`: an ideal `K` with `K ⊓ Γ⁺` a
  sub-divided power ideal.
* `relationGeneratorsQuotientData`,
  `relationGeneratorsCanonicalQuotientData`: the quotient data attached to the
  relation ideal `J₁₂`, given a proof that `J₁₂ ⊓ Γ⁺` is a sub-divided power
  ideal.

## Main results

* `canonicalPositiveAugmentationData`: `Γ⁺` is a sub-divided power ideal of
  itself.
* `positive_dpow_add`, `positive_dpow_mul`, `positive_mul_dpow`,
  `positive_dpow_comp`: the divided power axioms for `γ` on `Γ⁺`.

## References

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

section PositiveAugmentation

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

local notation "Γ" => DividedPowerAlgebra R M

/-! ## The positive ideal as a sub-divided power ideal -/

/--
The statement that `Γ⁺` is a sub-divided power ideal of `(Γ⁺, γ)`; it holds by
`canonicalPositiveAugmentationData`.
-/
structure PositiveAugmentationData
    (P : PositiveDPStructure (R := R) (M := M)) where
  positive_isSubDPIdeal :
    IsSubDPIdeal P.dividedPowers (positiveIdeal (R := R) (M := M))

/-- `Γ⁺` is a sub-divided power ideal of itself. -/
theorem canonicalPositiveAugmentationData
    (P : PositiveDPStructure (R := R) (M := M)) :
    PositiveAugmentationData (R := R) (M := M) P :=
  ⟨IsSubDPIdeal.self P.dividedPowers⟩

theorem PositiveAugmentationData.positive_isSubideal
    (P : PositiveDPStructure (R := R) (M := M))
    (D : PositiveAugmentationData (R := R) (M := M) P) :
    positiveIdeal (R := R) (M := M) ≤ positiveIdeal (R := R) (M := M) :=
  D.positive_isSubDPIdeal.isSubideal

theorem positive_zero_mem :
    (0 : Γ) ∈ positiveIdeal (R := R) (M := M) :=
  (positiveIdeal (R := R) (M := M)).zero_mem

theorem positive_add_mem {x y : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M))
    (hy : y ∈ positiveIdeal (R := R) (M := M)) :
    x + y ∈ positiveIdeal (R := R) (M := M) :=
  (positiveIdeal (R := R) (M := M)).add_mem hx hy

theorem positive_mul_mem_left (a : Γ) {x : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    a * x ∈ positiveIdeal (R := R) (M := M) :=
  (positiveIdeal (R := R) (M := M)).mul_mem_left a hx

theorem positive_mul_mem_right (a : Γ) {x : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    x * a ∈ positiveIdeal (R := R) (M := M) :=
  (positiveIdeal (R := R) (M := M)).mul_mem_right a hx

theorem positive_sub_mem {x y : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M))
    (hy : y ∈ positiveIdeal (R := R) (M := M)) :
    x - y ∈ positiveIdeal (R := R) (M := M) :=
  (positiveIdeal (R := R) (M := M)).sub_mem hx hy

/-! ## The divided power axioms on the positive ideal -/

theorem positive_dpow_zero
    (P : PositiveDPStructure (R := R) (M := M))
    {x : Γ} (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow 0 x = 1 :=
  P.dividedPowers.dpow_zero hx

theorem positive_dpow_one
    (P : PositiveDPStructure (R := R) (M := M))
    {x : Γ} (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow 1 x = x :=
  P.dividedPowers.dpow_one hx

theorem positive_dpow_mem
    (P : PositiveDPStructure (R := R) (M := M))
    {n : ℕ} (hn : n ≠ 0) {x : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow n x ∈ positiveIdeal (R := R) (M := M) :=
  P.dividedPowers.dpow_mem hn hx

theorem positive_dpow_add
    (P : PositiveDPStructure (R := R) (M := M))
    {n : ℕ} {x y : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M))
    (hy : y ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow n (x + y) =
      (Finset.antidiagonal n).sum
        (fun k ↦ P.dividedPowers.dpow k.1 x *
          P.dividedPowers.dpow k.2 y) :=
  P.dividedPowers.dpow_add hx hy

theorem positive_dpow_mul
    (P : PositiveDPStructure (R := R) (M := M))
    {n : ℕ} {a x : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow n (a * x) =
      a ^ n * P.dividedPowers.dpow n x :=
  P.dividedPowers.dpow_mul hx

theorem positive_mul_dpow
    (P : PositiveDPStructure (R := R) (M := M))
    {m n : ℕ} {x : Γ}
    (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow m x * P.dividedPowers.dpow n x =
      (Nat.choose (m + n) m : Γ) * P.dividedPowers.dpow (m + n) x :=
  P.dividedPowers.mul_dpow hx

theorem positive_dpow_comp
    (P : PositiveDPStructure (R := R) (M := M))
    {m n : ℕ} {x : Γ} (hn : n ≠ 0)
    (hx : x ∈ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow m (P.dividedPowers.dpow n x) =
      (Nat.uniformBell m n : Γ) * P.dividedPowers.dpow (m * n) x :=
  P.dividedPowers.dpow_comp hn hx

/-! ## Quotient data -/

/--
An ideal `K` of `Γ_R(M)` such that `K ⊓ Γ⁺` is a sub-divided power ideal of
`(Γ⁺, γ)`, so that `γ` descends to the quotient `Γ_R(M) ⧸ K`.
-/
structure PositiveAugmentationQuotientData
    (P : PositiveDPStructure (R := R) (M := M)) where
  relationIdeal : Ideal Γ
  relation_isSubDPIdeal :
    IsSubDPIdeal P.dividedPowers
      (relationIdeal ⊓ positiveIdeal (R := R) (M := M))

namespace PositiveAugmentationQuotientData

variable (P : PositiveDPStructure (R := R) (M := M))
variable (Q : PositiveAugmentationQuotientData (R := R) (M := M) P)

theorem intersection_le_positive :
    Q.relationIdeal ⊓ positiveIdeal (R := R) (M := M) ≤
      positiveIdeal (R := R) (M := M) :=
  inf_le_right

theorem intersection_le_relation :
    Q.relationIdeal ⊓ positiveIdeal (R := R) (M := M) ≤ Q.relationIdeal :=
  inf_le_left

theorem intersection_dpow_mem {n : ℕ} (hn : n ≠ 0) {x : Γ}
    (hx : x ∈ Q.relationIdeal ⊓ positiveIdeal (R := R) (M := M)) :
    P.dividedPowers.dpow n x ∈
      Q.relationIdeal ⊓ positiveIdeal (R := R) (M := M) :=
  Q.relation_isSubDPIdeal.dpow_mem n hn hx

/-- The same data, as a `PositiveDPQuotientData`. -/
def toPositiveDPQuotientData :
    PositiveDPQuotientData (R := R) (M := M) P :=
  { relationIdeal := Q.relationIdeal
    relation_isSubDPIdeal := Q.relation_isSubDPIdeal }

@[simp]
theorem toPositiveDPQuotientData_relationIdeal :
    (Q.toPositiveDPQuotientData P).relationIdeal = Q.relationIdeal :=
  rfl

theorem toPositiveDPQuotientData_stability :
    (Q.toPositiveDPQuotientData P).relation_isSubDPIdeal =
      Q.relation_isSubDPIdeal :=
  rfl

end PositiveAugmentationQuotientData

end PositiveAugmentation

section RelationGeneratorQuotient

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {B : Type v} [CommRing B] [Algebra A B] (J : Ideal B)
variable (hIJ : I.map (algebraMap A B) ≤ J)

local notation "ΓB" => DividedPowerAlgebra B J

/--
The relation ideal `J₁₂ = J₁ + J₂`, generated by the families `Rel1` and `Rel2'`,
as quotient data, given a proof that `J₁₂ ⊓ Γ⁺` is a sub-divided power ideal.
-/
def relationGeneratorsQuotientData
    (P : PositiveDPStructure (R := B) (M := J))
    (hstable :
      IsSubDPIdeal P.dividedPowers
        (relationIdeal hI J hIJ ⊓ positiveIdeal (R := B) (M := J))) :
    PositiveAugmentationQuotientData (R := B) (M := J) P :=
  { relationIdeal := relationIdeal hI J hIJ
    relation_isSubDPIdeal := hstable }

/-- The relation ideal `J₁₂` as a `PositiveDPQuotientData`. -/
def relationGeneratorsCanonicalQuotientData
    (P : PositiveDPStructure (R := B) (M := J))
    (hstable :
      IsSubDPIdeal P.dividedPowers
        (relationIdeal hI J hIJ ⊓ positiveIdeal (R := B) (M := J))) :
    PositiveDPQuotientData (R := B) (M := J) P :=
  (relationGeneratorsQuotientData hI J hIJ P hstable).toPositiveDPQuotientData P

@[simp]
theorem relationGeneratorsCanonicalQuotientData_relationIdeal
    (P : PositiveDPStructure (R := B) (M := J))
    (hstable :
      IsSubDPIdeal P.dividedPowers
        (relationIdeal hI J hIJ ⊓ positiveIdeal (R := B) (M := J))) :
    (relationGeneratorsCanonicalQuotientData hI J hIJ P hstable).relationIdeal =
      relationIdeal hI J hIJ :=
  rfl

end RelationGeneratorQuotient

end FreeConstruction
end Envelope
end AffineCrystalline
