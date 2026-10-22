/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.J12Stability
import AffineCrystalline.Envelope.FreeConstruction.IncludedEnvelopeConstruction
import AffineCrystalline.Envelope.FreeConstruction.RobyDpowConstruction

/-!
# Divided powers of the generators of the relation ideal

Let `δ` be Roby's divided powers on the positive ideal `Γ⁺` of `Γ_B(J)` and let
`J₁₂ = J₁ + J₂` be the relation ideal of the divided power envelope. This file
studies the divided powers of the generators of `J₁` and `J₂`.

For `x ∈ J`, the generator `[1](x) - x` of `J₁` has augmentation `-x`, hence lies
in `Γ⁺` only when `x = 0`. For the generators `g = [n](x) - [1](γ_n(x))` of `J₂`
we have `δ_0(g) = 1` and `δ_1(g) = g ∈ J₂`, so the condition `δ_r(g) ∈ J₂` in
`J12CompatibilityData` only needs to be checked for `r ≥ 2`. We also
record the expansion of `δ_r(a - b)` for `a, b ∈ Γ⁺`.

## Main definitions

* `rel1Generator`: the generator `[1](x) - x` of `J₁`.
* `Rel2GeneratorStabilityData`: the statement `δ_r(g) ∈ J₂` for `r > 0`
  and all generators `g` of `J₂`.
* `Rel2HigherStabilityData`: the same statement for `r ≥ 2`.

## Main results

* `rel1Generator_mem_positive_iff`: `[1](x) - x ∈ Γ⁺ ↔ x = 0`.
* `rel2_dpow_one_mem_j2`: `δ_1(g) ∈ J₂` for every generator `g` of `J₂`.
* `dpow_sub_expansion`:
  `δ_r(a - b) = ∑_{i + j = r} δ_i(a) · (-1)ʲ · δ_j(b)` for `a, b ∈ Γ⁺`.
* `Rel2HigherStabilityData.toJ12CompatibilityData`: the case
  `r ≥ 2`, together with the two ideal identities, yields a
  `J12CompatibilityData`.

## References

* P. Berthelot and A. Ogus, *Notes on crystalline cohomology*, Mathematical
  Notes 21, Princeton University Press (1978), §3.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *A formalization of divided
  powers in Lean*, ITP 2025, LIPIcs, 4:1–4:17.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *Formalizing polynomial laws
  and the universal divided power algebra*, arXiv:2512.05750.
-/

open DividedPowerAlgebra DividedPowers Ideal
open scoped BigOperators

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section J12GeneratorStability

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {B : Type v} [CommRing B] [Algebra A B] (J : Ideal B)
  (hIJ : I.map (algebraMap A B) ≤ J)

local notation "Γ" => DividedPowerAlgebra B J

variable (P : PositiveDPStructure (R := B) (M := J))

/-! ## The first relation family -/

/-- The generator `[1](x) - x` of `J₁`, for `x ∈ J`. -/
def rel1Generator (x : J) : Γ :=
  DividedPowerAlgebra.embed B J x - algebraMap B Γ (x : B)

theorem rel1Generator_mem_j1 (x : J) :
    rel1Generator J x ∈ j1 J :=
  rel1_mem_j1 J x

theorem augmentation_apply_embed (x : J) :
    augmentation (R := B) (M := J)
        (DividedPowerAlgebra.embed B J x) = 0 := by
  rw [DividedPowerAlgebra.embed_def]
  simp

theorem augmentation_apply_rel1Generator (x : J) :
    augmentation (R := B) (M := J) (rel1Generator J x) = -(x : B) := by
  simp [rel1Generator, augmentation_apply_embed]

/-- The generator `[1](x) - x` of `J₁` lies in `Γ⁺` if and only if `x = 0`, since
its augmentation is `-x`. In particular, `J₁` is not contained in `Γ⁺` unless
`J = 0`. -/
theorem rel1Generator_mem_positive_iff (x : J) :
    rel1Generator J x ∈ positiveIdeal (R := B) (M := J) ↔ x = 0 := by
  constructor
  · intro hx
    have hk : rel1Generator J x ∈
        RingHom.ker (augmentation (R := B) (M := J)).toRingHom := by
      rw [← positiveIdeal_eq_augmentation_ker (R := B) (M := J)]
      exact hx
    change augmentation (R := B) (M := J) (rel1Generator J x) = 0 at hk
    have hxB : (x : B) = 0 := by
      rw [augmentation_apply_rel1Generator J x] at hk
      exact neg_eq_zero.mp hk
    apply Subtype.ext
    exact hxB
  · intro hx
    subst x
    simp [rel1Generator]

theorem rel1Generator_dpow_mem_of_positive
    {r : ℕ} (hr : r ≠ 0) (x : J)
    (hx : rel1Generator J x ∈ positiveIdeal (R := B) (M := J)) :
    P.dividedPowers.dpow r (rel1Generator J x) ∈ j1 J := by
  have hx0 : x = 0 := (rel1Generator_mem_positive_iff J x).1 hx
  subst x
  rw [show rel1Generator J (0 : J) = 0 by simp [rel1Generator]]
  rw [P.dividedPowers.dpow_eval_zero hr]
  exact (j1 J).zero_mem

/-! ## The second relation family -/

theorem rel2Generator_mem_j2 {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2Generator hI J hIJ x hn ∈ j2 hI J hIJ :=
  rel2'_mem_j2 hI J hIJ x hn

theorem rel2Generator_mem_positive {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2Generator hI J hIJ x hn ∈ positiveIdeal (R := B) (M := J) :=
  rel2Generator_mem_positiveIdeal hI J hIJ hn

/-- Since `δ_1` is the identity on `Γ⁺`, every generator `g` of `J₂` satisfies
`δ_1(g) = g ∈ J₂`. -/
theorem rel2_dpow_one_mem_j2 {x : I} {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow 1 (rel2Generator hI J hIJ x hn) ∈
      j2 hI J hIJ := by
  rw [P.dividedPowers.dpow_one
    (rel2Generator_mem_positiveIdeal hI J hIJ hn)]
  exact rel2Generator_mem_j2 hI J hIJ hn

theorem rel2_dpow_zero_eq_one {x : I} {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow 0 (rel2Generator hI J hIJ x hn) = 1 :=
  P.dividedPowers.dpow_zero (rel2Generator_mem_positiveIdeal hI J hIJ hn)

theorem rel2_dpow_mem_of_zero
    {r : ℕ} (hr : r ≠ 0) {x : I} {n : ℕ} (hn : n ≠ 0)
    (hz : rel2Generator hI J hIJ x hn = 0) :
    P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈
      j2 hI J hIJ := by
  rw [hz, P.dividedPowers.dpow_eval_zero hr]
  exact (j2 hI J hIJ).zero_mem

/-! ## Divided powers of a difference -/

/-- For `a, b ∈ Γ⁺`, `δ_r(a - b) = ∑_{i + j = r} δ_i(a) · (-1)ʲ · δ_j(b)`. -/
theorem dpow_sub_expansion {r : ℕ} {a b : Γ}
    (ha : a ∈ positiveIdeal (R := B) (M := J))
    (hb : b ∈ positiveIdeal (R := B) (M := J)) :
    P.dividedPowers.dpow r (a - b) =
      (Finset.antidiagonal r).sum (fun k ↦
        P.dividedPowers.dpow k.1 a *
          ((-1 : Γ) ^ k.2 * P.dividedPowers.dpow k.2 b)) := by
  have hneg : (-1 : Γ) * b ∈ positiveIdeal (R := B) (M := J) := by
    exact (positiveIdeal (R := B) (M := J)).mul_mem_left (-1) hb
  have hadd := P.dividedPowers.dpow_add (n := r) ha hneg
  have hmul : ∀ k : ℕ,
      P.dividedPowers.dpow k ((-1 : Γ) * b) =
        (-1 : Γ) ^ k * P.dividedPowers.dpow k b := by
    intro k
    exact P.dividedPowers.dpow_mul hb
  rw [show a - b = a + (-1 : Γ) * b by ring, hadd]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hmul]

theorem rel2Left_mem_positive {x : I} {n : ℕ} (hn : n ≠ 0) :
    DividedPowerAlgebra.dp B n
        (⟨algebraMap A B x,
          hIJ (Ideal.mem_map_of_mem (algebraMap A B) x.2)⟩ : J) ∈
      positiveIdeal (R := B) (M := J) :=
  dp_mem_positiveIdeal hn _

theorem rel2Right_mem_positive {x : I} {n : ℕ} (hn : n ≠ 0) :
    DividedPowerAlgebra.embed B J
        ⟨algebraMap A B (hI.dpow n x),
          algebraMap_dpow_mem hI J hIJ x hn⟩ ∈
      positiveIdeal (R := B) (M := J) := by
  rw [DividedPowerAlgebra.embed_def]
  exact dp_mem_positiveIdeal one_ne_zero _

/-! ## Divided powers of the generators of `J₂` -/

/-- The statement that `δ_r(g) ∈ J₂` for all `r > 0` and all generators
`g = [n](x) - [1](γ_n(x))` of `J₂`. -/
structure Rel2GeneratorStabilityData where
  rel2_dpow_mem :
    ∀ {r : ℕ}, r ≠ 0 → ∀ (x : I) {n : ℕ} (hn : n ≠ 0),
      P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈
        j2 hI J hIJ

namespace Rel2GeneratorStabilityData

variable (D : Rel2GeneratorStabilityData hI J hIJ P)

theorem rel2_dpow_one_mem {x : I} {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow 1 (rel2Generator hI J hIJ x hn) ∈
      j2 hI J hIJ :=
  rel2_dpow_one_mem_j2 (hI := hI) (J := J) (hIJ := hIJ) (P := P) hn

theorem toJ12CompatibilityData
    (D : Rel2GeneratorStabilityData hI J hIJ P)
    (hintersection :
      j12 hI J hIJ ⊓ positiveIdeal (R := B) (M := J) =
        (j1 J ⊓ positiveIdeal (R := B) (M := J)) + j2 hI J hIJ)
    (hproduct :
      j1 J ⊓ positiveIdeal (R := B) (M := J) =
        positiveIdeal (R := B) (M := J) • j1 J) :
    J12CompatibilityData hI J hIJ P :=
  { intersection_eq_sum := hintersection
    j1_intersection_eq_prod := hproduct
    rel2_dpow_mem := D.rel2_dpow_mem }

end Rel2GeneratorStabilityData

/-- The statement that `δ_r(g) ∈ J₂` for all `r ≥ 2` and all generators `g` of
`J₂`. By `rel2_dpow_one_mem_j2` it implies the same statement for all `r > 0`
(`toRel2GeneratorStabilityData`). -/
structure Rel2HigherStabilityData where
  rel2_dpow_mem_of_two_le :
    ∀ {r : ℕ}, 2 ≤ r → ∀ (x : I) {n : ℕ} (hn : n ≠ 0),
      P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈
        j2 hI J hIJ

namespace Rel2HigherStabilityData

variable (D : Rel2HigherStabilityData hI J hIJ P)

theorem toRel2GeneratorStabilityData
    (D : Rel2HigherStabilityData hI J hIJ P) :
    Rel2GeneratorStabilityData hI J hIJ P where
  rel2_dpow_mem := by
    intro r hr x n hn
    by_cases hr1 : r = 1
    · subst r
      exact rel2_dpow_one_mem_j2 (hI := hI) (J := J) (hIJ := hIJ)
        (P := P) hn
    · exact Rel2HigherStabilityData.rel2_dpow_mem_of_two_le
        D (by omega) x hn

theorem toJ12CompatibilityData
    (D : Rel2HigherStabilityData hI J hIJ P)
    (hintersection :
      j12 hI J hIJ ⊓ positiveIdeal (R := B) (M := J) =
        (j1 J ⊓ positiveIdeal (R := B) (M := J)) + j2 hI J hIJ)
    (hproduct :
      j1 J ⊓ positiveIdeal (R := B) (M := J) =
        positiveIdeal (R := B) (M := J) • j1 J) :
    J12CompatibilityData hI J hIJ P :=
  Rel2GeneratorStabilityData.toJ12CompatibilityData
    (hI := hI) (J := J) (hIJ := hIJ) (P := P)
    (D := toRel2GeneratorStabilityData (hI := hI) (J := J) (hIJ := hIJ)
      (P := P) D) hintersection hproduct

end Rel2HigherStabilityData

end J12GeneratorStability

end FreeConstruction
end Envelope
end AffineCrystalline
