/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.J12GeneratorStability
import AffineCrystalline.DeRham.RiouRelationInduction
import AffineCrystalline.Envelope.FreeConstruction.RelationGenerators

/-!
# Higher divided powers of the generators of `J₂`

Let `δ` be Roby's divided powers on the positive ideal `Γ⁺` of `Γ_B(J)` and let
`g = [n](x) - [1](γ_n(x))`, for `x ∈ I` and `n > 0`, be a generator of the second
relation ideal `J₂`. By the binomial formula for divided powers,
`δ_r(g) = ∑_{i + j = r} δ_i([n](x)) · (-1)ʲ · δ_j([1](γ_n(x)))`.
We reduce the condition `δ_r(g) ∈ J₂`, for `r ≥ 2`, to the membership in `J₂` of
each summand of this expansion.

## Main definitions

* `rel2ExpansionTerm`: the summand `δ_i([n](x)) · (-1)ʲ · δ_j([1](γ_n(x)))`.
* `Rel2HigherExpansionData`: the statement that every summand lies in
  `J₂` when `r ≥ 2`.

## Main results

* `rel2_dpow_expansion`: the binomial expansion of `δ_r(g)`.
* `rel2_dpow_mem_of_two_le_of_termwise`: if every summand lies in `J₂`, then
  `δ_r(g) ∈ J₂`.
* `rel2_dpow_two_mem_iff_expansion_mem`: the case `r = 2`.
* `Rel2HigherExpansionData.toJ12CompatibilityData`: together with
  the two ideal identities, a `Rel2HigherExpansionData` yields a
  `J12CompatibilityData`.

## References

* P. Berthelot and A. Ogus, *Notes on crystalline cohomology*, Mathematical
  Notes 21, Princeton University Press (1978), §3.
* N. Roby, *Les algèbres à puissances divisées*, Bull. Sci. Math. (2) 89 (1965),
  75–91.
-/

open DividedPowerAlgebra DividedPowers Ideal
open scoped BigOperators

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section J12HigherStability

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {B : Type v} [CommRing B] [Algebra A B] (J : Ideal B)
  (hIJ : I.map (algebraMap A B) ≤ J)

local notation "Γ" => DividedPowerAlgebra B J

variable (P : PositiveDPStructure (R := B) (M := J))

/-- The summand `δ_i([n](x)) · (-1)ʲ · δ_j([1](γ_n(x)))`, indexed by
`k = (i, j)`, in the expansion of `δ_r([n](x) - [1](γ_n(x)))`. -/
def rel2ExpansionTerm (_r : ℕ) (x : I) {n : ℕ} (hn : n ≠ 0)
    (k : ℕ × ℕ) : Γ :=
  P.dividedPowers.dpow k.1
      (DividedPowerAlgebra.dp B n
        (⟨algebraMap A B x,
          hIJ (Ideal.mem_map_of_mem (algebraMap A B) x.2)⟩ : J)) *
    ((-1 : Γ) ^ k.2 *
      P.dividedPowers.dpow k.2
        (DividedPowerAlgebra.embed B J
          ⟨algebraMap A B (hI.dpow n x),
            algebraMap_dpow_mem hI J hIJ x hn⟩))

/-- The binomial expansion of `δ_r([n](x) - [1](γ_n(x)))`. -/
theorem rel2_dpow_expansion (r : ℕ) (x : I) {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) =
      (Finset.antidiagonal r).sum
        (rel2ExpansionTerm hI J hIJ P r x hn) := by
  unfold rel2Generator rel2ExpansionTerm
  exact dpow_sub_expansion J P
    (r := r)
    (a := DividedPowerAlgebra.dp B n
      (⟨algebraMap A B x,
        hIJ (Ideal.mem_map_of_mem (algebraMap A B) x.2)⟩ : J))
    (b := DividedPowerAlgebra.embed B J
      ⟨algebraMap A B (hI.dpow n x),
        algebraMap_dpow_mem hI J hIJ x hn⟩)
    (rel2Left_mem_positive J hIJ hn)
    (rel2Right_mem_positive hI J hIJ hn)

/--
If every summand of the expansion of `δ_r(g)` lies in `J₂`, then `δ_r(g) ∈ J₂`.
-/
theorem rel2_dpow_mem_of_two_le_of_termwise
    {r : ℕ} (_hr : 2 ≤ r) (x : I) {n : ℕ} (hn : n ≠ 0)
    (hterm : ∀ k ∈ Finset.antidiagonal r,
      rel2ExpansionTerm hI J hIJ P r x hn k ∈ j2 hI J hIJ) :
    P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈
      j2 hI J hIJ := by
  rw [rel2_dpow_expansion hI J hIJ P r x hn]
  exact (j2 hI J hIJ).sum_mem hterm

/-- If the expansion of `δ_r(g)` lies in `J₂`, then `δ_r(g) ∈ J₂`. -/
theorem rel2_dpow_mem_of_two_le_of_expansion
    {r : ℕ} (_hr : 2 ≤ r) (x : I) {n : ℕ} (hn : n ≠ 0)
    (hexp : (Finset.antidiagonal r).sum
        (rel2ExpansionTerm hI J hIJ P r x hn) ∈ j2 hI J hIJ) :
    P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈
      j2 hI J hIJ := by
  rw [rel2_dpow_expansion hI J hIJ P r x hn]
  exact hexp

/--
The statement that, for every `r ≥ 2` and every generator `g` of `J₂`, each
summand of the expansion of `δ_r(g)` lies in `J₂`. The membership `δ_1(g) ∈ J₂`
holds unconditionally (`rel2_dpow_one_mem_j2`).
-/
structure Rel2HigherExpansionData where
  term_mem : ∀ {r : ℕ}, 2 ≤ r → ∀ (x : I) {n : ℕ} (hn : n ≠ 0),
    ∀ k ∈ Finset.antidiagonal r,
      rel2ExpansionTerm hI J hIJ P r x hn k ∈ j2 hI J hIJ

namespace Rel2HigherExpansionData

variable (D : Rel2HigherExpansionData hI J hIJ P)

theorem rel2_dpow_mem_of_two_le
    (D : Rel2HigherExpansionData hI J hIJ P)
    {r : ℕ} (hr : 2 ≤ r) (x : I) {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈
      j2 hI J hIJ :=
  rel2_dpow_mem_of_two_le_of_termwise hI J hIJ P hr x hn
    (D.term_mem hr x hn)

theorem toRel2HigherStabilityData
    (D : Rel2HigherExpansionData hI J hIJ P) :
    Rel2HigherStabilityData hI J hIJ P where
  rel2_dpow_mem_of_two_le := by
    intro r hr x n hn
    exact Rel2HigherExpansionData.rel2_dpow_mem_of_two_le
      (hI := hI) (J := J) (hIJ := hIJ) (P := P) D hr x hn

theorem toRel2GeneratorStabilityData
    (D : Rel2HigherExpansionData hI J hIJ P) :
    Rel2GeneratorStabilityData hI J hIJ P :=
  Rel2HigherStabilityData.toRel2GeneratorStabilityData
    (hI := hI) (J := J) (hIJ := hIJ) (P := P)
    (D.toRel2HigherStabilityData)

theorem toJ12CompatibilityData
    (D : Rel2HigherExpansionData hI J hIJ P)
    (hintersection :
      j12 hI J hIJ ⊓ positiveIdeal (R := B) (M := J) =
        (j1 J ⊓ positiveIdeal (R := B) (M := J)) + j2 hI J hIJ)
    (hproduct :
      j1 J ⊓ positiveIdeal (R := B) (M := J) =
        positiveIdeal (R := B) (M := J) • j1 J) :
    J12CompatibilityData hI J hIJ P :=
  Rel2GeneratorStabilityData.toJ12CompatibilityData
    (hI := hI) (J := J) (hIJ := hIJ) (P := P)
    (D := D.toRel2GeneratorStabilityData)
    hintersection hproduct

end Rel2HigherExpansionData

/-- The case `r = 2`: `δ_2(g) ∈ J₂` if and only if the sum of the three summands
of its expansion lies in `J₂`. -/
theorem rel2_dpow_two_mem_iff_expansion_mem
    (x : I) {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow 2 (rel2Generator hI J hIJ x hn) ∈ j2 hI J hIJ ↔
      (Finset.antidiagonal 2).sum
          (rel2ExpansionTerm hI J hIJ P 2 x hn) ∈ j2 hI J hIJ := by
  rw [rel2_dpow_expansion hI J hIJ P 2 x hn]

/-- Given a `Rel2HigherExpansionData`, `δ_r(g) ∈ J₂` for every `r > 0`
and every generator `g` of `J₂`. -/
theorem rel2_dpow_mem_of_ne_zero_of_data
    (D : Rel2HigherExpansionData hI J hIJ P)
    {r : ℕ} (hr : r ≠ 0) (x : I) {n : ℕ} (hn : n ≠ 0) :
    P.dividedPowers.dpow r (rel2Generator hI J hIJ x hn) ∈ j2 hI J hIJ := by
  by_cases hr1 : r = 1
  · subst r
    exact rel2_dpow_one_mem_j2 (hI := hI) (J := J) (hIJ := hIJ) (P := P) hn
  · exact Rel2HigherExpansionData.rel2_dpow_mem_of_two_le
      (hI := hI) (J := J) (hIJ := hIJ) (P := P) D (by omega) x hn

end J12HigherStability

end FreeConstruction
end Envelope
end AffineCrystalline
