/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.PDDescent
import AffineCrystalline.DeRham.RiouDegreeOne

/-!
# PD stability: generating families and the degree-one computation

Let `δ` be a divided-power structure on an ideal `J ⊆ B`. The `B`-submodule
`pdRelations δ ⊆ Ω[B⁄A]` is spanned by the family `pdRelationFamily δ` of
one-forms `d (δ.dpow n x) - δ.dpow (n - 1) x • d x`. In degree `n`, the wedges
`m₁ ∧ ⋯ ∧ mₙ` with one factor in this family form the family
`pdRelationExteriorFamily δ n`, which is contained in the kernel
`pdRelationPower δ n` of the PD quotient map.

We show that the stability condition `PDRelationStable` may be checked on any
families spanning these kernels, and verify by a direct computation that the
degree-one differential `RiouDegreeOne.degreeOneDifferential` sends every
defining PD relation into the kernel of the quotient map in degree two.

The corresponding statement for the de Rham differential in all degrees is
`pdQuotientRelationStable`.

## Main definitions

* `pdRelationFamily δ`: the defining generators of `pdRelations δ`.
* `pdRelationExteriorFamily δ n`: wedges with one factor in
  `pdRelationFamily δ`.

## Main results

* `pdRelationExteriorFamily_span_le`: the `A`-span of
  `pdRelationExteriorFamily δ n` lies in `pdRelationPower δ n`.
* `pdRelationStable_of_span_le`, `pdRelationStable_of_pdRelationExteriorFamily`:
  PD stability can be checked on spanning families.
* `pdRelationGenerator_degreeOne_map_eq_zero`: the degree-one computation.

## References

* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-! ## The defining PD relation family

By definition, `pdRelations δ` is the `B`-span of the family
`pdRelationFamily δ` below. After passing to exterior powers, the relevant
relation modules are only `A`-submodules, so the stability statements are
`A`-linear.
-/

/-- The defining generators `d (δ.dpow n x) - δ.dpow (n - 1) x • d x`
(`n ≥ 1`, `x ∈ J`) of `pdRelations δ`. -/
def pdRelationFamily : Set (Ω[B⁄A]) :=
  {ω | ∃ (n : ℕ) (_ : 1 ≤ n) (x : B) (_ : x ∈ J),
    ω = KaehlerDifferential.D A B (δ.dpow n x)
      - δ.dpow (n - 1) x • KaehlerDifferential.D A B x}

/-- `pdRelations δ` is the `B`-span of `pdRelationFamily δ`. -/
theorem pdRelations_eq_span_pdRelationFamily :
    pdRelations (A := A) δ = Submodule.span B (pdRelationFamily (A := A) (B := B) δ) := by
  rfl

/-- The defining generators lie in `pdRelations δ`. -/
theorem pdRelationFamily_subset_pdRelations :
    pdRelationFamily (A := A) (B := B) δ ⊆ pdRelations (A := A) δ := by
  rw [pdRelations_eq_span_pdRelationFamily (A := A) (B := B) δ]
  exact Submodule.subset_span

/-! ## Exterior generators of the relations -/

/-- The wedges in `⋀[B]^n Ω[B⁄A]` having one factor equal to a defining PD
relation. They lie in `pdRelationPower δ n`
(`pdRelationExteriorFamily_subset_pdRelationPower`). -/
def pdRelationExteriorFamily (n : ℕ) :
    Set (OrdinaryTerm (A := A) (B := B) n) :=
  {ω | ∃ (i : Fin n) (m : Fin n → Ω[B⁄A]) (r : ℕ) (_ : 1 ≤ r)
      (x : B) (_ : x ∈ J),
      ω = exteriorPower.ιMulti B n
        (Function.update m i (pdRelationGenerator δ r x))}

/-- Every member of `pdRelationExteriorFamily δ n` vanishes in
`⋀[B]^n (PDKaehler δ)`. -/
theorem pdRelationExteriorFamily_subset_pdRelationPower (n : ℕ) :
    pdRelationExteriorFamily (A := A) (B := B) δ n ⊆
      pdRelationPower (A := A) (B := B) δ n := by
  rintro ω ⟨i, m, r, hr, x, hx, rfl⟩
  change pdTermMap (A := A) (B := B) δ n
      (exteriorPower.ιMulti B n
        (Function.update m i (pdRelationGenerator δ r x))) = 0
  rw [pdTermMap, LinearMap.restrictScalars_apply, pdTermMapB,
    exteriorPower.map_apply_ιMulti, Function.comp_update,
    mkQ_pdRelationGenerator_eq_zero (A := A) (B := B) δ r hr x hx]
  exact (exteriorPower.ιMulti B n).toMultilinearMap.map_update_zero _ i

/-- The `A`-span of `pdRelationExteriorFamily δ n` lies in
`pdRelationPower δ n`. -/
theorem pdRelationExteriorFamily_span_le (n : ℕ) :
    Submodule.span A (pdRelationExteriorFamily (A := A) (B := B) δ n) ≤
      pdRelationPower (A := A) (B := B) δ n := by
  rw [Submodule.span_le]
  exact pdRelationExteriorFamily_subset_pdRelationPower (A := A) (B := B) δ n

/-- PD stability can be checked on generators: if each `pdRelationPower δ n`
lies in the `A`-span of `generators n` and `pdTermMap δ (n + 1) ∘ d n` kills
`generators n`, then `d` is PD-stable. -/
theorem pdRelationStable_of_span_le
    (generators : ∀ n : ℕ, Set (OrdinaryTerm (A := A) (B := B) n))
    (hspan : ∀ n : ℕ,
      pdRelationPower (A := A) (B := B) δ n ≤
        Submodule.span A (generators n))
    (d : ∀ n : ℕ, OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (hkill : ∀ (n : ℕ) (ω : OrdinaryTerm (A := A) (B := B) n),
      ω ∈ generators n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d n) ω = 0) :
    PDRelationStable (A := A) (B := B) δ d := by
  intro n
  exact (hspan n).trans <| Submodule.span_le.2 fun ω hω ↦ hkill n ω hω

/-! ## Specialisation to `pdRelationExteriorFamily` -/

/-- The case of `pdRelationStable_of_span_le` for the families
`pdRelationExteriorFamily δ n`: if they span the kernels `pdRelationPower δ n`,
it suffices to check that `pdTermMap δ (n + 1) ∘ d n` kills them. -/
theorem pdRelationStable_of_pdRelationExteriorFamily
    (hspan : ∀ n : ℕ,
      pdRelationPower (A := A) (B := B) δ n ≤
        Submodule.span A (pdRelationExteriorFamily (A := A) (B := B) δ n))
    (d : ∀ n : ℕ, OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (hkill : ∀ (n : ℕ) (ω : OrdinaryTerm (A := A) (B := B) n),
      ω ∈ pdRelationExteriorFamily (A := A) (B := B) δ n →
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d n) ω = 0) :
    PDRelationStable (A := A) (B := B) δ d :=
  pdRelationStable_of_span_le (A := A) (B := B) δ
    (pdRelationExteriorFamily (A := A) (B := B) δ) hspan d hkill

/-! ## Stability in degree one -/

/-- The image of `a ∧ b` in `⋀[B]^2 (PDKaehler δ)` is the wedge of the classes of `a`
and `b`. -/
theorem pdTermMap_wedge (a b : Ω[B⁄A]) :
    pdTermMap (A := A) (B := B) δ 2 (RiouDegreeOne.wedge (A := A) (B := B) a b) =
      exteriorPower.ιMulti B 2
        ![(pdRelations (A := A) δ).mkQ a, (pdRelations (A := A) δ).mkQ b] := by
  rw [pdTermMap, LinearMap.restrictScalars_apply, pdTermMapB, RiouDegreeOne.wedge,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Modulo the PD relations, the differential of `δ.dpow m x` is a multiple of `d x`. -/
theorem exists_pdD_dpow_eq_smul (m : ℕ) {x : B} (hx : x ∈ J) :
    ∃ c : B, pdD (A := A) δ (δ.dpow m x) = c • pdD δ x := by
  cases m with
  | zero =>
    refine ⟨0, ?_⟩
    rw [δ.dpow_zero hx, zero_smul, pdD_apply, Derivation.map_one_eq_zero, map_zero]
  | succ m =>
    refine ⟨δ.dpow m x, ?_⟩
    simpa only [Nat.add_sub_cancel] using (pdD_isPDDerivation δ).dpow (m + 1) (by omega) x hx

/-- For `x ∈ J`, one has `d (δ.dpow m x) ∧ d x = 0` in `⋀[B]^2 (PDKaehler δ)`, since the
class of `d (δ.dpow m x)` is a multiple of `d x` (`exists_pdD_dpow_eq_smul`). -/
theorem ιMulti_pdD_dpow_pdD_eq_zero (m : ℕ) {x : B} (hx : x ∈ J) :
    exteriorPower.ιMulti B 2 ![pdD (A := A) δ (δ.dpow m x), pdD (A := A) δ x] = 0 := by
  obtain ⟨c, hc⟩ := exists_pdD_dpow_eq_smul (A := A) δ m hx
  have h : ![c • pdD (A := A) δ x, pdD δ x] =
      Function.update ![pdD δ x, pdD δ x] 0 (c • pdD (A := A) δ x) := by
    funext i
    fin_cases i <;> rfl
  rw [hc, h, AlternatingMap.map_update_smul, (exteriorPower.ιMulti B 2).map_eq_zero_of_eq _
    (i := 0) (j := 1) (by simp) (by decide), smul_zero]

/-- The degree-one differential sends each defining PD relation into the kernel
of `pdTermMap δ 2`. Indeed, the image of
`d (δ.dpow n x) - δ.dpow (n - 1) x • d x` is
`-d (δ.dpow (n - 1) x) ∧ d x`, and modulo `pdRelations δ` one has
`d (δ.dpow (n - 1) x) = δ.dpow (n - 2) x • d x` for `n ≥ 2`, while
`δ.dpow 0 x = 1` for `n = 1`. -/
theorem pdRelationGenerator_degreeOne_map_eq_zero
    (n : ℕ) (_hn : 1 ≤ n) (x : B) (hx : x ∈ J) :
    pdTermMap (A := A) (B := B) δ 2
      (AffineCrystalline.DeRham.RiouDegreeOne.degreeOneDifferential
        (A := A) (B := B)
        ((oneFormsEquiv (A := A) (B := B) Ω[B⁄A]).symm
          (pdRelationGenerator δ n x))) = 0 := by
  rw [RiouDegreeOne.degreeOneDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, pdRelationGenerator, map_sub,
    ← one_smul B (KaehlerDifferential.D A B (δ.dpow n x)),
    RiouDegreeOne.cotangentDifferential_apply, RiouDegreeOne.cotangentDifferential_apply,
    map_sub, pdTermMap_wedge, pdTermMap_wedge, Derivation.map_one_eq_zero, map_zero]
  simp only [← pdD_apply, ιMulti_pdD_dpow_pdD_eq_zero δ (n - 1) hx, sub_zero]
  exact (exteriorPower.ιMulti B 2).map_coord_zero 0 rfl

end AffineCrystalline.DeRham
