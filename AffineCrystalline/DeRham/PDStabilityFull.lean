/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.QuotientKernel
import AffineCrystalline.DeRham.RiouFull
import AffineCrystalline.DeRham.PDStability
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Stability of the divided-power relations in all degrees

Let `δ` be a divided-power structure on an ideal `J ⊆ B`. We prove that the de
Rham differential `DeRhamComplex.d` descends to the divided-power terms
`⋀[B]^n (PDKaehler δ)`: in every degree, it maps the kernel of the quotient map
`⋀[B]^n Ω[B⁄A] → ⋀[B]^n (PDKaehler δ)` into the kernel in the next degree
(`pdQuotientRelationStable`). This is the input for the PD de Rham complex
`pdDeRhamComplex`, obtained through `deRhamComplexOfQuotient`.

The proof has two steps.

1. The kernel is spanned over `A` by the Riou generators
   `b₀ • (db₁ ∧ ⋯ ∧ ρ ∧ ⋯ ∧ dbₙ)` in which one factor is a defining PD relation
   `ρ = d (δ.dpow r x) - δ.dpow (r - 1) x • d x` (the family
   `pdRiouRelationFamily`; see `quotientTermMap_ker_le_pdRiouSpan`). Starting
   from the description of the kernel by wedges having one factor in
   `pdRelations δ` (`quotientTermMap_ker`), one uses that the exact
   differentials `db` span `Ω[B⁄A]` over `B`, and that the `A`-span of the
   family is stable under multiplication by `B`.
2. On each such generator, Riou's formula
   `d (b₀ db₁ ∧ ⋯ ∧ dbₙ) = db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ` and the identity
   `d (δ.dpow r x) = δ.dpow (r - 1) x • d x` modulo `pdRelations δ` show that
   the image of the generator in `⋀[B]^(n + 1) (PDKaehler δ)` vanishes
   (`pdTermMap_comp_d_pdRelationGenerator_eq_zero`).

## Main definitions

* `pdRiouRelationFamily δ n`: the Riou generators containing one defining PD
  relation.

## Main results

* `DeRhamComplex.d_sourceGenerator`: Riou's generator formula for
  `DeRhamComplex.d`.
* `pdTermMap_comp_d_pdRelationGenerator_eq_zero`: the de Rham differential kills the
  members of `pdRiouRelationFamily δ n` modulo the PD relations.
* `quotientTermMap_ker_le_pdRiouSpan`: these members span the kernel of the PD
  quotient map.
* `pdQuotientRelationStable`: the divided-power relations are stable under the
  de Rham differential in every degree.

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham

open AffineCrystalline.DeRham.RiouPresentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-! ## Riou generators containing a PD relation -/

/-- Riou's generator formula `d (b₀ dg₀ ∧ ⋯ ∧ dgₙ₋₁) = db₀ ∧ dg₀ ∧ ⋯ ∧ dgₙ₋₁`
for the de Rham differential. -/
theorem DeRhamComplex.d_sourceGenerator (n : ℕ) (b₀ : B) (g : Fin n → B) :
    DeRhamComplex.d A B n (sourceGenerator (A := A) (B := B) n b₀ g) =
      targetGenerator (A := A) (B := B) n b₀ g := by
  change DeRhamComplex.d A B n
      (b₀ • exteriorPower.ιMulti B n (KaehlerDifferential.D A B ∘ g)) =
    exteriorPower.ιMulti B (n + 1)
      (KaehlerDifferential.D A B ∘ finInsert b₀ g)
  rw [← DeRhamComplex.presentationDifferentialsDown_var A B b₀ g,
    DeRhamComplex.d_var]
  rw [DeRhamComplex.presentationDifferentialsDown_var, one_smul]
  rfl

private theorem update_comp_differential (n : ℕ) (g : Fin n → B)
    (i : Fin n) (y : B) :
    Function.update (KaehlerDifferential.D A B ∘ g) i
        (KaehlerDifferential.D A B y) =
      KaehlerDifferential.D A B ∘ Function.update g i y := by
  funext j
  by_cases hji : j = i
  · subst j; simp
  · simp [hji]

omit [CommRing B] in
private theorem comp_finInsert_update {M : Type*} (f : B → M) (b₀ : B) {n : ℕ}
    (g : Fin n → B) (i : Fin n) (y : B) :
    f ∘ finInsert b₀ (Function.update g i y) =
      Function.update (f ∘ finInsert b₀ g) i.succ (f y) := by
  funext j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
  · by_cases hji : j = i
    · subst j; simp
    · simp [hji]

omit [CommRing B] in
private theorem comp_finInsert_eq_update_zero {M : Type*} (f : B → M) (b b₀ : B) {n : ℕ}
    (g : Fin n → B) :
    f ∘ finInsert b g = Function.update (f ∘ finInsert b₀ g) 0 (f b) := by
  funext j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · simp
  · simp

/-- The image in the PD de Rham term of `d (b₀ dg₀ ∧ ⋯ ∧ dgₙ₋₁)` is the wedge of the
classes of `db₀, dg₀, …, dgₙ₋₁` in `PDKaehler δ`. -/
theorem pdTermMap_d_smul_ιMulti (n : ℕ) (b₀ : B) (g : Fin n → B) :
    pdTermMap (A := A) (B := B) δ (n + 1) (DeRhamComplex.d A B n
        (b₀ • exteriorPower.ιMulti B n (KaehlerDifferential.D A B ∘ g))) =
      exteriorPower.ιMulti B (n + 1) (pdD δ ∘ finInsert b₀ g) := by
  have h := DeRhamComplex.d_sourceGenerator (A := A) n b₀ g
  unfold sourceGenerator targetGenerator at h
  rw [h]
  simp only [pdTermMap, LinearMap.restrictScalars_apply, pdTermMapB,
    exteriorPower.map_apply_ιMulti]
  rfl

/-- The de Rham differential maps a Riou generator having one defining PD
relation as a factor to zero in the next PD de Rham term. -/
theorem pdTermMap_comp_d_pdRelationGenerator_eq_zero
    (n : ℕ) (i : Fin n) (g : Fin n → B) (b₀ : B)
    (r : ℕ) (hr : 1 ≤ r) (x : B) (hx : x ∈ J) :
    (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ
      DeRhamComplex.d A B n)
      (b₀ • exteriorPower.ιMulti B n
        (Function.update (KaehlerDifferential.D A B ∘ g) i
          (pdRelationGenerator δ r x))) = 0 := by
  obtain ⟨c, hc⟩ := exists_pdD_dpow_eq_smul (A := A) δ (r - 1) hx
  set u := Function.update (pdD (A := A) δ ∘ finInsert b₀ g) i.succ (pdD δ x) with hu
  have hu₀ : Function.update u 0 (pdD δ b₀) = u := by
    rw [Function.update_eq_self_iff, hu, Function.update_of_ne (Fin.succ_ne_zero i).symm]
    rfl
  have hvanish : exteriorPower.ιMulti B (n + 1) (Function.update u 0 (pdD δ x)) = 0 :=
    (exteriorPower.ιMulti B (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
      (by simp [u]) (Fin.succ_ne_zero i).symm
  rw [LinearMap.comp_apply, pdRelationGenerator, AlternatingMap.map_update_sub,
    AlternatingMap.map_update_smul, smul_sub, smul_smul, update_comp_differential,
    update_comp_differential, map_sub, map_sub, pdTermMap_d_smul_ιMulti,
    pdTermMap_d_smul_ιMulti,
    comp_finInsert_eq_update_zero (pdD (A := A) δ) (b₀ * δ.dpow (r - 1) x) b₀,
    comp_finInsert_update, comp_finInsert_update, (pdD_isPDDerivation δ).dpow r hr x hx,
    AlternatingMap.map_update_smul, ← hu, (pdD_isPDDerivation δ).leibniz, hc,
    AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, AlternatingMap.map_update_smul, hvanish, hu₀]
  simp only [smul_zero, zero_add, sub_self]

/-! ## Generators of the kernel -/

/-- The Riou generators `b₀ • (dg₀ ∧ ⋯ ∧ ρ ∧ ⋯ ∧ dgₙ₋₁)` in which one factor is a
defining PD relation `ρ`. Including the leading coefficient `b₀` makes the
`A`-span of the family stable under multiplication by `B`. -/
def pdRiouRelationFamily (n : ℕ) :
    Set (OrdinaryTerm (A := A) (B := B) n) :=
  {ω | ∃ (i : Fin n) (g : Fin n → B) (b₀ : B)
      (r : ℕ) (_ : 1 ≤ r) (x : B) (_ : x ∈ J),
    ω = b₀ • exteriorPower.ιMulti B n
      (Function.update (KaehlerDifferential.D A B ∘ g) i
        (pdRelationGenerator δ r x))}

private theorem pdRiouRelationFamily_smul
    (n : ℕ) (c : B) {w : OrdinaryTerm (A := A) (B := B) n}
    (hw : w ∈ pdRiouRelationFamily (A := A) (B := B) δ n) :
    c • w ∈ pdRiouRelationFamily (A := A) (B := B) δ n := by
  obtain ⟨i, g, b₀, r, hr, x, hx, rfl⟩ := hw
  refine ⟨i, g, c * b₀, r, hr, x, hx, ?_⟩
  rw [mul_smul]

private theorem pdRiouSpanA_smul
    (n : ℕ) (c : B) {w : OrdinaryTerm (A := A) (B := B) n}
    (hw : w ∈ Submodule.span A
      (pdRiouRelationFamily (A := A) (B := B) δ n)) :
    c • w ∈ Submodule.span A
      (pdRiouRelationFamily (A := A) (B := B) δ n) := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (pdRiouRelationFamily_smul δ n c hw)
  | zero => simp only [smul_zero, Submodule.zero_mem]
  | add x y _ _ hx hy => simpa only [smul_add] using add_mem hx hy
  | smul a x _ hx =>
    rw [smul_comm c a]
    exact Submodule.smul_mem _ a hx

/-- The `B`-span of `pdRiouRelationFamily δ n` is contained in (hence equal to)
its `A`-span. -/
private theorem pdRiouSpanB_le_spanA (n : ℕ)
    {w : OrdinaryTerm (A := A) (B := B) n}
    (hw : w ∈ Submodule.span B
      (pdRiouRelationFamily (A := A) (B := B) δ n)) :
    w ∈ Submodule.span A
      (pdRiouRelationFamily (A := A) (B := B) δ n) := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span hw
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact pdRiouSpanA_smul δ n c hx

private theorem exactDifferentials_span :
    Submodule.span B (Set.range (KaehlerDifferential.D A B)) = ⊤ :=
  KaehlerDifferential.span_range_derivation A B

/-- The multilinear map `(m₁, …, mₙ) ↦ m₁ ∧ ⋯ ∧ mₙ` followed by the quotient by
the `B`-span of `pdRiouRelationFamily δ n`. -/
private noncomputable def relationTestMap (n : ℕ) :
    MultilinearMap B (fun _ : Fin n ↦ Ω[B⁄A])
      (OrdinaryTerm (A := A) (B := B) n ⧸
        Submodule.span B (pdRiouRelationFamily (A := A) (B := B) δ n)) :=
  LinearMap.compMultilinearMap
    (Submodule.mkQ (Submodule.span B
      (pdRiouRelationFamily (A := A) (B := B) δ n)))
    (exteriorPower.ιMulti B n).toMultilinearMap

/-- Inserting a defining PD relation in slot `i` makes `relationTestMap`
vanish; since exact differentials span `Ω[B⁄A]`, it suffices to test on them. -/
private theorem relationTestMap_curry_generator_zero
    {n : ℕ} (i : Fin (n + 1)) (r : ℕ) (hr : 1 ≤ r) (x : B) (hx : x ∈ J) :
    (relationTestMap (A := A) (B := B) δ (n + 1)).curryMid i
      (pdRelationGenerator δ r x) = 0 := by
  apply MultilinearMap.ext_of_span_eq_top
    (g := fun (_ : Fin n) (b : B) ↦ KaehlerDifferential.D A B b)
  · intro j
    exact exactDifferentials_span (A := A) (B := B)
  · intro g
    apply (Submodule.Quotient.mk_eq_zero _).2
    apply Submodule.subset_span
    let g' : Fin (n + 1) → B := i.insertNth 0 g
    refine ⟨i, g', 1, r, hr, x, hx, ?_⟩
    change exteriorPower.ιMulti B (n + 1)
        (i.insertNth (pdRelationGenerator δ r x)
          (KaehlerDifferential.D A B ∘ g)) =
      (1 : B) • exteriorPower.ιMulti B (n + 1)
        (Function.update (KaehlerDifferential.D A B ∘ g') i
          (pdRelationGenerator δ r x))
    rw [one_smul]
    congr 1
    funext j
    cases j using Fin.succAboveCases i with
    | x => simp [g']
    | p j => simp [g']

/-- Inserting any element of `pdRelations δ` in slot `i` makes
`relationTestMap` vanish. -/
private theorem relationTestMap_curry_mem_zero
    {n : ℕ} (i : Fin (n + 1)) (w : Ω[B⁄A])
    (hw : w ∈ pdRelations (A := A) δ) :
    (relationTestMap (A := A) (B := B) δ (n + 1)).curryMid i w = 0 := by
  rw [pdRelations_eq_span_pdRelationFamily (A := A) (B := B) δ] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hw
    exact relationTestMap_curry_generator_zero δ i r hr x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- Every wedge with one factor in `pdRelations δ` lies in the `B`-span of
`pdRiouRelationFamily δ n`. -/
private theorem exteriorRelationFamily_le_pdRiouSpanB (n : ℕ) :
    exteriorQuotientRelationFamily (pdRelations (A := A) δ) n ⊆
      Submodule.span B (pdRiouRelationFamily (A := A) (B := B) δ n) := by
  rintro w ⟨i, m, hmi, rfl⟩
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hz := DFunLike.congr_fun (relationTestMap_curry_mem_zero δ i (m i) hmi) (i.removeNth m)
    have hz' :
        (Submodule.span B
          (pdRiouRelationFamily (A := A) (B := B) δ (n + 1))).mkQ
          (exteriorPower.ιMulti B (n + 1) m) = 0 := by
      simpa [relationTestMap] using hz
    exact (Submodule.Quotient.mk_eq_zero _).1 hz'

/-- The kernel of `⋀[B]^n Ω[B⁄A] → ⋀[B]^n (PDKaehler δ)` is contained in the
`A`-span of the Riou generators containing one defining PD relation. -/
theorem quotientTermMap_ker_le_pdRiouSpan (n : ℕ) :
    LinearMap.ker (quotientTermMap (A := A)
      (pdRelations (A := A) δ) n) ≤
      Submodule.span A (pdRiouRelationFamily (A := A) (B := B) δ n) := by
  rw [quotientTermMap_ker (A := A) (B := B)]
  intro w hw
  exact pdRiouSpanB_le_spanA δ n
    (Submodule.span_le.2 (exteriorRelationFamily_le_pdRiouSpanB δ n) hw)

/-- The divided-power relations are stable under the de Rham differential in
every degree, so that it descends to the PD de Rham complex. -/
theorem pdQuotientRelationStable :
    QuotientRelationStable (A := A) (B := B) (pdRelations (A := A) δ) := by
  intro n
  refine (quotientTermMap_ker_le_pdRiouSpan δ n).trans ?_
  apply Submodule.span_le.2
  rintro w ⟨i, g, b₀, r, hr, x, hx, rfl⟩
  exact pdTermMap_comp_d_pdRelationGenerator_eq_zero δ n i g b₀ r hr x hx

end AffineCrystalline.DeRham
