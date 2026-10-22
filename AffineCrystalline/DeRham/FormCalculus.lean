/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.DeRham
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Calculus of divided power differential forms

Let `(B, J, δ)` be a divided power `A`-algebra, and write `Ω^m = ⋀^m_B Ω_{B,δ}`
(`PDTerm δ m`), viewed inside the exterior algebra of `Ω_{B,δ}`. This file develops
the basic operations on these forms used to compute with the divided power de Rham
complex `pdDeRhamComplex δ`.

## Main definitions

* `wdg δ v m : Ω^m → Ω^{m+1}`: left exterior multiplication `ω ↦ v ∧ ω` by a
  one-form `v`.
* `ctr δ φ m : Ω^{m+1} → Ω^m`: the interior product with a linear form
  `φ : Ω_{B,δ} → B`, defined as the Clifford contraction for the zero quadratic form.
* `dd δ m : Ω^m → Ω^{m+1}`: the differential of `pdDeRhamComplex δ`, as an
  `A`-linear map.

## Main results

* `pdTerm_induction`: `Ω^m` is spanned over `B` by the forms `dg₁ ∧ ⋯ ∧ dgₘ`.
* `ctr_wdg_zero`, `ctr_wdg_succ`: `ι_φ (v ∧ ω) = φ(v) ω - v ∧ ι_φ ω`.
* `dd_generator`: `d(b · dg₁ ∧ ⋯ ∧ dgₘ) = db ∧ dg₁ ∧ ⋯ ∧ dgₘ`.
* `dd_smul`: the Leibniz rule `d(f ω) = df ∧ ω + f dω`.
* `pdExteriorMap_wdg`: the maps on forms induced by a morphism of divided power
  algebras are compatible with `wdg`.

## References

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

local notation "Ω" => PDKaehler (A := A) δ

/-! ## Spanning -/

/-- `Ω_{B,δ}` is spanned over `B` by the differentials `db`, `b ∈ B`. -/
theorem span_range_pdD : Submodule.span B (Set.range (pdD (A := A) δ)) = (⊤ : Submodule B Ω) := by
  rw [eq_top_iff]
  rintro ω -
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective _ ω
  have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact Submodule.subset_span ⟨b, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- `Ω^n` is spanned over `B` by the forms `dg₁ ∧ ⋯ ∧ dgₙ`. -/
theorem pdTerm_induction {n : ℕ} {P : PDTerm (A := A) δ n → Prop}
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (b : B) x, P x → P (b • x))
    (hgen : ∀ g : Fin n → B, P (exteriorPower.ιMulti B n (pdD (A := A) δ ∘ g)))
    (x : PDTerm (A := A) δ n) : P x := by
  have hspan := exteriorPower.ιMulti_span_of_span B n (PDKaehler (A := A) δ)
    (span_range_pdD (A := A) δ)
  have hx : x ∈ Submodule.span B
      (exteriorPower.ιMulti B n '' {a | Set.range a ⊆ Set.range (pdD (A := A) δ)}) := by
    rw [hspan]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      have : ∀ i, ∃ b, pdD (A := A) δ b = v i := fun i ↦ hv ⟨i, rfl⟩
      choose g hg using this
      have hvg : v = pdD (A := A) δ ∘ g := funext fun i ↦ (hg i).symm
      rw [hvg]
      exact hgen g
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul b x _ hx => exact hsmul b x hx

/-! ## Wedge with a one-form -/

/-- `v ∧ ω` lies in `⋀^{m+1}` for a one-form `v` and `ω ∈ ⋀^m`. -/
theorem mul_mem_exteriorPower (v : Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    ExteriorAlgebra.ι B v * (x : ExteriorAlgebra B Ω) ∈ ⋀[B]^(m + 1) Ω := by
  rw [ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) x.2

/-- Left exterior multiplication `ω ↦ v ∧ ω` by a one-form `v`, as a map
`Ω^m → Ω^{m+1}`. -/
def wdg (v : Ω) (m : ℕ) : PDTerm (A := A) δ m →ₗ[B] PDTerm (A := A) δ (m + 1) where
  toFun x := ⟨ExteriorAlgebra.ι B v * x, mul_mem_exteriorPower δ v x⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' b x := Subtype.ext (by simp)

theorem wdg_coe (v : Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    ((wdg δ v m x : PDTerm (A := A) δ (m + 1)) : ExteriorAlgebra B Ω) =
      ExteriorAlgebra.ι B v * x := rfl

theorem wdg_add_left (v w : Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    wdg δ (v + w) m x = wdg δ v m x + wdg δ w m x :=
  Subtype.ext (by simp [wdg_coe, add_mul])

theorem wdg_smul_left (b : B) (v : Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    wdg δ (b • v) m x = b • wdg δ v m x :=
  Subtype.ext (by simp [wdg_coe])

theorem wdg_zero_left {m : ℕ} (x : PDTerm (A := A) δ m) : wdg δ 0 m x = 0 :=
  Subtype.ext (by simp [wdg_coe])

/-- `v ∧ v ∧ ω = 0`. -/
theorem wdg_wdg_self (v : Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    wdg δ v (m + 1) (wdg δ v m x) = 0 :=
  Subtype.ext (by simp [wdg_coe, ← mul_assoc])

/-- `v ∧ w ∧ ω = -(w ∧ v ∧ ω)`. -/
theorem wdg_comm (v w : Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    wdg δ v (m + 1) (wdg δ w m x) = -wdg δ w (m + 1) (wdg δ v m x) := by
  apply Subtype.ext
  simp only [wdg_coe, NegMemClass.coe_neg, ← mul_assoc]
  rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := B) v w), neg_mul]

/-- `v₀ ∧ v₁ ∧ ⋯ ∧ vₘ = v₀ ∧ (v₁ ∧ ⋯ ∧ vₘ)`. -/
theorem ιMulti_succ_eq_wdg {m : ℕ} (v : Fin (m + 1) → Ω) :
    exteriorPower.ιMulti B (m + 1) v = wdg δ (v 0) m (exteriorPower.ιMulti B m (Fin.tail v)) :=
  Subtype.ext (by
    rw [wdg_coe, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_succ_apply]
    rfl)

/-! ## Interior product -/

/-- Contraction with `φ` maps `⋀^{m+1}` into `⋀^m`. -/
theorem contractLeft_mem (φ : Module.Dual B Ω) :
    ∀ (m : ℕ) (x : ExteriorAlgebra B Ω), x ∈ ⋀[B]^(m + 1) Ω →
      CliffordAlgebra.contractLeft (Q := 0) φ x ∈ ⋀[B]^m Ω := by
  intro m
  induction m with
  | zero =>
      intro x hx
      rw [ExteriorAlgebra.exteriorPower, zero_add, pow_one] at hx
      obtain ⟨v, rfl⟩ := hx
      rw [ExteriorAlgebra.exteriorPower, pow_zero]
      have := CliffordAlgebra.contractLeft_ι (Q := (0 : QuadraticForm B Ω)) (d := φ) v
      rw [this, Submodule.one_eq_range]
      exact ⟨φ v, rfl⟩
  | succ m ih =>
      intro x hx
      rw [ExteriorAlgebra.exteriorPower, pow_succ'] at hx
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
          obtain ⟨v, rfl⟩ := ha
          rw [CliffordAlgebra.contractLeft_ι_mul]
          refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) ?_
          have := ih b hb
          rw [ExteriorAlgebra.exteriorPower, pow_succ']
          exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) this
      | add x hx' y hy' ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy

/-- The interior product `ι_φ : Ω^{m+1} → Ω^m` with a linear form `φ : Ω_{B,δ} → B`. -/
def ctr (φ : Module.Dual B Ω) (m : ℕ) :
    PDTerm (A := A) δ (m + 1) →ₗ[B] PDTerm (A := A) δ m where
  toFun x := ⟨CliffordAlgebra.contractLeft (Q := 0) φ x, contractLeft_mem δ φ m x x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem ctr_coe (φ : Module.Dual B Ω) {m : ℕ} (x : PDTerm (A := A) δ (m + 1)) :
    ((ctr δ φ m x : PDTerm (A := A) δ m) : ExteriorAlgebra B Ω) =
      CliffordAlgebra.contractLeft (Q := 0) φ x := rfl

/-- `ι_φ (v ∧ f) = φ(v) f` for a `0`-form `f`. -/
theorem ctr_wdg_zero (φ : Module.Dual B Ω) (v : Ω) (x : PDTerm (A := A) δ 0) :
    ctr δ φ 0 (wdg δ v 0 x) = φ v • x := by
  apply Subtype.ext
  rw [ctr_coe, wdg_coe, CliffordAlgebra.contractLeft_ι_mul]
  have hx : (x : ExteriorAlgebra B Ω) ∈ (LinearMap.range (ExteriorAlgebra.ι B (M := Ω))) ^ 0 :=
    x.2
  rw [pow_zero, Submodule.one_eq_range] at hx
  obtain ⟨r, hr⟩ := hx
  have h0 : CliffordAlgebra.contractLeft (Q := 0) φ (x : ExteriorAlgebra B Ω) = 0 := by
    rw [← hr]
    exact CliffordAlgebra.contractLeft_algebraMap (Q := (0 : QuadraticForm B Ω)) φ r
  rw [h0, mul_zero, sub_zero]
  rfl

/-- `ι_φ (v ∧ ω) = φ(v) ω - v ∧ ι_φ ω`. -/
theorem ctr_wdg_succ (φ : Module.Dual B Ω) (v : Ω) {m : ℕ} (x : PDTerm (A := A) δ (m + 1)) :
    ctr δ φ (m + 1) (wdg δ v (m + 1) x) = φ v • x - wdg δ v m (ctr δ φ m x) := by
  apply Subtype.ext
  rw [ctr_coe, wdg_coe, CliffordAlgebra.contractLeft_ι_mul]
  rfl

/-! ## The de Rham differential -/

/-- The differential `Ω^m → Ω^{m+1}` of the divided power de Rham complex, as an
`A`-linear map. -/
abbrev dd (m : ℕ) : PDTerm (A := A) δ m →ₗ[A] PDTerm (A := A) δ (m + 1) :=
  ((pdDeRhamComplex (A := A) δ).d m (m + 1)).hom

/-- `d(b · dg₁ ∧ ⋯ ∧ dgₘ) = db ∧ dg₁ ∧ ⋯ ∧ dgₘ`. -/
theorem dd_generator (m : ℕ) (b : B) (g : Fin m → B) :
    dd δ m (b • exteriorPower.ιMulti B m (pdD (A := A) δ ∘ g)) =
      wdg δ (pdD (A := A) δ b) m (exteriorPower.ιMulti B m (pdD (A := A) δ ∘ g)) := by
  refine (pdDeRhamComplex_d_generator (A := A) δ m b g).trans ?_
  rw [ιMulti_succ_eq_wdg]
  rfl

/-- `d1 = 0`. -/
theorem pdD_one : pdD (A := A) δ (1 : B) = 0 := by
  simp

/-- **Leibniz rule** for the divided power de Rham differential:
`d(f ω) = df ∧ ω + f dω`. -/
theorem dd_smul (m : ℕ) (f : B) (x : PDTerm (A := A) δ m) :
    dd δ m (f • x) = wdg δ (pdD (A := A) δ f) m x + f • dd δ m x := by
  revert f
  refine pdTerm_induction δ (P := fun x ↦ ∀ f : B, dd δ m (f • x) = wdg δ (pdD (A := A) δ f) m x +
    f • dd δ m x) ?_ ?_ ?_ ?_ x
  · intro f; simp
  · intro x y hx hy f
    rw [smul_add, map_add, hx, hy, map_add, map_add, smul_add]
    abel
  · intro b x hx f
    rw [smul_smul, hx (f * b), hx b, (pdD_isPDDerivation (A := A) δ).leibniz, wdg_add_left,
      wdg_smul_left, wdg_smul_left, map_smul, smul_add, smul_smul]
    abel
  · intro g f
    have h1 := dd_generator (A := A) δ m f g
    have h2 := dd_generator (A := A) δ m 1 g
    rw [one_smul, pdD_one, wdg_zero_left] at h2
    rw [h1, h2, smul_zero, add_zero]

/-- In degree `0`, `d(f · 1) = df ∧ 1`. -/
theorem wdg_eq_dd_smul_one (f : B) :
    dd δ 0 (f • exteriorPower.ιMulti B 0 (pdD (A := A) δ ∘ Fin.elim0)) =
      wdg δ (pdD (A := A) δ f) 0 (exteriorPower.ιMulti B 0 (pdD (A := A) δ ∘ Fin.elim0)) :=
  dd_generator (A := A) δ 0 f Fin.elim0

/-! ## Compatibility with algebra maps -/

variable {D : Type u} [CommRing D] [Algebra A D] {K : Ideal D} (δ' : DividedPowers K)

/-- For a morphism of divided power algebras `f : B → D`, the induced map on forms
satisfies `f^*(v ∧ ω) = f^* v ∧ f^* ω`. -/
theorem pdExteriorMap_wdg (f : B →ₐ[A] D) (hf : IsDPMorphism δ δ' f.toRingHom) (v : Ω)
    (m : ℕ) (x : PDTerm (A := A) δ m) :
    pdExteriorMap δ δ' f hf (m + 1) (wdg δ v m x) =
      wdg δ' (pdKaehlerMap δ δ' f hf v) m (pdExteriorMap δ δ' f hf m x) := by
  refine pdTerm_induction δ (P := fun x ↦ pdExteriorMap δ δ' f hf (m + 1) (wdg δ v m x) =
      wdg δ' (pdKaehlerMap δ δ' f hf v) m (pdExteriorMap δ δ' f hf m x)) ?_ ?_ ?_ ?_ x
  · simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, map_add]
  · intro b x hx
    rw [map_smul, pdExteriorMap_smul, hx, pdExteriorMap_smul, map_smul]
  · intro g
    have e1 : wdg δ v m (exteriorPower.ιMulti B m (pdD (A := A) δ ∘ g)) =
        exteriorPower.ιMulti B (m + 1) (Fin.cons v (pdD (A := A) δ ∘ g)) := by
      rw [ιMulti_succ_eq_wdg]; rfl
    rw [e1, pdExteriorMap_ιMulti, pdExteriorMap_ιMulti, ιMulti_succ_eq_wdg]
    congr 2

end AffineCrystalline.DeRham
