/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.FormCalculus

/-!
# The divided power Poincaré lemma in one variable

Let `(B, J, δ)` be a divided power `A`-algebra equipped with

* an idempotent endomorphism `ε` of divided power `A`-algebras ("set `ξ = 0`"),
* an element `ξ ∈ J` with `ε ξ = 0`,
* a divided power derivation `∂ : B → B` with `∂ ξ = 1` and `∂ ∘ ε = 0`,
* the Taylor property: every `y ∈ B` is a finite sum `∑ ξ^[k] ε(c_k)`.

This axiomatizes the situation `B = B₀⟨ξ⟩` with `B₀ = ε(B)`, without assuming that
the divided powers `ξ^[k]` are linearly independent over `B₀`. We prove that the
pullback `ε^*` acts as the identity on the cohomology of the divided power de Rham
complex `Ω^•_{B,δ}`: every cocycle `ω` of degree `m + 1` satisfies
`ω - ε^* ω ∈ d(Ω^m)`, and every cocycle of degree `0` satisfies `ω = ε^* ω`.

The proof follows [Stacks, Tag 07Q8]: write `ω = ∑ ξ^[k] (α_k + dξ ∧ β_k)` with
`α_k`, `β_k` pulled back along `ε`, subtract `d(∑ ξ^[k+1] β_k)`, and show that a
cocycle `∑ ξ^[k] ρ_k` with pulled-back coefficients equals `ρ_0`. The coefficient
`ρ_a` is recovered as `ε^* (ι_∂ ∘ d)^a`, where `ι_∂` is the interior product with the
linear form `Ω_{B,δ} → B` induced by `∂`.

## Main definitions

* `AffineCrystalline.DeRham.OneVariable δ`: the data `(ε, ξ, ∂)` above.
* `AffineCrystalline.DeRham.taylorSubalgebra`: the subalgebra of elements
  `∑ ξ^[k] ε(c_k)`.
* `AffineCrystalline.DeRham.IsBd`: the property of being a coboundary in
  `Ω^•_{B,δ}`.

## Main results

* `OneVariable.cocycle_zero`: a `0`-cocycle `ω` satisfies `ω = ε^* ω`.
* `OneVariable.cocycle_succ`: a cocycle `ω` of degree `m + 1` satisfies
  `ω - ε^* ω = dη` for some `η`.
* `OneVariable.isBd_sub`: in every degree, `ω - ε^* ω` is a coboundary for every
  cocycle `ω`.
* `taylorSubalgebra_dpow_mem`: the Taylor subalgebra is stable under the divided
  powers of elements of `J`.

## References

* [Stacks Project, Tag 07Q8](https://stacks.math.columbia.edu/tag/07Q8)
-/

open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-- Equal divided power morphisms induce equal maps on forms. -/
theorem pdExteriorMap_congr {D : Type u} [CommRing D] [Algebra A D] {K : Ideal D}
    (δ' : DividedPowers K) {f g : B →ₐ[A] D} (h : f = g)
    (hf : IsDPMorphism δ δ' f.toRingHom) (hg : IsDPMorphism δ δ' g.toRingHom) (n : ℕ) :
    pdExteriorMap δ δ' f hf n = pdExteriorMap δ δ' g hg n := by
  subst h; rfl

/-- The data of a divided power algebra in one divided power variable `ξ` over the
subalgebra `ε(B)`, as in the hypotheses of the one-variable Poincaré lemma. -/
structure OneVariable where
  /-- The retraction "set `ξ = 0`". -/
  ε : B →ₐ[A] B
  /-- `ε` is compatible with the divided powers. -/
  hε : IsDPMorphism δ δ ε.toRingHom
  /-- `ε` is idempotent. -/
  idem : ∀ y, ε (ε y) = ε y
  /-- The variable. -/
  ξ : B
  /-- The variable lies in the divided power ideal. -/
  ξ_mem : ξ ∈ J
  /-- `ε` sets the variable to `0`. -/
  ε_ξ : ε ξ = 0
  /-- The derivation `∂ = ∂/∂ξ`. -/
  der : B →ₗ[A] B
  /-- `∂` is a divided power derivation. -/
  hder : IsPDDerivation δ B der
  /-- `∂ ξ = 1`. -/
  der_ξ : der ξ = 1
  /-- `∂` vanishes on the image of `ε`. -/
  der_ε : ∀ y, der (ε y) = 0
  /-- Every element is a finite sum `∑ ξ^[k] ε(c_k)`. -/
  taylor : ∀ y : B, ∃ c : ℕ →₀ B, y = c.sum fun k a ↦ δ.dpow k ξ * ε a

namespace OneVariable

variable {δ} (V : OneVariable (A := A) δ)

local notation "Ω" => PDKaehler (A := A) δ

/-- The divided power `ξ^[k]`. -/
abbrev ξk (k : ℕ) : B := δ.dpow k V.ξ

theorem ξk_zero : V.ξk 0 = 1 := δ.dpow_zero V.ξ_mem

theorem ε_ξk (k : ℕ) : V.ε (V.ξk k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; rw [ξk_zero, map_one]
  · have h := V.hε.dpow_comp (n := k) V.ξ V.ξ_mem
    change δ.dpow k (V.ε V.ξ) = V.ε (δ.dpow k V.ξ) at h
    rw [← h, V.ε_ξ, δ.dpow_eval_zero hk]

theorem ξk_mul (a b : ℕ) : V.ξk a * V.ξk b = (a + b).choose a * V.ξk (a + b) :=
  δ.mul_dpow V.ξ_mem

theorem pdD_ξk_succ (k : ℕ) :
    pdD (A := A) δ (V.ξk (k + 1)) = V.ξk k • pdD (A := A) δ V.ξ := by
  have := (pdD_isPDDerivation (A := A) δ).dpow (k + 1) (by omega) V.ξ V.ξ_mem
  simpa using this

/-- The linear form `Ω_{B,δ} → B` induced by `∂`, i.e. `db ↦ ∂ b`. -/
def φ : Module.Dual B Ω := PDKaehler.lift δ B V.der V.hder

theorem φ_pdD (y : B) : V.φ (pdD (A := A) δ y) = V.der y :=
  LinearMap.congr_fun (PDKaehler.lift_comp δ B V.der V.hder) y

/-- The pullback `ε^*` on `Ω^m`. -/
abbrev εs (m : ℕ) : PDTerm (A := A) δ m →ₗ[A] PDTerm (A := A) δ m :=
  pdExteriorMap δ δ V.ε V.hε m

theorem εs_εs (m : ℕ) (x : PDTerm (A := A) δ m) : V.εs m (V.εs m x) = V.εs m x := by
  have h := LinearMap.congr_fun (pdExteriorMap_comp δ δ δ V.ε V.hε V.ε V.hε m) x
  rw [LinearMap.comp_apply] at h
  rw [h]
  have hεε : V.ε.comp V.ε = V.ε := AlgHom.ext fun y ↦ V.idem y
  exact LinearMap.congr_fun (pdExteriorMap_congr δ δ hεε _ V.hε m) x

theorem εs_smul (m : ℕ) (b : B) (x : PDTerm (A := A) δ m) :
    V.εs m (b • x) = V.ε b • V.εs m x :=
  pdExteriorMap_smul δ δ V.ε V.hε m b x

theorem dd_εs (m : ℕ) (x : PDTerm (A := A) δ m) :
    dd δ m (V.εs m x) = V.εs (m + 1) (dd δ m x) :=
  LinearMap.congr_fun (pdExteriorMap_d_naturality δ δ V.ε V.hε m) x

theorem pdKaehlerMap_ε_pdD (y : B) :
    pdKaehlerMap δ δ V.ε V.hε (pdD (A := A) δ y) = pdD (A := A) δ (V.ε y) :=
  pdKaehlerMap_pdD δ δ V.ε V.hε y

theorem εs_wdg_pdD (y : B) (m : ℕ) (x : PDTerm (A := A) δ m) :
    V.εs (m + 1) (wdg δ (pdD (A := A) δ y) m x) =
      wdg δ (pdD (A := A) δ (V.ε y)) m (V.εs m x) := by
  rw [εs, pdExteriorMap_wdg, pdKaehlerMap_ε_pdD]

theorem ctr_ιMulti_eq_zero {m : ℕ} (w : Fin (m + 1) → Ω) (hw : ∀ i, V.φ (w i) = 0) :
    ctr δ V.φ m (exteriorPower.ιMulti B (m + 1) w) = 0 := by
  induction m with
  | zero =>
      rw [ιMulti_succ_eq_wdg, ctr_wdg_zero, hw, zero_smul]
  | succ m ih =>
      rw [ιMulti_succ_eq_wdg, ctr_wdg_succ, hw, zero_smul, zero_sub,
        ih (Fin.tail w) (fun i ↦ hw _), map_zero, neg_zero]

theorem ctr_εs (m : ℕ) (x : PDTerm (A := A) δ (m + 1)) : ctr δ V.φ m (V.εs (m + 1) x) = 0 := by
  refine pdTerm_induction δ (P := fun x ↦ ctr δ V.φ m (V.εs (m + 1) x) = 0) ?_ ?_ ?_ ?_ x
  · simp
  · intro x y hx hy; rw [map_add, map_add, hx, hy, add_zero]
  · intro b x hx; rw [εs_smul, map_smul, hx, smul_zero]
  · intro g
    rw [εs, pdExteriorMap_ιMulti]
    apply ctr_ιMulti_eq_zero
    intro i
    simp only [Function.comp_apply, pdKaehlerMap_pdD]
    rw [φ_pdD]
    exact V.der_ε _

/-! ## Pulled-back forms -/

/-- The forms pulled back along `ε`, i.e. the image of `ε^*`. -/
abbrev Ω0 (m : ℕ) : Submodule A (PDTerm (A := A) δ m) := LinearMap.range (V.εs m)

theorem εs_of_mem {m : ℕ} {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) : V.εs m x = x := by
  obtain ⟨w, rfl⟩ := hx
  exact V.εs_εs m w

theorem ctr_of_mem {m : ℕ} {x : PDTerm (A := A) δ (m + 1)} (hx : x ∈ V.Ω0 (m + 1)) :
    ctr δ V.φ m x = 0 := by
  obtain ⟨w, rfl⟩ := hx
  exact V.ctr_εs m w

theorem dd_mem {m : ℕ} {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) :
    dd δ m x ∈ V.Ω0 (m + 1) := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨dd δ m w, (V.dd_εs m w).symm⟩

theorem ε_smul_mem {m : ℕ} (c : B) {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) :
    V.ε c • x ∈ V.Ω0 m := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨c • w, V.εs_smul m c w⟩

theorem ctr_wdg_dξ {m : ℕ} {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) :
    ctr δ V.φ m (wdg δ (pdD (A := A) δ V.ξ) m x) = x := by
  cases m with
  | zero => rw [ctr_wdg_zero, φ_pdD, V.der_ξ, one_smul]
  | succ m => rw [ctr_wdg_succ, φ_pdD, V.der_ξ, one_smul, V.ctr_of_mem hx, map_zero, sub_zero]

/-! ## Coefficient extraction -/

/-- The operator `ι_∂ ∘ d` on `Ω^m`. -/
def Λ (m : ℕ) : PDTerm (A := A) δ m →ₗ[A] PDTerm (A := A) δ m :=
  (ctr δ V.φ m).restrictScalars A ∘ₗ dd δ m

theorem Λ_ξk_succ {m : ℕ} (k : ℕ) {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) :
    V.Λ m (V.ξk (k + 1) • x) = V.ξk k • x := by
  simp only [Λ, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [dd_smul, V.pdD_ξk_succ, wdg_smul_left, map_add, map_smul, map_smul,
    V.ctr_wdg_dξ hx, V.ctr_of_mem (V.dd_mem hx), smul_zero, add_zero]

theorem Λ_of_mem {m : ℕ} {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) : V.Λ m x = 0 := by
  simp only [Λ, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  exact V.ctr_of_mem (V.dd_mem hx)

theorem Λ_iterate_ξk {m : ℕ} (a k : ℕ) {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) :
    (V.Λ m)^[a] (V.ξk k • x) = if a ≤ k then V.ξk (k - a) • x else 0 := by
  induction a generalizing k with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      rcases k with _ | k
      · rw [ξk_zero, one_smul, V.Λ_of_mem hx]
        simp [iterate_map_zero]
      · rw [V.Λ_ξk_succ k hx, ih k, Nat.add_sub_add_right]
        simp only [Nat.add_le_add_iff_right]

theorem εs_ξk_smul {m : ℕ} (k : ℕ) {x : PDTerm (A := A) δ m} (hx : x ∈ V.Ω0 m) :
    V.εs m (V.ξk k • x) = if k = 0 then x else 0 := by
  rw [εs_smul, ε_ξk, V.εs_of_mem hx]
  split_ifs <;> simp

/-- Coefficient extraction: if the `ρ_k` are pulled back along `ε`, then
`ρ_a = ε^* ((ι_∂ ∘ d)^a (∑ ξ^[k] ρ_k))`. -/
theorem extract {m : ℕ} (ρ : ℕ →₀ PDTerm (A := A) δ m) (hρ : ∀ k, ρ k ∈ V.Ω0 m) (a : ℕ) :
    V.εs m ((V.Λ m)^[a] (ρ.sum fun k x ↦ V.ξk k • x)) = ρ a := by
  rw [Finsupp.sum, ← Module.End.pow_apply, map_sum, map_sum]
  simp_rw [Module.End.pow_apply, V.Λ_iterate_ξk _ _ (hρ _)]
  rw [Finset.sum_eq_single a]
  · rw [if_pos le_rfl, Nat.sub_self, V.εs_ξk_smul 0 (hρ a), if_pos rfl]
  · intro k _ hk
    split_ifs with h
    · rw [V.εs_ξk_smul _ (hρ k), if_neg (by omega)]
    · exact map_zero _
  · intro ha
    rw [Finsupp.notMem_support_iff.mp ha]
    simp

theorem iterate_Λ_zero {m : ℕ} (b : ℕ) : (V.Λ m)^[b] 0 = 0 := by
  rw [← Module.End.pow_apply, map_zero]

/-- A cocycle `∑ ξ^[k] ρ_k` whose coefficients are pulled back along `ε` is fixed by
`ε^*`. -/
theorem cocycle_pure {m : ℕ} (ρ : ℕ →₀ PDTerm (A := A) δ m) (hρ : ∀ k, ρ k ∈ V.Ω0 m)
    (hY : dd δ m (ρ.sum fun k x ↦ V.ξk k • x) = 0) :
    (ρ.sum fun k x ↦ V.ξk k • x) = V.εs m (ρ.sum fun k x ↦ V.ξk k • x) := by
  set Y := ρ.sum fun k x ↦ V.ξk k • x with hYdef
  have hΛ : V.Λ m Y = 0 := by
    simp only [Λ, LinearMap.comp_apply, hY, map_zero]
  have hzero : ∀ a, 1 ≤ a → ρ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha
    rw [← V.extract ρ hρ (b + 1), Function.iterate_succ_apply, ← hYdef, hΛ, iterate_Λ_zero,
      map_zero]
  have hρs : ρ = Finsupp.single 0 (ρ 0) := by
    ext k
    rcases k with _ | k
    · simp
    · rw [Finsupp.single_apply, if_neg (by omega), hzero _ (by omega)]
  have h0 : V.εs m Y = ρ 0 := V.extract ρ hρ 0
  rw [h0, hYdef, hρs, Finsupp.sum_single_index (by simp), ξk_zero, one_smul]
  simp

/-! ## Decomposition of forms -/

/-- The forms `α + dξ ∧ β` with `α` and `β` pulled back along `ε`. -/
def Z : (m : ℕ) → Submodule A (PDTerm (A := A) δ m)
  | 0 => V.Ω0 0
  | m + 1 => V.Ω0 (m + 1) ⊔ (V.Ω0 m).map ((wdg δ (pdD (A := A) δ V.ξ) m).restrictScalars A)

theorem Ω0_le_Z (m : ℕ) : V.Ω0 m ≤ V.Z m := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact le_sup_left

theorem Z_ε_smul {m : ℕ} (c : B) {z : PDTerm (A := A) δ m} (hz : z ∈ V.Z m) :
    V.ε c • z ∈ V.Z m := by
  cases m with
  | zero => exact V.ε_smul_mem c hz
  | succ m =>
      obtain ⟨α, hα, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨β, hβ, rfl⟩ := hw
      rw [smul_add]
      refine Submodule.add_mem_sup (V.ε_smul_mem c hα) ⟨V.ε c • β, V.ε_smul_mem c hβ, ?_⟩
      simp

theorem Z_wdg_ε {m : ℕ} (c : B) {z : PDTerm (A := A) δ m} (hz : z ∈ V.Z m) :
    wdg δ (pdD (A := A) δ (V.ε c)) m z ∈ V.Z (m + 1) := by
  cases m with
  | zero =>
      obtain ⟨w, rfl⟩ := hz
      exact le_sup_left (a := V.Ω0 1) ⟨wdg δ (pdD (A := A) δ c) 0 w, V.εs_wdg_pdD c 0 w⟩
  | succ m =>
      obtain ⟨α, hα, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨β, hβ, rfl⟩ := hw
      rw [map_add]
      refine Submodule.add_mem_sup ?_ ?_
      · obtain ⟨a, rfl⟩ := hα
        exact ⟨wdg δ (pdD (A := A) δ c) (m + 1) a, V.εs_wdg_pdD c (m + 1) a⟩
      · obtain ⟨b, rfl⟩ := hβ
        refine ⟨-(V.εs (m + 1) (wdg δ (pdD (A := A) δ c) m b)), ?_, ?_⟩
        · exact Submodule.neg_mem _ ⟨_, rfl⟩
        · simp only [LinearMap.restrictScalars_apply, map_neg]
          rw [V.εs_wdg_pdD, wdg_comm, neg_neg]

theorem Z_wdg_ξ {m : ℕ} {z : PDTerm (A := A) δ m} (hz : z ∈ V.Z m) :
    wdg δ (pdD (A := A) δ V.ξ) m z ∈ V.Z (m + 1) := by
  cases m with
  | zero => exact le_sup_right (a := V.Ω0 1) ⟨z, hz, rfl⟩
  | succ m =>
      obtain ⟨α, hα, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨β, hβ, rfl⟩ := hw
      change wdg δ _ (m + 1) (α + wdg δ _ m β) ∈ _
      rw [map_add, wdg_wdg_self, add_zero]
      exact Submodule.mem_sup_right ⟨α, hα, rfl⟩

/-- The `A`-span of the forms `ξ^[k] z` with `z ∈ Z m`. -/
def decomp (m : ℕ) : Submodule A (PDTerm (A := A) δ m) :=
  Submodule.span A {x | ∃ k z, z ∈ V.Z m ∧ x = V.ξk k • z}

theorem ξk_smul_mem_decomp {m : ℕ} (k : ℕ) {z : PDTerm (A := A) δ m} (hz : z ∈ V.Z m) :
    V.ξk k • z ∈ V.decomp m :=
  Submodule.subset_span ⟨k, z, hz, rfl⟩

theorem Z_le_decomp {m : ℕ} {z : PDTerm (A := A) δ m} (hz : z ∈ V.Z m) : z ∈ V.decomp m := by
  have := V.ξk_smul_mem_decomp 0 hz
  rwa [ξk_zero, one_smul] at this

theorem decomp_ξk_smul {m : ℕ} (a : ℕ) {x : PDTerm (A := A) δ m} (hx : x ∈ V.decomp m) :
    V.ξk a • x ∈ V.decomp m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨k, z, hz, rfl⟩ := hy
      rw [smul_smul, ξk_mul, mul_smul, smul_comm, Nat.cast_smul_eq_nsmul]
      exact V.ξk_smul_mem_decomp _ (nsmul_mem hz _)
  | zero => simp
  | add y w _ _ hy hw => rw [smul_add]; exact Submodule.add_mem _ hy hw
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

theorem decomp_ε_smul {m : ℕ} (c : B) {x : PDTerm (A := A) δ m} (hx : x ∈ V.decomp m) :
    V.ε c • x ∈ V.decomp m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨k, z, hz, rfl⟩ := hy
      rw [smul_comm]
      exact V.ξk_smul_mem_decomp _ (V.Z_ε_smul c hz)
  | zero => simp
  | add y w _ _ hy hw => rw [smul_add]; exact Submodule.add_mem _ hy hw
  | smul c' y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c' hy

theorem decomp_smul {m : ℕ} (b : B) {x : PDTerm (A := A) δ m} (hx : x ∈ V.decomp m) :
    b • x ∈ V.decomp m := by
  obtain ⟨c, rfl⟩ := V.taylor b
  rw [Finsupp.sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  rw [mul_smul]
  exact V.decomp_ξk_smul k (V.decomp_ε_smul _ hx)

theorem wdg_sum_left {ι : Type*} (s : Finset ι) (v : ι → Ω) {m : ℕ} (x : PDTerm (A := A) δ m) :
    wdg δ (∑ i ∈ s, v i) m x = ∑ i ∈ s, wdg δ (v i) m x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wdg_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, wdg_add_left, ih, Finset.sum_insert hi]

theorem Z_wdg_mem_decomp {m : ℕ} (y : B) {z : PDTerm (A := A) δ m} (hz : z ∈ V.Z m) :
    wdg δ (pdD (A := A) δ y) m z ∈ V.decomp (m + 1) := by
  obtain ⟨c, rfl⟩ := V.taylor y
  rw [Finsupp.sum, map_sum, wdg_sum_left]
  refine Submodule.sum_mem _ fun a _ ↦ ?_
  rw [(pdD_isPDDerivation (A := A) δ).leibniz, wdg_add_left, wdg_smul_left, wdg_smul_left]
  refine Submodule.add_mem _ (V.decomp_ξk_smul a (V.Z_le_decomp (V.Z_wdg_ε _ hz))) ?_
  refine V.decomp_ε_smul _ ?_
  rcases a with _ | a
  · rw [δ.dpow_zero V.ξ_mem, pdD_one, wdg_zero_left]
    exact Submodule.zero_mem _
  · rw [V.pdD_ξk_succ, wdg_smul_left]
    exact V.decomp_ξk_smul a (V.Z_le_decomp (V.Z_wdg_ξ hz))

theorem decomp_wdg {m : ℕ} (y : B) {x : PDTerm (A := A) δ m} (hx : x ∈ V.decomp m) :
    wdg δ (pdD (A := A) δ y) m x ∈ V.decomp (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨k, z, hz, rfl⟩ := hw
      rw [map_smul]
      exact V.decomp_ξk_smul k (V.Z_wdg_mem_decomp y hz)
  | zero => simp
  | add w w' _ _ hw hw' => rw [map_add]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
      rw [← algebraMap_smul B c w, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ c hw

theorem ιMulti_mem_decomp : ∀ (m : ℕ) (g : Fin m → B),
    exteriorPower.ιMulti B m (pdD (A := A) δ ∘ g) ∈ V.decomp m
  | 0, g => by
      refine V.Z_le_decomp ⟨exteriorPower.ιMulti B 0 (pdD (A := A) δ ∘ g), ?_⟩
      rw [εs, pdExteriorMap_ιMulti]
      congr 1
      funext i
      exact i.elim0
  | m + 1, g => by
      rw [ιMulti_succ_eq_wdg]
      exact V.decomp_wdg (g 0) (ιMulti_mem_decomp m (Fin.tail g))

/-- Every form lies in `decomp`. -/
theorem mem_decomp {m : ℕ} (x : PDTerm (A := A) δ m) : x ∈ V.decomp m :=
  pdTerm_induction δ (Submodule.zero_mem _) (fun _ _ hx hy ↦ Submodule.add_mem _ hx hy)
    (fun b _ hx ↦ V.decomp_smul b hx) (V.ιMulti_mem_decomp m) x

/-- Every element of `decomp` is a finite sum `∑ ξ^[k] z_k` with `z_k ∈ Z`. -/
theorem exists_repr {m : ℕ} {x : PDTerm (A := A) δ m} (hx : x ∈ V.decomp m) :
    ∃ z : ℕ →₀ PDTerm (A := A) δ m, (∀ k, z k ∈ V.Z m) ∧ x = z.sum fun k w ↦ V.ξk k • w := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨k, z, hz, rfl⟩ := hy
      refine ⟨Finsupp.single k z, fun j ↦ ?_, by rw [Finsupp.sum_single_index (by simp)]⟩
      rw [Finsupp.single_apply]
      split_ifs
      · exact hz
      · exact Submodule.zero_mem _
  | zero => exact ⟨0, fun _ ↦ Submodule.zero_mem _, by simp⟩
  | add y w _ _ hy hw =>
      obtain ⟨z₁, hz₁, rfl⟩ := hy
      obtain ⟨z₂, hz₂, rfl⟩ := hw
      refine ⟨z₁ + z₂, fun k ↦ Submodule.add_mem _ (hz₁ k) (hz₂ k), ?_⟩
      rw [Finsupp.sum_add_index' (by simp) (by intros; rw [smul_add])]
  | smul c y _ hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨c • z, fun k ↦ Submodule.smul_mem _ c (hz k), ?_⟩
      rw [Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
      simp_rw [smul_comm c]

/-- `d ∘ d = 0`. -/
theorem dd_dd (m : ℕ) (x : PDTerm (A := A) δ m) : dd δ (m + 1) (dd δ m x) = 0 := by
  have h := (pdDeRhamComplex (A := A) δ).d_comp_d m (m + 1) (m + 2)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

/-- **One-variable divided power Poincaré lemma, degree `0`.** A `0`-cocycle `ω`
satisfies `ω = ε^* ω`. -/
theorem cocycle_zero (ω : PDTerm (A := A) δ 0) (hω : dd δ 0 ω = 0) : ω = V.εs 0 ω := by
  obtain ⟨z, hz, rfl⟩ := V.exists_repr (V.mem_decomp ω)
  exact V.cocycle_pure z hz hω

/-- A form in `Z (m + 1)` is `α + dξ ∧ β` with `α` and `β` pulled back along `ε`. -/
theorem exists_eq_add_wdg_of_mem_Z {m : ℕ} {z : PDTerm (A := A) δ (m + 1)}
    (hz : z ∈ V.Z (m + 1)) :
    ∃ α ∈ V.Ω0 (m + 1), ∃ β ∈ V.Ω0 m, z = α + wdg δ (pdD (A := A) δ V.ξ) m β := by
  obtain ⟨α, hα, w, hw, h⟩ := Submodule.mem_sup.mp hz
  obtain ⟨β, hβ, rfl⟩ := hw
  exact ⟨α, hα, β, hβ, h.symm⟩

/-- The coefficients of `∑ₖ (ξ^[k] αₖ - ξ^[k+1] dβₖ)` are pulled back along `ε` if the
`αₖ` and `βₖ` are. -/
theorem finset_sum_single_sub_single_mem {m : ℕ} (s : Finset ℕ)
    {α : ℕ → PDTerm (A := A) δ (m + 1)} {β : ℕ → PDTerm (A := A) δ m}
    (hα : ∀ k, α k ∈ V.Ω0 (m + 1)) (hβ : ∀ k, β k ∈ V.Ω0 m) (j : ℕ) :
    (∑ k ∈ s, (Finsupp.single k (α k) - Finsupp.single (k + 1) (dd δ m (β k)))) j ∈
      V.Ω0 (m + 1) := by
  rw [Finsupp.finsetSum_apply]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  refine Submodule.sub_mem _ ?_ ?_
  · split_ifs
    · exact hα k
    · exact Submodule.zero_mem _
  · split_ifs
    · exact V.dd_mem (hβ k)
    · exact Submodule.zero_mem _

/-- The form with coefficients `∑ₖ (single k αₖ - single (k + 1) dβₖ)` is
`∑ₖ (ξ^[k] αₖ - ξ^[k+1] dβₖ)`. -/
theorem sum_finset_sum_single_sub_single {m : ℕ} (s : Finset ℕ)
    (α : ℕ → PDTerm (A := A) δ (m + 1)) (β : ℕ → PDTerm (A := A) δ m) :
    ((∑ k ∈ s, (Finsupp.single k (α k) - Finsupp.single (k + 1) (dd δ m (β k)))).sum
        fun k x ↦ V.ξk k • x) =
      ∑ k ∈ s, (V.ξk k • α k - V.ξk (k + 1) • dd δ m (β k)) := by
  rw [← Finsupp.sum_finsetSum_index (fun _ ↦ smul_zero _) (fun _ _ _ ↦ smul_add _ _ _)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finsupp.sum_sub_index (by intros; rw [smul_sub]), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp)]

/-- `d (∑ₖ ξ^[k+1] βₖ) = ∑ₖ (ξ^[k] dξ ∧ βₖ + ξ^[k+1] dβₖ)`. -/
theorem dd_finset_sum_ξk_succ_smul {m : ℕ} (s : Finset ℕ) (β : ℕ → PDTerm (A := A) δ m) :
    dd δ m (∑ k ∈ s, V.ξk (k + 1) • β k) =
      ∑ k ∈ s, (V.ξk k • wdg δ (pdD (A := A) δ V.ξ) m (β k) + V.ξk (k + 1) • dd δ m (β k)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [dd_smul, V.pdD_ξk_succ, wdg_smul_left]

/-- `ε^* (∑ₖ ξ^[k+1] βₖ) = 0` if the `βₖ` are pulled back along `ε`. -/
theorem εs_finset_sum_ξk_succ_smul {m : ℕ} (s : Finset ℕ) {β : ℕ → PDTerm (A := A) δ m}
    (hβ : ∀ k, β k ∈ V.Ω0 m) :
    V.εs m (∑ k ∈ s, V.ξk (k + 1) • β k) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [V.εs_ξk_smul _ (hβ k), if_neg (by omega)]

/-- **One-variable divided power Poincaré lemma, positive degree.** A cocycle `ω` of
degree `m + 1` satisfies `ω - ε^* ω = dη` for some `η`. -/
theorem cocycle_succ {m : ℕ} (ω : PDTerm (A := A) δ (m + 1)) (hω : dd δ (m + 1) ω = 0) :
    ∃ η : PDTerm (A := A) δ m, ω - V.εs (m + 1) ω = dd δ m η := by
  classical
  obtain ⟨z, hz, hωz⟩ := V.exists_repr (V.mem_decomp ω)
  choose α hα β hβ hzk using fun k ↦ V.exists_eq_add_wdg_of_mem_Z (hz k)
  set η : PDTerm (A := A) δ m := ∑ k ∈ z.support, V.ξk (k + 1) • β k with hη
  set ρ : ℕ →₀ PDTerm (A := A) δ (m + 1) :=
    ∑ k ∈ z.support, (Finsupp.single k (α k) - Finsupp.single (k + 1) (dd δ m (β k))) with hρdef
  have hY : ω - dd δ m η = ρ.sum fun k x ↦ V.ξk k • x := by
    rw [hρdef, V.sum_finset_sum_single_sub_single, hη, V.dd_finset_sum_ξk_succ_smul, hωz,
      Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hzk k, smul_add]
    abel
  have hpure := V.cocycle_pure ρ (V.finset_sum_single_sub_single_mem _ hα hβ)
    (by rw [← hY, map_sub, hω, dd_dd, sub_zero])
  refine ⟨η, ?_⟩
  have hεω : V.εs (m + 1) ω = ρ.sum fun k x ↦ V.ξk k • x := by
    have : ω = dd δ m η + ρ.sum fun k x ↦ V.ξk k • x := by rw [← hY]; abel
    rw [this, map_add, ← V.dd_εs, V.εs_finset_sum_ξk_succ_smul _ hβ, map_zero, zero_add,
      ← hpure]
  rw [hεω, ← hY]
  abel

end OneVariable

/-! ## The Taylor subalgebra -/

section Taylor

variable {δ}
variable (ε : B →ₐ[A] B) (hε : IsDPMorphism δ δ ε.toRingHom) (idem : ∀ y, ε (ε y) = ε y)
variable (ξ : B) (ξ_mem : ξ ∈ J) (εξ : ε ξ = 0)

/-- The subalgebra of `B` consisting of the finite sums `∑ ξ^[k] ε(c_k)`. -/
def taylorSubalgebra : Subalgebra A B where
  carrier := {y | ∃ c : ℕ →₀ B, y = c.sum fun k a ↦ δ.dpow k ξ * ε a}
  mul_mem' := by
    classical
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨∑ a ∈ c.support, ∑ b ∈ d.support,
      Finsupp.single (a + b) (((a + b).choose a : B) * (c a * d b)), ?_⟩
    rw [← Finsupp.sum_finsetSum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [map_add, mul_add])]
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finsupp.sum_finsetSum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [map_add, mul_add])]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finsupp.sum_single_index (by simp), map_mul, map_mul, map_natCast]
    have := δ.mul_dpow (m := a) (n := b) ξ_mem
    calc δ.dpow a ξ * ε (c a) * (δ.dpow b ξ * ε (d b))
        = (δ.dpow a ξ * δ.dpow b ξ) * (ε (c a) * ε (d b)) := by ring
      _ = _ := by rw [this]; ring
  add_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, by rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ by rw [map_add, mul_add])]⟩
  algebraMap_mem' a := ⟨Finsupp.single 0 (algebraMap A B a), by
    rw [Finsupp.sum_single_index (by simp), δ.dpow_zero ξ_mem, one_mul, AlgHom.commutes]⟩

theorem mem_taylorSubalgebra_of_ε (y : B) :
    ε y ∈ taylorSubalgebra (δ := δ) ε ξ ξ_mem := ⟨Finsupp.single 0 y, by
  rw [Finsupp.sum_single_index (by simp), δ.dpow_zero ξ_mem, one_mul]⟩

theorem dpow_mem_taylorSubalgebra (k : ℕ) :
    δ.dpow k ξ ∈ taylorSubalgebra (δ := δ) ε ξ ξ_mem := ⟨Finsupp.single k 1, by
  rw [Finsupp.sum_single_index (by simp), map_one, mul_one]⟩

include hε ξ_mem εξ in
/-- `ε (ξ^[k])` is `1` for `k = 0` and `0` otherwise. -/
theorem ε_dpow_eq_ite (k : ℕ) : ε (δ.dpow k ξ) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; rw [δ.dpow_zero ξ_mem, map_one]
  · have h := hε.dpow_comp (n := k) ξ ξ_mem
    change δ.dpow k (ε ξ) = ε (δ.dpow k ξ) at h
    rw [← h, εξ, δ.dpow_eval_zero hk]

include hε idem ξ_mem εξ in
/-- `ε (∑ ξ^[k] ε(c_k)) = ε(c_0)`. -/
theorem ε_taylorSum (c : ℕ →₀ B) :
    ε (c.sum fun k a ↦ δ.dpow k ξ * ε a) = ε (c 0) := by
  classical
  rw [Finsupp.sum, map_sum]
  simp_rw [map_mul, ε_dpow_eq_ite ε hε ξ ξ_mem εξ, idem]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h0; rw [Finsupp.notMem_support_iff.mp h0]; simp

include hε idem in
/-- The divided powers of an element `ε y ∈ J` lie in the Taylor subalgebra. -/
theorem dpow_ε_mem_taylorSubalgebra (y : B) (hy : ε y ∈ J) (n : ℕ) :
    δ.dpow n (ε y) ∈ taylorSubalgebra (δ := δ) ε ξ ξ_mem := by
  have h := hε.dpow_comp (n := n) (ε y) hy
  change δ.dpow n (ε (ε y)) = ε (δ.dpow n (ε y)) at h
  rw [idem] at h
  rw [h]
  exact mem_taylorSubalgebra_of_ε _ _ _ _

/-- The divided powers of `ξ^[i + 1]` lie in the Taylor subalgebra. -/
theorem dpow_dpow_mem_taylorSubalgebra (i j : ℕ) :
    δ.dpow j (δ.dpow (i + 1) ξ) ∈ taylorSubalgebra (δ := δ) ε ξ ξ_mem := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · rw [hj, δ.dpow_zero (δ.dpow_mem (by omega) ξ_mem)]
    exact Subalgebra.one_mem _
  rw [δ.dpow_comp (by omega) ξ_mem]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_mem_taylorSubalgebra _ _ _ _)

include hε idem εξ in
/-- The Taylor subalgebra is stable under the divided powers of its elements
lying in `J`. -/
theorem taylorSubalgebra_dpow_mem (x : B) (hx : x ∈ taylorSubalgebra (δ := δ) ε ξ ξ_mem)
    (hxK : x ∈ J) (n : ℕ) : δ.dpow n x ∈ taylorSubalgebra (δ := δ) ε ξ ξ_mem := by
  classical
  obtain ⟨c, rfl⟩ := hx
  have hterm : ∀ k ∈ c.support, δ.dpow k ξ * ε (c k) ∈ J := by
    intro k _
    rcases k with _ | k
    · rw [δ.dpow_zero ξ_mem, one_mul, ← ε_taylorSum ε hε idem ξ ξ_mem εξ]
      exact hε.ideal_comp (Ideal.mem_map_of_mem _ hxK)
    · exact J.mul_mem_right _ (δ.dpow_mem (by omega) ξ_mem)
  rw [Finsupp.sum, δ.dpow_sum hterm]
  refine Subalgebra.sum_mem _ fun k _ ↦ Subalgebra.prod_mem _ fun i hi ↦ ?_
  rcases i with _ | i
  · rw [δ.dpow_zero ξ_mem, one_mul]
    have hmem := hterm 0 hi
    rw [δ.dpow_zero ξ_mem, one_mul] at hmem
    exact dpow_ε_mem_taylorSubalgebra ε hε idem ξ ξ_mem _ hmem _
  · rw [mul_comm, δ.dpow_mul (δ.dpow_mem (by omega) ξ_mem)]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (mem_taylorSubalgebra_of_ε _ _ _ _) _)
      (dpow_dpow_mem_taylorSubalgebra _ _ _ _ _)

end Taylor

/-! ## Coboundaries -/

/-- `ω` is a coboundary in the divided power de Rham complex; in degree `0` this
means `ω = 0`. -/
def IsBd : (j : ℕ) → PDTerm (A := A) δ j → Prop
  | 0, ω => ω = 0
  | m + 1, ω => ∃ η : PDTerm (A := A) δ m, dd δ m η = ω

theorem isBd_zero : ∀ j, IsBd (A := A) δ j 0
  | 0 => rfl
  | _ + 1 => ⟨0, map_zero _⟩

theorem isBd_add : ∀ {j} {x y : PDTerm (A := A) δ j},
    IsBd (A := A) δ j x → IsBd (A := A) δ j y → IsBd (A := A) δ j (x + y)
  | 0, _, _, hx, hy => by
      change _ = (0 : PDTerm (A := A) δ 0) at hx hy
      change _ = (0 : PDTerm (A := A) δ 0)
      rw [hx, hy, add_zero]
  | m + 1, _, _, ⟨η, hη⟩, ⟨η', hη'⟩ => ⟨η + η', by rw [map_add, hη, hη']⟩

/-- Coboundaries are preserved by the maps induced by divided power morphisms. -/
theorem isBd_pdExteriorMap {D : Type u} [CommRing D] [Algebra A D] {K : Ideal D}
    (δ' : DividedPowers K) (f : B →ₐ[A] D) (hf : IsDPMorphism δ δ' f.toRingHom) :
    ∀ {j} {x : PDTerm (A := A) δ j},
      IsBd (A := A) δ j x → IsBd (A := A) δ' j (pdExteriorMap δ δ' f hf j x)
  | 0, x, hx => by
      change x = (0 : PDTerm (A := A) δ 0) at hx
      change _ = (0 : PDTerm (A := A) δ' 0)
      rw [hx, map_zero]
  | m + 1, _, ⟨η, rfl⟩ => ⟨pdExteriorMap δ δ' f hf m η,
      (LinearMap.congr_fun (pdExteriorMap_d_naturality δ δ' f hf m) η)⟩

/-- **One-variable divided power Poincaré lemma.** For every cocycle `ω`, the form
`ω - ε^* ω` is a coboundary. -/
theorem OneVariable.isBd_sub (V : OneVariable (A := A) δ) :
    ∀ (j : ℕ) (ω : PDTerm (A := A) δ j),
      dd (A := A) δ j ω = 0 → IsBd (A := A) δ j (ω - V.εs j ω)
  | 0, ω, hω => by
      change _ = (0 : PDTerm (A := A) δ 0)
      rw [← V.cocycle_zero ω hω, sub_self]
  | m + 1, ω, hω => by
      obtain ⟨η, hη⟩ := V.cocycle_succ ω hω
      exact ⟨η, hη.symm⟩

end AffineCrystalline.DeRham
