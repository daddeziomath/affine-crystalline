/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.PresentedEnvelope

/-!
# Basic constructions for presented PD envelopes

Let `ι : A[x_s : s ∈ σ] → (D, K, δ)` be a presented PD envelope
(`IsPresentedEnvelope`).  This file proves that `D` is generated, as a PD
algebra, by the images of the variables, and constructs morphisms and PD
derivations out of `D` from their values on the variables.

The induction principle `PresentedEnvelope.eq_top` is proved as follows: a
subalgebra `D'` containing the `ι(x_s)` and stable under the divided powers of
its elements in `K` inherits divided powers (`DividedPowers.restrictSubalgebra`)
and receives the presentation, so the universal property gives a PD morphism
`D → D'` whose composite with the inclusion is the identity of `D`.

## Main definitions

* `DividedPowers.restrictSubalgebra`: divided powers restricted to a stable
  subalgebra.
* `PresentedEnvelope.lift`: the PD morphism induced by a map of presentations.
* `PresentedEnvelope.extendDer`: the PD derivation with prescribed values on
  the variables.

## Main results

* `PresentedEnvelope.hom_ext`: PD morphisms out of a presented envelope are
  determined by their values on the variables.
* `PresentedEnvelope.eq_top`: induction principle for presented envelopes.
* `PresentedEnvelope.lift_spec`, `PresentedEnvelope.lift_X`,
  `PresentedEnvelope.extendDer_spec`: characteristic properties of `lift` and
  `extendDer`.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open DividedPowers

universe u

namespace AffineCrystalline

/-! ## Divided powers restricted to a subalgebra -/

section Restrict

variable {A D : Type u} [CommRing A] [CommRing D] [Algebra A D] {K : Ideal D}

/-- The divided powers of `δ` restricted to a subalgebra stable under them. -/
noncomputable def DividedPowers.restrictSubalgebra (δ : DividedPowers K) (D' : Subalgebra A D)
    (h : ∀ x ∈ D', x ∈ K → ∀ n, δ.dpow n x ∈ D') :
    DividedPowers (K.comap D'.val.toRingHom) := by
  classical
  exact
  { dpow := fun n x ↦ if hx : (x : D) ∈ K then ⟨δ.dpow n x, h x x.2 hx n⟩ else 0
    dpow_null := fun {n x} hx ↦ dif_neg hx
    dpow_zero := fun {x} hx ↦ by
      have hx' : (x : D) ∈ K := hx
      apply Subtype.ext
      simp only [dif_pos hx', δ.dpow_zero hx', OneMemClass.coe_one]
    dpow_one := fun {x} hx ↦ by
      have hx' : (x : D) ∈ K := hx
      apply Subtype.ext
      simp only [dif_pos hx', δ.dpow_one hx']
    dpow_mem := fun {n x} hn hx ↦ by
      have hx' : (x : D) ∈ K := hx
      simp only [dif_pos hx']
      exact δ.dpow_mem hn hx'
    dpow_add := fun {n x y} hx hy ↦ by
      have hx' : (x : D) ∈ K := hx
      have hy' : (y : D) ∈ K := hy
      have hxy : ((x + y : D') : D) ∈ K := K.add_mem hx' hy'
      apply Subtype.ext
      rw [dif_pos hxy]
      simp only [dif_pos hx', dif_pos hy', AddSubmonoidClass.coe_finsetSum,
        Subalgebra.coe_mul, Subalgebra.coe_add]
      exact δ.dpow_add hx' hy'
    dpow_mul := fun {n a x} hx ↦ by
      have hx' : (x : D) ∈ K := hx
      have hax : ((a * x : D') : D) ∈ K := K.mul_mem_left _ hx'
      apply Subtype.ext
      rw [dif_pos hax]
      simp only [dif_pos hx', Subalgebra.coe_mul, SubmonoidClass.coe_pow]
      exact δ.dpow_mul hx'
    mul_dpow := fun {m n x} hx ↦ by
      have hx' : (x : D) ∈ K := hx
      apply Subtype.ext
      simp only [dif_pos hx', Subalgebra.coe_mul]
      push_cast
      exact δ.mul_dpow hx'
    dpow_comp := fun {m n x} hn hx ↦ by
      have hx' : (x : D) ∈ K := hx
      have hx'' : δ.dpow n (x : D) ∈ K := δ.dpow_mem hn hx'
      apply Subtype.ext
      simp only [dif_pos hx', dif_pos hx'', Subalgebra.coe_mul]
      push_cast
      exact δ.dpow_comp hn hx' }

/-- The inclusion of a stable subalgebra, with the restricted divided powers, is
a PD morphism. -/
theorem DividedPowers.restrictSubalgebra_val (δ : DividedPowers K) (D' : Subalgebra A D)
    (h : ∀ x ∈ D', x ∈ K → ∀ n, δ.dpow n x ∈ D') :
    IsDPMorphism (DividedPowers.restrictSubalgebra δ D' h) δ D'.val.toRingHom where
  ideal_comp := by
    rw [Ideal.map_le_iff_le_comap]
  dpow_comp := fun {n} a ha ↦ by
    change δ.dpow n (a : D) = ((DividedPowers.restrictSubalgebra δ D' h).dpow n a : D)
    simp only [DividedPowers.restrictSubalgebra]
    rw [dif_pos (show (a : D) ∈ K from ha)]

end Restrict

namespace PresentedEnvelope

variable {A σ D : Type u} [CommRing A] [CommRing D] [Algebra A D]
variable {I : Ideal A} {γ : DividedPowers I}
variable {ι : MvPolynomial σ A →ₐ[A] D} {J : Ideal (MvPolynomial σ A)}
variable {K : Ideal D} {δ : DividedPowers K}
variable (H : IsPresentedEnvelope γ ι J δ)
include H

/-- PD morphisms out of a presented envelope are determined on the variables. -/
theorem hom_ext {D' : Type u} [CommRing D'] [Algebra A D'] {K' : Ideal D'}
    {δ' : DividedPowers K'} {f g : D →ₐ[A] D'} (hf : IsDPMorphism δ δ' f.toRingHom)
    (hg : IsDPMorphism δ δ' g.toRingHom)
    (h : ∀ s, f (ι (MvPolynomial.X s)) = g (ι (MvPolynomial.X s))) : f = g :=
  H.isDPEnvelope.algHom_ext hf hg (MvPolynomial.algHom_ext h)

/-- The corestriction of the presentation to a subalgebra `D'` containing its image
sends `J` and `I` into the ideal `K ∩ D'`. -/
theorem codRestrict_map_sup_le_comap (D' : Subalgebra A D) (hι : ∀ p, ι p ∈ D') :
    J.map (ι.codRestrict D' hι).toRingHom ⊔ I.map (algebraMap A D') ≤
      K.comap D'.val.toRingHom := by
  rw [sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  exact ⟨fun x hx ↦ H.contain (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)),
    fun a ha ↦ H.contain (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))⟩

/-- The structure map `A → D'` into a subalgebra stable under the divided powers
is compatible with the restricted divided powers. -/
theorem isDPMorphism_algebraMap_restrictSubalgebra (D' : Subalgebra A D)
    (hdp : ∀ x ∈ D', x ∈ K → ∀ n, δ.dpow n x ∈ D') :
    IsDPMorphism γ (DividedPowers.restrictSubalgebra δ D' hdp) (algebraMap A D') := by
  have hmem (a : A) (ha : a ∈ I) : algebraMap A D a ∈ K :=
    H.contain (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
  refine ⟨?_, fun {n} a ha ↦ Subtype.ext ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    exact hmem
  · change ((DividedPowers.restrictSubalgebra δ D' hdp).dpow n (algebraMap A D' a) : D) = _
    simp only [DividedPowers.restrictSubalgebra]
    rw [dif_pos (show ((algebraMap A D' a : D') : D) ∈ K from hmem a ha)]
    exact H.compat.dpow_comp a ha

/-- **Induction principle for presented envelopes.**  A subalgebra of `D`
containing the `ι(x_s)` and stable under the divided powers of its elements in
`K` is all of `D`. -/
theorem eq_top (D' : Subalgebra A D) (hX : ∀ s, ι (MvPolynomial.X s) ∈ D')
    (hdp : ∀ x ∈ D', x ∈ K → ∀ n, δ.dpow n x ∈ D') : D' = ⊤ := by
  have hι : ∀ p, ι p ∈ D' := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.algHom_C]; exact D'.algebraMap_mem a
    | add p q hp hq => rw [map_add]; exact D'.add_mem hp hq
    | mul_X p s hp => rw [map_mul]; exact D'.mul_mem hp (hX s)
  obtain ⟨ψ, hψ, -⟩ := H.initial (K.comap D'.val.toRingHom) (ι.codRestrict D' hι)
    (DividedPowers.restrictSubalgebra δ D' hdp) (codRestrict_map_sup_le_comap H D' hι)
    (isDPMorphism_algebraMap_restrictSubalgebra H D' hdp)
  have hcomp : IsDPMorphism δ δ (D'.val.comp ψ).toRingHom :=
    IsDPMorphism.comp δ (DividedPowers.restrictSubalgebra_val δ D' hdp) hψ.2
  have heq : D'.val.comp ψ = AlgHom.id A D :=
    hom_ext H hcomp ⟨by simp, by simp⟩ fun s ↦ congrArg Subtype.val
      (congrArg (fun f ↦ f (MvPolynomial.X s)) hψ.1)
  rw [eq_top_iff]
  intro d _
  rw [← show (ψ d : D) = d from congrArg (fun f ↦ f d) heq]
  exact (ψ d).2

/-- The PD morphism `D → D'` induced by a map of presentations
`φ : A[x_σ] → A[x_σ']` with `φ(J) ⊆ J'`. -/
noncomputable def lift {σ' D' : Type u} [CommRing D'] [Algebra A D']
    {ι' : MvPolynomial σ' A →ₐ[A] D'} {J' : Ideal (MvPolynomial σ' A)} {K' : Ideal D'}
    {δ' : DividedPowers K'} (H' : IsPresentedEnvelope γ ι' J' δ')
    (φ : MvPolynomial σ A →ₐ[A] MvPolynomial σ' A) (hφ : J.map φ.toRingHom ≤ J') : D →ₐ[A] D' :=
  Classical.choose (H.initial K' (ι'.comp φ) δ' (by
    refine sup_le ?_ (le_trans le_sup_right H'.contain)
    rw [show (ι'.comp φ).toRingHom = ι'.toRingHom.comp φ.toRingHom from rfl, ← Ideal.map_map]
    exact le_trans (Ideal.map_mono hφ) (le_trans le_sup_left H'.contain)) H'.compat)

/-- `lift` is a PD morphism with `lift ∘ ι = ι' ∘ φ`. -/
theorem lift_spec {σ' D' : Type u} [CommRing D'] [Algebra A D']
    {ι' : MvPolynomial σ' A →ₐ[A] D'} {J' : Ideal (MvPolynomial σ' A)} {K' : Ideal D'}
    {δ' : DividedPowers K'} (H' : IsPresentedEnvelope γ ι' J' δ')
    (φ : MvPolynomial σ A →ₐ[A] MvPolynomial σ' A) (hφ : J.map φ.toRingHom ≤ J') :
    (lift H H' φ hφ).comp ι = ι'.comp φ ∧ IsDPMorphism δ δ' (lift H H' φ hφ).toRingHom :=
  (Classical.choose_spec (H.initial K' (ι'.comp φ) δ' (by
    refine sup_le ?_ (le_trans le_sup_right H'.contain)
    rw [show (ι'.comp φ).toRingHom = ι'.toRingHom.comp φ.toRingHom from rfl, ← Ideal.map_map]
    exact le_trans (Ideal.map_mono hφ) (le_trans le_sup_left H'.contain)) H'.compat)).1

theorem lift_X {σ' D' : Type u} [CommRing D'] [Algebra A D']
    {ι' : MvPolynomial σ' A →ₐ[A] D'} {J' : Ideal (MvPolynomial σ' A)} {K' : Ideal D'}
    {δ' : DividedPowers K'} (H' : IsPresentedEnvelope γ ι' J' δ')
    (φ : MvPolynomial σ A →ₐ[A] MvPolynomial σ' A) (hφ : J.map φ.toRingHom ≤ J') (s : σ) :
    lift H H' φ hφ (ι (MvPolynomial.X s)) = ι' (φ (MvPolynomial.X s)) :=
  congrArg (fun f ↦ f (MvPolynomial.X s)) (lift_spec H H' φ hφ).1

/-- The PD derivation into a `D`-module with prescribed values on the variables. -/
noncomputable def extendDer {M : Type u} [AddCommGroup M] [Module D M] [Module A M]
    [IsScalarTower A D M] (f : σ → M) : D →ₗ[A] M := by
  letI : Module (MvPolynomial σ A) M := Module.compHom _ ι.toRingHom
  haveI : IsScalarTower A (MvPolynomial σ A) M :=
    ⟨fun a b m ↦ by
      change ι (a • b) • m = a • (ι b • m)
      rw [map_smul, smul_assoc]⟩
  exact Classical.choose (existsUnique_pdDerivation_of_initial ι J δ H.contain H.compat
    H.initial (MvPolynomial.mkDerivation A f).toLinearMap
    (fun b b' ↦ (MvPolynomial.mkDerivation A f).leibniz b b'))

/-- `extendDer f` is a PD derivation with `ι(x_s) ↦ f s`. -/
theorem extendDer_spec {M : Type u} [AddCommGroup M] [Module D M] [Module A M]
    [IsScalarTower A D M] (f : σ → M) :
    IsPDDerivation δ M (extendDer H f) ∧ ∀ s, extendDer H f (ι (MvPolynomial.X s)) = f s := by
  letI : Module (MvPolynomial σ A) M := Module.compHom _ ι.toRingHom
  haveI : IsScalarTower A (MvPolynomial σ A) M :=
    ⟨fun a b m ↦ by
      change ι (a • b) • m = a • (ι b • m)
      rw [map_smul, smul_assoc]⟩
  have h := (Classical.choose_spec (existsUnique_pdDerivation_of_initial ι J δ H.contain
    H.compat H.initial (MvPolynomial.mkDerivation A f).toLinearMap
    (fun b b' ↦ (MvPolynomial.mkDerivation A f).leibniz b b'))).1
  refine ⟨h.1, fun s ↦ ?_⟩
  have := LinearMap.congr_fun h.2 (MvPolynomial.X s)
  exact this.trans (MvPolynomial.mkDerivation_X A f s)

end PresentedEnvelope

end AffineCrystalline
