/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.PDDerivationExtension
import AffineCrystalline.Ocris.DeRham

/-!
# PD envelopes of polynomial presentations: partial differential operators

Let `ι : A[x_s : s ∈ σ] → (D, K, δ)` have the universal property of the PD
envelope of an ideal `J` of the polynomial ring, compatible with `γ`
(`IsPresentedEnvelope`).  Then:

* `Ω_{D,δ}` is generated over `D` by the differentials `dx_s = d(ι(x_s))`
  (`PresentedEnvelope.span_dx`);
* for every predicate `S` on `σ` there is a `D`-linear operator
  `partialOp S : Ω_{D,δ} → Ω_{D,δ}` with `dx_s ↦ [S s] dx_s`
  (`partialOp_dx`), obtained from the PD derivation extending
  `x_s ↦ [S s] dx_s`; it is unique by `hom_ext_dx`;
* these operators and their exterior powers are natural for maps of presented
  envelopes compatible with a map of index sets (`partialOp_natural`,
  `partialExt_natural`).

The exterior powers `partialExt` are the homotopy operators in the proof of the
vanishing lemma (`positiveCechExact`).  No freeness of `Ω_{D,δ}` is used.

## Main definitions

* `IsPresentedEnvelope`: the universal property of the PD envelope of a
  polynomial presentation.
* `PresentedEnvelope.dx`: the differential of a variable.
* `PresentedEnvelope.partialDer`: the PD derivation `D → Ω_{D,δ}` with
  `x_s ↦ [S s] dx_s`.
* `PresentedEnvelope.partialOp`, `PresentedEnvelope.partialExt`: the operator
  `dx_s ↦ [S s] dx_s` on `Ω_{D,δ}` and its exterior powers.

## Main results

* `PresentedEnvelope.pdDerivation_ext`: PD derivations out of `D` are
  determined on the variables.
* `PresentedEnvelope.span_dx`: the `dx_s` generate `Ω_{D,δ}`.
* `PresentedEnvelope.partialExt_of_forall`, `PresentedEnvelope.partialExt_of_forall_not`:
  `partialExt` is the identity if `S` holds everywhere, and zero in positive
  degree if `S` holds nowhere.
* `PresentedEnvelope.partialExt_natural`: naturality.

## References

* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

open DividedPowers

universe u

namespace AffineCrystalline

variable {A σ D : Type u} [CommRing A] [CommRing D] [Algebra A D]
variable {I : Ideal A} {γ : DividedPowers I}

/-- `ι : A[x_σ] → D` exhibits `(D, K, δ)` as a PD envelope of the ideal `J`
compatible with `γ`: `ι(J)` and `I·D` lie in `K`, `δ` is compatible with `γ`,
and `ι` is initial among such maps. -/
structure IsPresentedEnvelope (γ : DividedPowers I) (ι : MvPolynomial σ A →ₐ[A] D)
    (J : Ideal (MvPolynomial σ A)) {K : Ideal D} (δ : DividedPowers K) : Prop where
  contain : J.map ι.toRingHom ⊔ I.map (algebraMap A D) ≤ K
  compat : IsDPMorphism γ δ (algebraMap A D)
  initial : ∀ {D' : Type u} [CommRing D'] [Algebra A D'] (K' : Ideal D')
    (φ' : MvPolynomial σ A →ₐ[A] D') (δ' : DividedPowers K'),
    J.map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K' →
      IsDPMorphism γ δ' (algebraMap A D') →
        ∃! ψ : D →ₐ[A] D', ψ.comp ι = φ' ∧ IsDPMorphism δ δ' ψ.toRingHom

/-- A presented envelope is a divided power envelope of the polynomial presentation. -/
theorem IsPresentedEnvelope.isDPEnvelope {ι : MvPolynomial σ A →ₐ[A] D}
    {J : Ideal (MvPolynomial σ A)} {K : Ideal D} {δ : DividedPowers K}
    (H : IsPresentedEnvelope γ ι J δ) : IsDPEnvelope γ J D ι K δ :=
  ⟨H.contain, H.compat, H.initial⟩

namespace PresentedEnvelope

variable {ι : MvPolynomial σ A →ₐ[A] D} {J : Ideal (MvPolynomial σ A)}
variable {K : Ideal D} {δ : DividedPowers K}

/-- The differential `dx_s = d(ι(x_s))` in `Ω_{D,δ}`. -/
noncomputable def dx (ι : MvPolynomial σ A →ₐ[A] D) (δ : DividedPowers K) (s : σ) :
    PDKaehler (A := A) δ :=
  pdD δ (ι (MvPolynomial.X s))

/-- A linear map out of the polynomial ring satisfying the Leibniz rule along
`ι` and vanishing on the variables vanishes. -/
theorem leibniz_eq_zero {M : Type u} [AddCommGroup M] [Module D M] [Module A M]
    [IsScalarTower A D M] (v : MvPolynomial σ A →ₗ[A] M)
    (hv : ∀ b b', v (b * b') = ι b • v b' + ι b' • v b)
    (hX : ∀ s, v (MvPolynomial.X s) = 0) : v = 0 := by
  have h1 : v 1 = 0 := by
    have h := hv 1 1
    simp only [mul_one, map_one, one_smul] at h
    simpa using h
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul, map_smul, h1, smul_zero]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq, LinearMap.zero_apply, add_zero]
  | mul_X p s hp => rw [hv, hX, hp]; simp

/-- Two linear maps satisfying the Leibniz rule along `ι` and agreeing on the
variables agree. -/
theorem leibniz_ext {M : Type u} [AddCommGroup M] [Module D M] [Module A M]
    [IsScalarTower A D M] (v w : MvPolynomial σ A →ₗ[A] M)
    (hv : ∀ b b', v (b * b') = ι b • v b' + ι b' • v b)
    (hw : ∀ b b', w (b * b') = ι b • w b' + ι b' • w b)
    (hX : ∀ s, v (MvPolynomial.X s) = w (MvPolynomial.X s)) : v = w := by
  have := leibniz_eq_zero (ι := ι) (v - w) (fun b b' ↦ by
    simp only [LinearMap.sub_apply, hv, hw, smul_sub]; abel)
    (fun s ↦ by simp [hX s])
  exact sub_eq_zero.mp this

variable (H : IsPresentedEnvelope γ ι J δ)
include H

/-- PD derivations out of `D` are determined by their values on the
`ι(x_s)`. -/
theorem pdDerivation_ext {M : Type u} [AddCommGroup M] [Module D M] [Module A M]
    [IsScalarTower A D M] (θ θ' : D →ₗ[A] M) (hθ : IsPDDerivation δ M θ)
    (hθ' : IsPDDerivation δ M θ')
    (hX : ∀ s, θ (ι (MvPolynomial.X s)) = θ' (ι (MvPolynomial.X s))) : θ = θ' := by
  have hleib {θ₀ : D →ₗ[A] M} (h₀ : IsPDDerivation δ M θ₀) (b b' : MvPolynomial σ A) :
      (θ₀.comp ι.toLinearMap) (b * b') =
        ι b • (θ₀.comp ι.toLinearMap) b' + ι b' • (θ₀.comp ι.toLinearMap) b := by
    change θ₀ (ι (b * b')) = _
    rw [map_mul, h₀.leibniz]
    rfl
  exact H.isDPEnvelope.pdDerivation_ext hθ hθ' <|
    leibniz_ext _ _ (hleib hθ) (hleib hθ') hX

/-- `Ω_{D,δ}` is generated over `D` by the differentials of the variables. -/
theorem span_dx : Submodule.span D (Set.range (dx ι δ)) = ⊤ := by
  set S := Submodule.span D (Set.range (dx ι δ))
  have hθ := IsPDDerivation.compLinearMap δ (pdD δ) (pdD_isPDDerivation δ) S.mkQ
  have hzero : IsPDDerivation δ (PDKaehler (A := A) δ ⧸ S)
      (0 : D →ₗ[A] PDKaehler (A := A) δ ⧸ S) :=
    ⟨fun _ _ ↦ by simp, fun _ _ _ _ ↦ by simp⟩
  have heq := pdDerivation_ext H _ 0 hθ hzero (fun s ↦ by
    change S.mkQ (dx ι δ s) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨s, rfl⟩)
  have hmem : ∀ d : D, pdD δ d ∈ S := fun d ↦ by
    have := LinearMap.congr_fun heq d
    change S.mkQ (pdD δ d) = 0 at this
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  rw [eq_top_iff]
  rintro ω -
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective _ ω
  have hω : ω ∈ Submodule.span D (Set.range (KaehlerDifferential.D A D)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      exact hmem d
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact S.smul_mem a hx

/-- A `D`-linear map out of `Ω_{D,δ}` is determined by its values on the
`dx_s`. -/
theorem hom_ext_dx {M : Type u} [AddCommGroup M] [Module D M] {f g : PDKaehler (A := A) δ →ₗ[D] M}
    (h : ∀ s, f (dx ι δ s) = g (dx ι δ s)) : f = g :=
  LinearMap.ext_on_range (span_dx H) h

/-- The derivation `A[x_σ] → Ω_{D,δ}` along `ι` with `x_s ↦ [S s] dx_s`. -/
noncomputable def partialPoly (S : σ → Prop) [DecidablePred S] :
    MvPolynomial σ A →ₗ[A] PDKaehler (A := A) δ := by
  letI : Module (MvPolynomial σ A) (PDKaehler (A := A) δ) :=
    Module.compHom _ ι.toRingHom
  haveI : IsScalarTower A (MvPolynomial σ A) (PDKaehler (A := A) δ) :=
    ⟨fun a b m ↦ by
      change ι (a • b) • m = a • (ι b • m)
      rw [map_smul, smul_assoc]⟩
  exact (MvPolynomial.mkDerivation A
    (fun s ↦ if S s then dx ι δ s else 0)).toLinearMap

omit H in
theorem partialPoly_leibniz (S : σ → Prop) [DecidablePred S] (b b' : MvPolynomial σ A) :
    partialPoly (ι := ι) (δ := δ) S (b * b') =
      ι b • partialPoly (ι := ι) (δ := δ) S b' + ι b' • partialPoly (ι := ι) (δ := δ) S b := by
  letI : Module (MvPolynomial σ A) (PDKaehler (A := A) δ) :=
    Module.compHom _ ι.toRingHom
  haveI : IsScalarTower A (MvPolynomial σ A) (PDKaehler (A := A) δ) :=
    ⟨fun a b m ↦ by
      change ι (a • b) • m = a • (ι b • m)
      rw [map_smul, smul_assoc]⟩
  exact (MvPolynomial.mkDerivation A (fun s ↦ if S s then dx ι δ s else 0)).leibniz b b'

omit H in
theorem partialPoly_X (S : σ → Prop) [DecidablePred S] (s : σ) :
    partialPoly (ι := ι) (δ := δ) S (MvPolynomial.X s) = if S s then dx ι δ s else 0 := by
  letI : Module (MvPolynomial σ A) (PDKaehler (A := A) δ) :=
    Module.compHom _ ι.toRingHom
  haveI : IsScalarTower A (MvPolynomial σ A) (PDKaehler (A := A) δ) :=
    ⟨fun a b m ↦ by
      change ι (a • b) • m = a • (ι b • m)
      rw [map_smul, smul_assoc]⟩
  exact MvPolynomial.mkDerivation_X A _ s

/-- The PD derivation `D → Ω_{D,δ}` with `x_s ↦ [S s] dx_s`. -/
noncomputable def partialDer (S : σ → Prop) [DecidablePred S] :
    D →ₗ[A] PDKaehler (A := A) δ :=
  Classical.choose (existsUnique_pdDerivation_of_initial ι J δ H.contain H.compat H.initial
    (partialPoly (ι := ι) (δ := δ) S) (partialPoly_leibniz S))

theorem partialDer_spec (S : σ → Prop) [DecidablePred S] :
    IsPDDerivation δ (PDKaehler (A := A) δ) (partialDer H S) ∧
      (partialDer H S).comp ι.toLinearMap = partialPoly (ι := ι) (δ := δ) S :=
  (Classical.choose_spec (existsUnique_pdDerivation_of_initial ι J δ H.contain H.compat
    H.initial (partialPoly (ι := ι) (δ := δ) S) (partialPoly_leibniz S))).1

/-- The `D`-linear operator `dx_s ↦ [S s] dx_s` on `Ω_{D,δ}`. -/
noncomputable def partialOp (S : σ → Prop) [DecidablePred S] :
    PDKaehler (A := A) δ →ₗ[D] PDKaehler (A := A) δ :=
  PDKaehler.lift δ _ (partialDer H S) (partialDer_spec H S).1

/-- `partialOp S` sends `dx_s` to `[S s] dx_s`. -/
theorem partialOp_dx (S : σ → Prop) [DecidablePred S] (s : σ) :
    partialOp H S (dx ι δ s) = if S s then dx ι δ s else 0 := by
  have h1 := LinearMap.congr_fun (PDKaehler.lift_comp δ _ (partialDer H S)
    (partialDer_spec H S).1) (ι (MvPolynomial.X s))
  have h2 := LinearMap.congr_fun (partialDer_spec H S).2 (MvPolynomial.X s)
  change partialOp H S (pdD δ (ι (MvPolynomial.X s))) = _
  exact h1.trans (h2.trans (partialPoly_X S s))

theorem partialOp_of_forall (S : σ → Prop) [DecidablePred S] (hS : ∀ s, S s) :
    partialOp H S = LinearMap.id :=
  hom_ext_dx H fun s ↦ by rw [partialOp_dx, if_pos (hS s)]; rfl

theorem partialOp_of_forall_not (S : σ → Prop) [DecidablePred S] (hS : ∀ s, ¬ S s) :
    partialOp H S = 0 :=
  hom_ext_dx H fun s ↦ by rw [partialOp_dx, if_neg (hS s)]; rfl

/-! ## Exterior powers -/

/-- The operator `⋀^q (partialOp S)` on PD `q`-forms. -/
noncomputable def partialExt (q : ℕ) (S : σ → Prop) [DecidablePred S] :
    DeRham.PDTerm (A := A) δ q →ₗ[D] DeRham.PDTerm (A := A) δ q :=
  exteriorPower.map q (partialOp H S)

theorem partialExt_of_forall (q : ℕ) (S : σ → Prop) [DecidablePred S] (hS : ∀ s, S s) :
    partialExt H q S = LinearMap.id := by
  rw [partialExt, partialOp_of_forall H S hS]
  exact exteriorPower.map_id

theorem partialExt_of_forall_not (q : ℕ) (S : σ → Prop) [DecidablePred S] (hS : ∀ s, ¬ S s) :
    partialExt H (q + 1) S = 0 := by
  apply LinearMap.ext_on_range (exteriorPower.ιMulti_span (R := D) (n := q + 1)
    (M := PDKaehler (A := A) δ))
  intro v
  rw [partialExt, exteriorPower.map_apply_ιMulti, partialOp_of_forall_not H S hS,
    LinearMap.zero_apply]
  exact AlternatingMap.map_coord_zero _ 0 (by simp)

/-! ## Naturality -/

omit H in
/-- The map induced on PD differentials is semilinear along `g`. -/
theorem _root_.AffineCrystalline.DeRham.pdKaehlerMap_smul {D' : Type u} [CommRing D']
    [Algebra A D'] {K' : Ideal D'} (δ' : DividedPowers K') (g : D →ₐ[A] D')
    (hg : IsDPMorphism δ δ' g.toRingHom) (d : D) (ω : PDKaehler (A := A) δ) :
    DeRham.pdKaehlerMap δ δ' g hg (d • ω) = g d • DeRham.pdKaehlerMap δ δ' g hg ω := by
  letI : Algebra D D' := g.toRingHom.toAlgebra
  simp only [DeRham.pdKaehlerMap, LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

/-- Naturality of `partialOp`: if a PD morphism `g : D → D'` between presented
envelopes sends `ι(x_s)` to `ι'(x_{r(s)})`, then `g` intertwines
`partialOp (S' ∘ r)` and `partialOp S'`. -/
theorem partialOp_natural {σ' D' : Type u} [CommRing D'] [Algebra A D']
    {ι' : MvPolynomial σ' A →ₐ[A] D'} {J' : Ideal (MvPolynomial σ' A)} {K' : Ideal D'}
    {δ' : DividedPowers K'} (H' : IsPresentedEnvelope γ ι' J' δ') (g : D →ₐ[A] D')
    (hg : IsDPMorphism δ δ' g.toRingHom) (r : σ → σ')
    (hgr : ∀ s, g (ι (MvPolynomial.X s)) = ι' (MvPolynomial.X (r s)))
    (S' : σ' → Prop) [DecidablePred S'] (ω : PDKaehler (A := A) δ) :
    DeRham.pdKaehlerMap δ δ' g hg (partialOp H (fun s ↦ S' (r s)) ω) =
      partialOp H' S' (DeRham.pdKaehlerMap δ δ' g hg ω) := by
  have hω : ω ∈ Submodule.span D (Set.range (dx ι δ)) := by rw [span_dx H]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      have hdx : DeRham.pdKaehlerMap δ δ' g hg (dx ι δ s) = dx ι' δ' (r s) := by
        rw [dx, DeRham.pdKaehlerMap_pdD, hgr]
        rfl
      rw [partialOp_dx, hdx, partialOp_dx]
      split_ifs
      · exact hdx
      · exact map_zero _
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul d x _ hx =>
      rw [LinearMap.map_smul, DeRham.pdKaehlerMap_smul, DeRham.pdKaehlerMap_smul,
        LinearMap.map_smul, hx]

/-- Naturality of `partialExt`, in the setting of `partialOp_natural`. -/
theorem partialExt_natural {σ' D' : Type u} [CommRing D'] [Algebra A D']
    {ι' : MvPolynomial σ' A →ₐ[A] D'} {J' : Ideal (MvPolynomial σ' A)} {K' : Ideal D'}
    {δ' : DividedPowers K'} (H' : IsPresentedEnvelope γ ι' J' δ') (g : D →ₐ[A] D')
    (hg : IsDPMorphism δ δ' g.toRingHom) (r : σ → σ')
    (hgr : ∀ s, g (ι (MvPolynomial.X s)) = ι' (MvPolynomial.X (r s)))
    (q : ℕ) (S' : σ' → Prop) [DecidablePred S'] (x : DeRham.PDTerm (A := A) δ q) :
    DeRham.pdExteriorMap δ δ' g hg q (partialExt H q (fun s ↦ S' (r s)) x) =
      partialExt H' q S' (DeRham.pdExteriorMap δ δ' g hg q x) := by
  have hx : x ∈ Submodule.span D (Set.range (exteriorPower.ιMulti D q)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [partialExt, exteriorPower.map_apply_ιMulti, DeRham.pdExteriorMap_ιMulti,
        DeRham.pdExteriorMap_ιMulti, partialExt, exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      exact partialOp_natural H H' g hg r hgr S' (v i)
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul d y _ hy =>
      rw [LinearMap.map_smul, DeRham.pdExteriorMap_smul, DeRham.pdExteriorMap_smul,
        LinearMap.map_smul, hy]

end PresentedEnvelope

end AffineCrystalline
