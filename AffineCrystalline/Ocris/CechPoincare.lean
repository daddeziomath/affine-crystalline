/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.CechVanishing
import AffineCrystalline.Ocris.PresentedEnvelopeTools
import AffineCrystalline.DeRham.OneVariablePoincare

/-!
# The relative PD Poincaré lemma and the affine de Rham comparison

Let `e` be a positive integer with `e! = 0` in `A`.  Let `X^{(e)}(•)` be the Čech nerve of
the weakly initial object of `INF^{(e)}` (`Level A C e`) and `D(n) = Ocris(X^{(e)}(n))`,
a presented PD envelope of `A[x_{i,c} : i ∈ [n], c ∈ C] → C`.  We prove that the
first-vertex maps `Ω^•_{D(0)} → Ω^•_{D(n)}` are quasi-isomorphisms
(`firstVertexQuasiIso`).  Together with the vanishing lemma
(`positiveCechExact`) this gives the affine comparison between crystalline
and PD de Rham cohomology.

For a set `S` of variables let `ε_S` be the PD endomorphism of `D(n)` with
`x_s ↦ x_{0,c}` for `s = (i, c) ∈ S` and `x_s ↦ x_s` otherwise.  For a single
variable `t = (i, c)` with `i ≠ 0`, the data `ε_t`, `ξ_t = x_t - x_{0,c}` and the
PD derivation `∂/∂x_t` form an instance of `OneVariable`, the input of the
one-variable PD Poincaré lemma; the Taylor expansion property follows from the
induction principle for presented envelopes (`PresentedEnvelope.eq_top`).
Every form involves only finitely many variables, so composing the
one-variable homotopies shows that every cocycle `ω` is cohomologous to
`ε_{all} ω`, which is pulled back from `D(0)`.

## Main definitions

* `EnvelopeFamily.vsub`: the substitution sending the variables in `S` to
  vertex `0`.
* `EnvelopeFamily.εS`: the PD endomorphism `ε_S` of `D(n)`; `EnvelopeFamily.εsS`
  is the induced map on PD forms.
* `EnvelopeFamily.ξt`, `EnvelopeFamily.dert`: the element `ξ_t` and the PD
  derivation `∂/∂x_t`.
* `EnvelopeFamily.oneVariable`: the one-variable PD Poincaré data at a
  variable `t` off vertex `0`.
* `EnvelopeFamily.finiteSupportSubalgebra`: the subalgebra of elements involving
  only finitely many variables.

## Main results

* `PresentedEnvelope.pdDerivation_comp_apply_eq_zero`: a PD derivation composed
  with a PD morphism out of a presented envelope vanishes if it vanishes on the
  variables.
* `EnvelopeFamily.taylorSubalgebra_εS_eq_top`: every element of `D(n)` has a
  Taylor expansion in `ξ_t`.
* `EnvelopeFamily.exists_support_form`: every PD form on `D(n)` involves only
  finitely many variables.
* `EnvelopeFamily.isBd_sub_all`: every PD de Rham cocycle `ω` on `D(n)` is
  cohomologous to `ε_{all} ω`.
* `EnvelopeFamily.firstVertexQuasiIso`: the relative PD Poincaré lemma;
  `FirstVertexQuasiIso e` holds if `e! = 0` in `A`.
* `EnvelopeFamily.affineDeRhamComparison`: `RΓ(INF(C/A), Ocris)`
  is connected to `Ω^•_{D(0)}` by a zigzag of quasi-isomorphisms.
* `EnvelopeFamily.crystallineCohomologyIsoDeRham`:
  `H^k(RΓ(INF(C/A), Ocris)) ≅ H^k(Ω^•_{D(0)})`.

## References

* [Stacks Project, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* B. Bhatt, A. J. de Jong, *Crystalline cohomology and de Rham cohomology*,
  arXiv:1110.5001
-/

open CategoryTheory DividedPowers
open scoped Simplicial

universe u

/-- An elementary rearrangement: if `dη = y - εy` then `εy = y + (-dη)`. -/
theorem AffineCrystalline.eq_add_neg_of_eq_sub {M : Type*} [AddCommGroup M] (Y εY : M) (dη : M)
    (hη : dη = Y - εY) : εY = Y + -dη := by
  rw [hη, neg_sub, add_sub_cancel]

namespace AffineCrystalline.PresentedEnvelope

variable {A σ D D' M : Type u} [CommRing A] [CommRing D] [Algebra A D] [CommRing D']
  [Algebra A D'] [AddCommGroup M] [Module D' M] [Module A M]
  {I : Ideal A} {γ : DividedPowers I} {ι : MvPolynomial σ A →ₐ[A] D}
  {J : Ideal (MvPolynomial σ A)} {K : Ideal D} {δ : DividedPowers K} {K' : Ideal D'}
  {δ' : DividedPowers K'}

/-- Let `D` be a presented PD envelope, `f : D → D'` a PD morphism and `θ` a PD
derivation of `D'`. If `θ ∘ f` vanishes on the variables, then it vanishes. -/
theorem pdDerivation_comp_apply_eq_zero (H : IsPresentedEnvelope γ ι J δ) {θ : D' →ₗ[A] M}
    (hθ : IsPDDerivation δ' M θ) {f : D →ₐ[A] D'} (hf : IsDPMorphism δ δ' f.toRingHom)
    (hX : ∀ s, θ (f (ι (MvPolynomial.X s))) = 0) (y : D) : θ (f y) = 0 := by
  have h1 : θ 1 = 0 := (hθ.toDerivation δ' M θ).map_one_eq_zero
  let S : Subalgebra A D :=
    { carrier := {y | θ (f y) = 0}
      mul_mem' := fun {a b} ha hb ↦ by
        change θ (f a) = 0 at ha
        change θ (f b) = 0 at hb
        change θ (f (a * b)) = 0
        rw [map_mul, hθ.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      add_mem' := fun {a b} ha hb ↦ by
        change θ (f a) = 0 at ha
        change θ (f b) = 0 at hb
        change θ (f (a + b)) = 0
        rw [map_add, map_add, ha, hb, add_zero]
      algebraMap_mem' := fun a ↦ by
        change θ (f (algebraMap A D a)) = 0
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero] }
  have hS : S = ⊤ := by
    refine eq_top H S hX fun x hx hxK k ↦ ?_
    change θ (f x) = 0 at hx
    change θ (f (δ.dpow k x)) = 0
    have hfx : f x ∈ K' := hf.ideal_comp (Ideal.mem_map_of_mem _ hxK)
    rw [← show δ'.dpow k (f x) = f (δ.dpow k x) from hf.dpow_comp x hxK]
    rcases k with _ | k
    · rw [δ'.dpow_zero hfx, h1]
    · rw [hθ.dpow (k + 1) (by omega) _ hfx, hx, smul_zero]
  exact (hS ▸ Algebra.mem_top : y ∈ S)

end AffineCrystalline.PresentedEnvelope

namespace AffineCrystalline.InfinitesimalSite

open Homology InfinitesimalThickening DeRham

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
variable (e : ℕ) [NeZero e] (he : ((Nat.factorial e : ℕ) : A) = 0)

/-! ## Vertex substitutions -/

/-- The substitution of index sets sending each variable `(i, c)` in `S` to
`(0, c)` and fixing the others. -/
noncomputable def vsub {n : ℕ} (S : Fin (n + 1) × C → Prop) (s : Fin (n + 1) × C) :
    Fin (n + 1) × C := by
  classical exact if S s then (0, s.2) else s

omit [CommRing C] in
theorem vsub_snd {n : ℕ} (S : Fin (n + 1) × C → Prop) (s : Fin (n + 1) × C) :
    (vsub S s).2 = s.2 := by
  unfold vsub; split_ifs <;> rfl

theorem cechπ_rename_vsub {n : ℕ} (S : Fin (n + 1) × C → Prop) :
    (cechπ (A := A) (C := C) n).comp (MvPolynomial.rename (vsub S)) = cechπ n := by
  apply MvPolynomial.algHom_ext
  intro s
  simp [cechπ, vsub_snd]

theorem ker_map_rename_vsub {n : ℕ} (S : Fin (n + 1) × C → Prop) :
    (RingHom.ker (cechπ (A := A) (C := C) n).toRingHom).map
        (MvPolynomial.rename (R := A) (vsub S)).toRingHom ≤
      RingHom.ker (cechπ (A := A) (C := C) n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change cechπ n (MvPolynomial.rename (vsub S) x) = 0
  rw [← AlgHom.comp_apply, cechπ_rename_vsub]
  exact hx

variable {e} in
/-- The envelope `D(n) = Ocris(X^{(e)}(n))`. -/
noncomputable abbrev Dn (n : ℕ) := E.envelope (Level.cechObj (A := A) (C := C) e n).obj

include he

/-- The PD endomorphism `ε_S` of `D(n)`, induced by `x_s ↦ x_{vsub S s}`. -/
noncomputable def εS {n : ℕ} (S : Fin (n + 1) × C → Prop) :
    (E.Dn (e := e) n).carrier →ₐ[A] (E.Dn (e := e) n).carrier :=
  PresentedEnvelope.lift (E.cech_isPresentedEnvelope e he n)
    (E.cech_isPresentedEnvelope e he n) (MvPolynomial.rename (vsub S))
    (ker_map_rename_vsub S)

theorem εS_isDP {n : ℕ} (S : Fin (n + 1) × C → Prop) :
    IsDPMorphism (E.Dn (e := e) n).dividedPowers (E.Dn (e := e) n).dividedPowers
      (E.εS e he S).toRingHom :=
  (PresentedEnvelope.lift_spec _ _ _ _).2

theorem εS_X {n : ℕ} (S : Fin (n + 1) × C → Prop) (s : Fin (n + 1) × C) :
    E.εS e he S (E.cechι e n (MvPolynomial.X s)) =
      E.cechι e n (MvPolynomial.X (vsub S s)) := by
  rw [εS, PresentedEnvelope.lift_X]
  simp

theorem εS_ext {n : ℕ} {f : (E.Dn (e := e) n).carrier →ₐ[A] (E.Dn (e := e) n).carrier}
    (hf : IsDPMorphism (E.Dn (e := e) n).dividedPowers (E.Dn (e := e) n).dividedPowers f.toRingHom)
    (S : Fin (n + 1) × C → Prop)
    (h : ∀ s, f (E.cechι e n (MvPolynomial.X s)) = E.cechι e n (MvPolynomial.X (vsub S s))) :
    f = E.εS e he S :=
  PresentedEnvelope.hom_ext (E.cech_isPresentedEnvelope e he n) hf
    (E.εS_isDP e he S) fun s ↦ by rw [h, εS_X]

theorem εS_comp {n : ℕ} (S T : Fin (n + 1) × C → Prop)
    (U : Fin (n + 1) × C → Prop) (hU : ∀ s, U s ↔ S s ∨ T s) :
    (E.εS e he S).comp (E.εS e he T) = E.εS e he U := by
  apply E.εS_ext e he (IsDPMorphism.comp _ (E.εS_isDP e he S)
    (E.εS_isDP e he T))
  intro s
  rw [AlgHom.comp_apply, εS_X, εS_X]
  congr 2
  unfold vsub
  by_cases hT : T s
  · rw [if_pos hT, if_pos ((hU s).2 (Or.inr hT))]
    split_ifs <;> rfl
  · rw [if_neg hT]
    by_cases hS : S s
    · rw [if_pos hS, if_pos ((hU s).2 (Or.inl hS))]
    · rw [if_neg hS, if_neg (fun h ↦ ((hU s).1 h).elim hS hT)]

/-- `ε_S` is idempotent. -/
theorem εS_idem {n : ℕ} (S : Fin (n + 1) × C → Prop) (y : (E.Dn (e := e) n).carrier) :
    E.εS e he S (E.εS e he S y) = E.εS e he S y :=
  congrArg (fun f ↦ f y) (E.εS_comp e he S S S fun _ ↦ or_self_iff.symm)

theorem εS_eq_id_of_forall_fst_eq_zero {n : ℕ} (S : Fin (n + 1) × C → Prop)
    (hS : ∀ s, S s → s.1 = 0) : E.εS e he S = AlgHom.id A _ := by
  symm
  apply E.εS_ext e he ⟨by simp, by simp⟩
  intro s
  rw [AlgHom.id_apply]
  congr 2
  unfold vsub
  split_ifs with h
  · rw [← hS s h]
  · rfl

/-! ## One-variable data -/

section OneVar

variable {n : ℕ} (t : Fin (n + 1) × C)

/-- `ξ_t = x_t - x_{0,c}`. -/
noncomputable def ξt : (E.Dn (e := e) n).carrier :=
  E.cechι e n (MvPolynomial.X t - MvPolynomial.X (0, t.2))

omit he in
theorem ξt_mem : E.ξt e t ∈ (E.Dn (e := e) n).pdIdeal := by
  have hk : MvPolynomial.X t - MvPolynomial.X (0, t.2) ∈
      RingHom.ker (cechπ (A := A) (C := C) n).toRingHom := by
    change cechπ n _ = 0
    simp [cechπ]
  have hk' := Ideal.mem_map_of_mem (Level.cechMk (A := A) (C := C) e n).toRingHom hk
  have hker : RingHom.ker (Level.cechObj (A := A) (C := C) e n).obj.π.toRingHom =
      (RingHom.ker (cechπ (A := A) (C := C) n).toRingHom).map
        (Level.cechMk (A := A) (C := C) e n).toRingHom :=
    ker_truncate_eq_map _ _ _ _
  rw [← hker] at hk'
  exact (E.Dn (e := e) n).isEnvelope.le (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hk'))

open scoped Classical in
/-- The PD derivation `∂/∂x_t` of `D(n)`. -/
noncomputable def dert : (E.Dn (e := e) n).carrier →ₗ[A] (E.Dn (e := e) n).carrier :=
  PresentedEnvelope.extendDer (E.cech_isPresentedEnvelope e he n)
    (M := (E.Dn (e := e) n).carrier) (fun s ↦ if s = t then 1 else 0)

open scoped Classical in
theorem dert_spec :
    IsPDDerivation (E.Dn (e := e) n).dividedPowers (E.Dn (e := e) n).carrier
        (E.dert e he t) ∧
      ∀ s, E.dert e he t (E.cechι e n (MvPolynomial.X s)) = if s = t then 1 else 0 :=
  PresentedEnvelope.extendDer_spec _ _

theorem dert_algebraMap (a : A) : E.dert e he t (algebraMap A _ a) = 0 := by
  have h1 : E.dert e he t 1 = 0 := by
    have h := (E.dert_spec e he t).1.leibniz 1 1
    simp only [mul_one, one_smul] at h
    simpa using h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

omit [CommRing C] he in
/-- `ε_t` fixes `x_{0,c}` when `t = (i, c)` with `i ≠ 0`. -/
theorem vsub_eq_self_zero (ht : t.1 ≠ 0) : vsub (· = t) ((0 : Fin (n + 1)), t.2) = (0, t.2) := by
  unfold vsub
  rw [if_neg fun h ↦ ht (congrArg Prod.fst h).symm]

/-- `ε_t` kills `ξ_t`. -/
theorem εS_ξt (ht : t.1 ≠ 0) : E.εS e he (· = t) (E.ξt e t) = 0 := by
  rw [ξt, map_sub, map_sub, εS_X, εS_X, vsub_eq_self_zero t ht]
  unfold vsub
  rw [if_pos rfl, sub_self]

/-- `∂/∂x_t (ξ_t) = 1`. -/
theorem dert_ξt (ht : t.1 ≠ 0) : E.dert e he t (E.ξt e t) = 1 := by
  rw [ξt, map_sub, map_sub, (E.dert_spec e he t).2, (E.dert_spec e he t).2,
    if_pos rfl, if_neg fun h ↦ ht (congrArg Prod.fst h).symm, sub_zero]

/-- `∂/∂x_t` kills the image of `ε_t`, whose elements do not involve `x_t`. -/
theorem dert_εS (ht : t.1 ≠ 0) (y : (E.Dn (e := e) n).carrier) :
    E.dert e he t (E.εS e he (· = t) y) = 0 := by
  refine PresentedEnvelope.pdDerivation_comp_apply_eq_zero
    (E.cech_isPresentedEnvelope e he n) (E.dert_spec e he t).1
    (E.εS_isDP e he _) (fun s ↦ ?_) y
  have hne : vsub (· = t) s ≠ t := by
    unfold vsub
    split_ifs with h
    · exact fun h' ↦ ht (congrArg Prod.fst h').symm
    · exact h
  rw [εS_X, (E.dert_spec e he t).2, if_neg hne]

/-- The variables `x_s` lie in the Taylor subalgebra of `ε_t` and `ξ_t`. -/
theorem cechι_X_mem_taylorSubalgebra (ht : t.1 ≠ 0) (s : Fin (n + 1) × C) :
    E.cechι e n (MvPolynomial.X s) ∈ taylorSubalgebra (δ := (E.Dn (e := e) n).dividedPowers)
      (E.εS e he (· = t)) (E.ξt e t) (E.ξt_mem e t) := by
  by_cases hs : s = t
  · subst hs
    have hx : E.cechι e n (MvPolynomial.X s) =
        E.ξt e s + E.εS e he (· = s) (E.cechι e n (MvPolynomial.X (0, s.2))) := by
      rw [εS_X, vsub_eq_self_zero s ht, ξt, map_sub]
      ring
    rw [hx]
    refine Subalgebra.add_mem _ ?_ (mem_taylorSubalgebra_of_ε _ _ _ _)
    simpa only [(E.Dn (e := e) n).dividedPowers.dpow_one (E.ξt_mem e s)] using
      dpow_mem_taylorSubalgebra (δ := (E.Dn (e := e) n).dividedPowers)
        (E.εS e he (· = s)) (E.ξt e s) (E.ξt_mem e s) 1
  · have h0 : E.cechι e n (MvPolynomial.X s) =
        E.εS e he (· = t) (E.cechι e n (MvPolynomial.X s)) := by
      rw [εS_X]
      unfold vsub
      rw [if_neg hs]
    rw [h0]
    exact mem_taylorSubalgebra_of_ε _ _ _ _

/-- Every element of `D(n)` has a Taylor expansion `∑ ξ_t^[k] ε_t(c_k)` in the
variable `ξ_t`. -/
theorem taylorSubalgebra_εS_eq_top (ht : t.1 ≠ 0) :
    taylorSubalgebra (δ := (E.Dn (e := e) n).dividedPowers)
      (E.εS e he (· = t)) (E.ξt e t) (E.ξt_mem e t) = ⊤ :=
  PresentedEnvelope.eq_top (E.cech_isPresentedEnvelope e he n) _
    (E.cechι_X_mem_taylorSubalgebra e he t ht) fun x hx hxK k ↦
      taylorSubalgebra_dpow_mem _ (E.εS_isDP e he _) (E.εS_idem e he _) _ _
        (E.εS_ξt e he t ht) x hx hxK k

/-- The one-variable PD Poincaré data at a variable `t` off vertex `0`. -/
noncomputable def oneVariable (ht : t.1 ≠ 0) :
    OneVariable (A := A) (E.Dn (e := e) n).dividedPowers where
  ε := E.εS e he (· = t)
  hε := E.εS_isDP e he _
  idem := E.εS_idem e he _
  ξ := E.ξt e t
  ξ_mem := E.ξt_mem e t
  ε_ξ := E.εS_ξt e he t ht
  der := E.dert e he t
  hder := (E.dert_spec e he t).1
  der_ξ := E.dert_ξt e he t ht
  der_ε := E.dert_εS e he t ht
  taylor y := (E.taylorSubalgebra_εS_eq_top e he t ht ▸ Algebra.mem_top :
    y ∈ taylorSubalgebra (δ := (E.Dn (e := e) n).dividedPowers)
      (E.εS e he (· = t)) (E.ξt e t) (E.ξt_mem e t))

end OneVar

/-! ## Finite support -/

section Support

variable {n : ℕ}

/-- The map induced by `ε_S` on PD `j`-forms. -/
noncomputable abbrev εsS (S : Fin (n + 1) × C → Prop) (j : ℕ) :
    PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j →ₗ[A]
      PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j :=
  pdExteriorMap _ _ (E.εS e he S) (E.εS_isDP e he S) j

theorem εsS_comp (S T U : Fin (n + 1) × C → Prop) (hU : ∀ s, U s ↔ S s ∨ T s) (j : ℕ)
    (ω : PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j) :
    E.εsS e he S j (E.εsS e he T j ω) = E.εsS e he U j ω := by
  have h := LinearMap.congr_fun (pdExteriorMap_comp _ _ _ (E.εS e he T)
    (E.εS_isDP e he T) (E.εS e he S) (E.εS_isDP e he S) j) ω
  rw [LinearMap.comp_apply] at h
  rw [h]
  exact LinearMap.congr_fun (pdExteriorMap_congr _ _ (E.εS_comp e he S T U hU) _ _ j) ω

theorem εsS_eq_self_of_forall_fst_eq_zero (S : Fin (n + 1) × C → Prop) (hS : ∀ s, S s → s.1 = 0)
    (j : ℕ) (ω : PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j) :
    E.εsS e he S j ω = ω := by
  have h := pdExteriorMap_congr (E.Dn (e := e) n).dividedPowers (E.Dn (e := e) n).dividedPowers
    (E.εS_eq_id_of_forall_fst_eq_zero e he S hS) (E.εS_isDP e he S)
    ⟨by simp, by simp⟩ j
  rw [εsS, h, pdExteriorMap_id]
  rfl

/-- The subalgebra of the elements of `D(n)` involving only finitely many variables:
those fixed by `ε_S` whenever `S` avoids a suitable finite set. -/
noncomputable def finiteSupportSubalgebra : Subalgebra A (E.Dn (e := e) n).carrier where
  carrier := {y | ∃ F : Finset (Fin (n + 1) × C), ∀ G : Finset (Fin (n + 1) × C), F ⊆ G →
    E.εS e he (· ∉ G) y = y}
  mul_mem' := by
    classical
    rintro a b ⟨Fa, ha⟩ ⟨Fb, hb⟩
    refine ⟨Fa ∪ Fb, fun G hG ↦ ?_⟩
    rw [map_mul, ha G (le_trans Finset.subset_union_left hG),
      hb G (le_trans Finset.subset_union_right hG)]
  add_mem' := by
    classical
    rintro a b ⟨Fa, ha⟩ ⟨Fb, hb⟩
    refine ⟨Fa ∪ Fb, fun G hG ↦ ?_⟩
    rw [map_add, ha G (le_trans Finset.subset_union_left hG),
      hb G (le_trans Finset.subset_union_right hG)]
  algebraMap_mem' a := ⟨∅, fun _ _ ↦ AlgHom.commutes _ a⟩

/-- Every element of `D(n)` involves only finitely many variables: it is fixed by
`ε_S` whenever `S` avoids a suitable finite set. -/
theorem exists_support (y : (E.Dn (e := e) n).carrier) :
    ∃ F : Finset (Fin (n + 1) × C), ∀ G : Finset (Fin (n + 1) × C), F ⊆ G →
      E.εS e he (· ∉ G) y = y := by
  have hS : E.finiteSupportSubalgebra e he (n := n) = ⊤ := by
    refine PresentedEnvelope.eq_top (E.cech_isPresentedEnvelope e he n) _ ?_ ?_
    · intro s
      refine ⟨{s}, fun G hG ↦ ?_⟩
      rw [εS_X]
      unfold vsub
      rw [if_neg (not_not.mpr (hG (Finset.mem_singleton_self s)))]
    · rintro x ⟨F, hF⟩ hxK k
      refine ⟨F, fun G hG ↦ ?_⟩
      have h := (E.εS_isDP e he (· ∉ G)).dpow_comp (n := k) x hxK
      change (E.Dn (e := e) n).dividedPowers.dpow k (E.εS e he (· ∉ G) x) =
        E.εS e he (· ∉ G) ((E.Dn (e := e) n).dividedPowers.dpow k x) at h
      rw [← h, hF G hG]
  exact (hS ▸ Algebra.mem_top : y ∈ E.finiteSupportSubalgebra e he (n := n))

/-- Every PD form on `D(n)` involves only finitely many variables. -/
theorem exists_support_form (j : ℕ) (ω : PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j) :
    ∃ F : Finset (Fin (n + 1) × C), ∀ G : Finset (Fin (n + 1) × C), F ⊆ G →
      E.εsS e he (· ∉ G) j ω = ω := by
  classical
  refine pdTerm_induction _ (P := fun ω ↦ ∃ F : Finset (Fin (n + 1) × C),
    ∀ G : Finset (Fin (n + 1) × C), F ⊆ G → E.εsS e he (· ∉ G) j ω = ω) ?_ ?_ ?_ ?_ ω
  · exact ⟨∅, fun G _ ↦ map_zero _⟩
  · rintro x y ⟨Fx, hx⟩ ⟨Fy, hy⟩
    refine ⟨Fx ∪ Fy, fun G hG ↦ ?_⟩
    rw [map_add, hx G (le_trans Finset.subset_union_left hG),
      hy G (le_trans Finset.subset_union_right hG)]
  · rintro b x ⟨Fx, hx⟩
    obtain ⟨Fb, hb⟩ := E.exists_support e he b
    refine ⟨Fb ∪ Fx, fun G hG ↦ ?_⟩
    rw [εsS, pdExteriorMap_smul, ← εsS, hx G (le_trans Finset.subset_union_right hG)]
    exact congrArg (· • x) (hb G (le_trans Finset.subset_union_left hG))
  · intro g
    choose F hF using fun i ↦ E.exists_support e he (g i)
    refine ⟨Finset.univ.biUnion F, fun G hG ↦ ?_⟩
    refine (pdExteriorMap_ιMulti _ _ _ _ j _).trans ?_
    refine congrArg (exteriorPower.ιMulti _ j) (funext fun i ↦ ?_)
    refine (pdKaehlerMap_pdD _ _ _ _ (g i)).trans ?_
    exact congrArg _ (hF i G (le_trans (Finset.subset_biUnion_of_mem F (Finset.mem_univ i)) hG))

theorem dd_εsS (S : Fin (n + 1) × C → Prop) (j : ℕ)
    (ω : PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j) :
    dd _ j (E.εsS e he S j ω) = E.εsS e he S (j + 1) (dd _ j ω) :=
  LinearMap.congr_fun (pdExteriorMap_d_naturality _ _ _ _ j) ω

/-- For a finite set `F` of variables, every cocycle `ω` is cohomologous to
`ε_F ω`; this composes the one-variable homotopies over `F`. -/
theorem isBd_sub_finset (j : ℕ) (F : Finset (Fin (n + 1) × C)) :
    ∀ ω : PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j, dd _ j ω = 0 →
      IsBd (A := A) _ j (ω - E.εsS e he (· ∈ F) j ω) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      intro ω _
      rw [E.εsS_eq_self_of_forall_fst_eq_zero e he _
        (fun s hs ↦ absurd hs (Finset.notMem_empty s)), sub_self]
      exact isBd_zero _ j
  | insert t F ht ih =>
      intro ω hω
      have hcomp := E.εsS_comp e he (· ∈ F) (· = t) (· ∈ insert t F)
        (fun s ↦ by rw [Finset.mem_insert]; tauto) j ω
      rw [← hcomp]
      have hsplit : ω - E.εsS e he (· ∈ F) j (E.εsS e he (· = t) j ω) =
          (ω - E.εsS e he (· = t) j ω) +
            (E.εsS e he (· = t) j ω -
              E.εsS e he (· ∈ F) j (E.εsS e he (· = t) j ω)) := by abel
      rw [hsplit]
      refine isBd_add _ ?_ (ih _ (by rw [dd_εsS, hω, map_zero]))
      by_cases h0 : t.1 = 0
      · rw [E.εsS_eq_self_of_forall_fst_eq_zero e he _ (fun s hs ↦ hs ▸ h0), sub_self]
        exact isBd_zero _ j
      · exact (E.oneVariable e he t h0).isBd_sub _ j ω hω

/-- Every PD de Rham cocycle on `D(n)` is cohomologous to its image under
`ε_{all}` (all variables sent to vertex `0`). -/
theorem isBd_sub_all (j : ℕ) (ω : PDTerm (A := A) (E.Dn (e := e) n).dividedPowers j)
    (hω : dd _ j ω = 0) :
    IsBd (A := A) _ j (ω - E.εsS e he (fun _ ↦ True) j ω) := by
  obtain ⟨F, hF⟩ := E.exists_support_form e he j ω
  have h := E.εsS_comp e he (· ∈ F) (· ∉ F) (fun _ ↦ True) (fun s ↦ by tauto) j ω
  rw [← h, hF F le_rfl]
  exact E.isBd_sub_finset e he j F ω hω

end Support

/-! ## The Poincaré lemma -/

omit he in
theorem levelCechDeRham_map_apply {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (j : ℕ)
    (x : ((E.levelCechDeRham e).obj ⦋m⦌).X j) :
    (((E.levelCechDeRham e).map f).f j).hom x =
      ULift.up (pdExteriorMap _ _ (EnvelopeChoice.comparison ((Level.ι e).map
          ((Level.cechNerve e).map f)) (E.Dn (e := e) m) (E.Dn (e := e) n))
        (EnvelopeChoice.comparison_spec ((Level.ι e).map ((Level.cechNerve e).map f))
          (E.Dn (e := e) m) (E.Dn (e := e) n)).2 j x.down) := rfl

omit he in
theorem levelCechDeRham_d_apply (n j : ℕ) (x : ((E.levelCechDeRham e).obj ⦋n⦌).X j) :
    (((E.levelCechDeRham e).obj ⦋n⦌).d j (j + 1)).hom x =
      ULift.up (dd (A := A) (E.Dn (e := e) n).dividedPowers j x.down) := rfl

/-- The comparison map of `D(n)` along the constant map `[n] → [n]` with value
`0` is `ε_{all}`. -/
theorem comparison_const_eq_εS (n : ℕ) :
    EnvelopeChoice.comparison ((Level.ι e).map ((Level.cechNerve e).map
        (SimplexCategory.const ⦋n⦌ ⦋n⦌ 0))) (E.Dn (e := e) n) (E.Dn (e := e) n) =
      E.εS e he (fun _ ↦ True) := by
  apply E.εS_ext e he (n := n) (EnvelopeChoice.comparison_spec _ _ _).2
  intro s
  refine (E.cech_comparison_X e (m := n) (n := n) (SimplexCategory.const ⦋n⦌ ⦋n⦌ 0) s).trans ?_
  unfold vsub
  rw [if_pos trivial]
  rfl

/-- On `Ω^•_{D(n)}`, the composite of the maps induced by `[n] → [0]` and by the
first vertex `[0] → [n]` is `ε_{all}`. -/
theorem levelCechDeRham_map_const_apply (n j : ℕ) (y : ((E.levelCechDeRham e).obj ⦋n⦌).X j) :
    (((E.levelCechDeRham e).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).f j).hom
        ((((E.levelCechDeRham e).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).f j).hom y) =
      ULift.up (E.εsS e he (fun _ ↦ True) j y.down) := by
  have := congrArg (fun φ ↦ (φ.f j).hom y) ((E.levelCechDeRham e).map_comp
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [← this, show SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 =
    SimplexCategory.const ⦋n⦌ ⦋n⦌ 0 from rfl, levelCechDeRham_map_apply]
  congr 1
  exact LinearMap.congr_fun (pdExteriorMap_congr _ _ (E.comparison_const_eq_εS e he n)
    _ _ j) y.down

/-- Every cocycle `y` of `Ω^•_{D(n)}` is cohomologous to `ε_{all} y`. -/
theorem exists_εsS_all_eq_add_d (n j : ℕ) (y : ((E.levelCechDeRham e).obj ⦋n⦌).X j)
    (hy : (((E.levelCechDeRham e).obj ⦋n⦌).d j (j + 1)).hom y = 0) :
    ∃ z : ((E.levelCechDeRham e).obj ⦋n⦌).X (j - 1),
      ULift.up (E.εsS e he (fun _ ↦ True) j y.down) =
        y + (((E.levelCechDeRham e).obj ⦋n⦌).d (j - 1) j).hom z := by
  have hbd := E.isBd_sub_all e he (n := n) j y.down (congrArg ULift.down hy)
  rcases j with _ | m
  · refine ⟨0, ?_⟩
    change _ = (0 : PDTerm (A := A) _ 0) at hbd
    rw [map_zero, add_zero]
    exact ULift.down_injective (sub_eq_zero.mp hbd).symm
  · obtain ⟨η, hη⟩ := hbd
    refine ⟨ULift.up (-η), ULift.down_injective ((eq_add_neg_of_eq_sub _ _ _ hη).trans ?_)⟩
    exact congrArg (fun t ↦ y.down + t)
      (map_neg (dd (A := A) (E.Dn (e := e) n).dividedPowers m) η).symm

/-- **The relative PD Poincaré lemma**
[Stacks Project, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD): if `e! = 0` in `A`,
every first-vertex map `Ω^•_{D(0)} → Ω^•_{D(n)}` is a quasi-isomorphism, i.e.
`FirstVertexQuasiIso e` holds.  The map induced by `[n] → [0]` is a left inverse,
and the composite in the other order is `ε_{all}`, which induces the identity on
cohomology by `isBd_sub_all`. -/
theorem firstVertexQuasiIso : E.FirstVertexQuasiIso e := by
  intro n
  set Kc := E.levelCechDeRham e
  set s0 : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ 0
  set r0 : ⦋n⦌ ⟶ ⦋0⦌ := SimplexCategory.const ⦋n⦌ ⦋0⦌ 0
  have hsr : s0 ≫ r0 = 𝟙 ⦋0⦌ := by
    ext i : 3
    exact Subsingleton.elim (α := Fin 1) _ _
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_elementwise]
  constructor
  · intro y hy
    refine ⟨((Kc.map r0).f j).hom y, by rw [hom_comm_apply, hy, map_zero], ?_⟩
    rw [E.levelCechDeRham_map_const_apply e he n j y]
    exact E.exists_εsS_all_eq_add_d e he n j y hy
  · intro x hx z hz
    refine ⟨((Kc.map r0).f (j - 1)).hom z, ?_⟩
    rw [hom_comm_apply, ← hz]
    have := congrArg (fun φ ↦ (φ.f j).hom x) (Kc.map_comp s0 r0)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [← this, hsr, Kc.map_id]
    rfl

end EnvelopeFamily

/-! ## The affine de Rham comparison -/

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I] (hIC : I.map (algebraMap A C) = ⊥)
variable (n : ℕ) [NeZero n] (hn : ((Nat.factorial n : ℕ) : A) = 0)

include hn in
/-- **Affine de Rham comparison for crystalline cohomology**
[Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM).
If `n! = 0` in `A`, the complex `lim I^•` computing `RΓ(INF(C/A), Ocris)` on `INF^{(n)}`
(see `ocrisDerivedGlobalSectionsIsoLimComplex`) is connected by a zigzag of
quasi-isomorphisms to the PD de Rham complex `Ω^•_{D(0)}` of the PD envelope `D(0)`
of `A[x_c : c ∈ C] → C` (`ocrisCech_isEnvelope`).  This is
`affineDeRhamComparison_of_quasiIso_of_exact` combined with `firstVertexQuasiIso` and
`positiveCechExact`.  For the Frobenius level `n = p ^ e`, the site `INF_e` of the
accompanying article, the hypothesis reads `(p ^ e)! = 0` in `A`. -/
theorem affineDeRhamComparison :
    QuasiIsoEquiv
      (Cohomology.Cech.limComplex (injectiveResolution (E.levelOcrisModule p hIC n)))
      ((ocrisDeRhamComplex E).obj (Level.cechObj n 0).obj) :=
  E.affineDeRhamComparison_of_quasiIso_of_exact p hIC n (E.firstVertexQuasiIso n hn)
    (E.positiveCechExact n hn)

include p hIC hn in
/-- **Crystalline cohomology is PD de Rham cohomology (affine case).**  If
`n! = 0` in `A`, the `k`-th cohomology of `RΓ(INF(C/A), Ocris)` is isomorphic to the
`k`-th cohomology of the PD de Rham complex of the envelope `D(0)` of the canonical
presentation `A[x_c : c ∈ C] → C`, where `D(0) = Ocris(X^{(n)}(0))`. -/
theorem crystallineCohomologyIsoDeRham (k : ℕ) :
    Nonempty (((HomotopyCategory.homologyFunctor (ModuleCat.{u + 1} A) (ComplexShape.up ℕ) k).obj
        (ocrisDerivedGlobalSections E)) ≅
      ((ocrisDeRhamComplex E).obj (Level.cechObj n 0).obj).homology k) :=
  E.crystallineCohomologyIsoDeRham_of_quasiIso_of_exact p hIC n hn
    (E.firstVertexQuasiIso n hn) (E.positiveCechExact n hn) k

end EnvelopeFamily

end AffineCrystalline.InfinitesimalSite
