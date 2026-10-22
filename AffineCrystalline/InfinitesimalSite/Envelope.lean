/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.InfinitesimalSite.Basic
import AffineCrystalline.PDDifferentials
import AffineCrystalline.Envelope.Universal
import AffineCrystalline.Setting
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Divided power envelopes of infinitesimal thickenings

An object `X = (π : B → C)` of the big infinitesimal site `INF(C/A)` carries no
divided powers. An `EnvelopeChoice X` is a compatible divided power envelope of
`B` along `J_X = ker π`: an `A`-algebra `D_X` with a map `φ : B → D_X`, an ideal
`K_X ⊇ J_X D_X + I D_X` and divided powers on `K_X`, compatible with `γ` and
satisfying the universal property `IsDPEnvelope`. Every map between envelopes is obtained from
this universal property; no proof depends on how `D_X` is constructed.

We prove the following.

* If `n! = 0` in `A`, then `x ^ n = 0` for every element `x` of a divided power
  ideal of an `A`-algebra, since `x ^ n = n! δₙ(x)`. This applies to `n = p ^ N`
  when `p ^ N = 0` in `A`.
* If `I C = 0`, there is a unique divided power morphism `q : D_X → C`, for
  the zero divided power ideal of `C`, with `q ∘ φ = π`. It is surjective and
  `ker q = K_X`.
* A morphism `f : X → Y` induces a unique divided power morphism
  `c(f) : D_X → D_Y` with `c(f) ∘ φ_X = φ_Y ∘ f`; moreover `c(id) = id`,
  `c(g ∘ f) = c(g) ∘ c(f)`, `q_Y ∘ c(f) = q_X`, and two envelopes of `X` are
  isomorphic.

## Main definitions

* `EnvelopeChoice X`: a compatible divided power envelope of `X`.
* `EnvelopeChoice.projection`: the projection `q : D_X → C`.
* `EnvelopeChoice.comparison`: the comparison map `c(f) : D_X → D_Y`.
* `EnvelopeExistenceData`: the existence of an envelope at every object.

## Main results

* `dividedPowers_pow_eq_zero_of_factorial_eq_zero`: if `n! = 0` in `A`, every divided
  power ideal of an `A`-algebra has exponent `n`.
* `natCast_factorial_pow_eq_zero`: if `p ^ N = 0` in `A`, then `(p ^ N)! = 0` in `A`.
* `dividedPowers_bounded`: divided power ideals have bounded nilpotence exponent when
  `p` is nilpotent.
* `EnvelopeChoice.projectionKernel_eq_dividedPowersIdeal`: `ker q = K_X`.
* `EnvelopeChoice.comparison_id`, `EnvelopeChoice.comparison_comp`:
  functoriality of the comparison maps.
* `EnvelopeChoice.comparison_overC`: the comparison maps lie over `C`.
* `EnvelopeChoice.comparison_comp_comparison_left`,
  `EnvelopeChoice.comparison_comp_comparison_right`: two envelopes of the same
  object are isomorphic.
* `EnvelopeChoice.comparison_id_comp_comparison`: comparison maps commute with
  changes of envelopes.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
-/

open DividedPowers
open CategoryTheory

universe u

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-- An `A`-algebra map `g : B → D` that kills the kernel of a surjection
`f : B → C` factors through `f`. -/
private noncomputable def algHomFactorOfSurjective
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D]
    (f : B →ₐ[A] C) (hf : Function.Surjective f)
    (g : B →ₐ[A] D)
    (hker : ∀ x, x ∈ RingHom.ker f.toRingHom → g x = 0) : C →ₐ[A] D := by
  classical
  let s : C → B := fun c ↦ Classical.choose (hf c)
  have hs (c : C) : f (s c) = c := Classical.choose_spec (hf c)
  have hdesc {c : C} {b : B} (hb : f b = c) : g (s c) = g b := by
    have hmem : s c - b ∈ RingHom.ker f.toRingHom := by
      change f (s c - b) = 0
      rw [map_sub, hs c, hb]
      simp
    have hz := hker (s c - b) hmem
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  refine
    { toFun := fun c ↦ g (s c)
      map_zero' := by
        simpa using hdesc (c := 0) (b := 0) (by simp)
      map_one' := by
        simpa using hdesc (c := 1) (b := 1) (by simp)
      map_add' := fun c d ↦ by
        calc
          g (s (c + d)) = g (s c + s d) :=
            hdesc (c := c + d) (b := s c + s d) (by simp [hs])
          _ = g (s c) + g (s d) := map_add g (s c) (s d)
      map_mul' := fun c d ↦ by
        calc
          g (s (c * d)) = g (s c * s d) :=
            hdesc (c := c * d) (b := s c * s d) (by simp [hs])
          _ = g (s c) * g (s d) := map_mul g (s c) (s d)
      commutes' := fun a ↦ by
        calc
          g (s (algebraMap A C a)) = g (algebraMap A B a) :=
            hdesc (c := algebraMap A C a) (b := algebraMap A B a) (by simp)
          _ = algebraMap A D a := g.commutes a }

private theorem algHomFactorOfSurjective_comp
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D]
    (f : B →ₐ[A] C) (hf : Function.Surjective f)
    (g : B →ₐ[A] D)
    (hker : ∀ x, x ∈ RingHom.ker f.toRingHom → g x = 0) (b : B) :
    algHomFactorOfSurjective f hf g hker (f b) = g b := by
  classical
  change g (Classical.choose (hf (f b))) = g b
  have hs : f (Classical.choose (hf (f b))) = f b :=
    Classical.choose_spec (hf (f b))
  have hmem : Classical.choose (hf (f b)) - b ∈ RingHom.ker f.toRingHom := by
    change f (Classical.choose (hf (f b)) - b) = 0
    rw [map_sub, hs]
    simp
  have hz := hker (Classical.choose (hf (f b)) - b) hmem
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- A ring map sending a divided power ideal `K` to zero is a divided power
morphism to the zero divided power ideal. -/
private theorem isDPMorphism_toBot_of_ideal
    {D Q : Type u} [CommRing D] [CommRing Q] {K : Ideal D}
    (δ : DividedPowers K) (f : D →+* Q)
    (hK : K.map f = ⊥) : IsDPMorphism δ (dividedPowersBot Q) f := by
  refine ⟨?_, ?_⟩
  · simp [hK]
  · intro n x hx
    have hfx : f x = 0 := by
      have hm : f x ∈ K.map f := Ideal.mem_map_of_mem f hx
      rw [hK] at hm
      exact Ideal.mem_bot.mp hm
    by_cases hn : n = 0
    · subst n
      rw [δ.dpow_zero hx, map_one]
      simp [dividedPowersBot, hfx]
    · have hzero : f (δ.dpow n x) = 0 := by
        have hm : δ.dpow n x ∈ K := δ.dpow_mem hn hx
        have hmap : f (δ.dpow n x) ∈ K.map f :=
          Ideal.mem_map_of_mem f hm
        rw [hK] at hmap
        exact Ideal.mem_bot.mp hmap
      rw [hzero]
      simp [dividedPowersBot, hn, hfx]

/-- The quotient map `D → D ⧸ K` is a divided power morphism to the zero divided
power ideal of `D ⧸ K`. -/
theorem isDPMorphism_quotientMk_bot {D : Type u} [CommRing D] {K : Ideal D}
    (δ : DividedPowers K) : IsDPMorphism δ (dividedPowersBot (D ⧸ K)) (Ideal.Quotient.mk K) :=
  isDPMorphism_toBot_of_ideal δ _ (Ideal.map_quotient_self K)

/-- If `K` contains `I D`, then `I` maps to zero in `D ⧸ K`. -/
theorem map_algebraMap_quotient_eq_bot {D : Type u} [CommRing D] [Algebra A D] {K : Ideal D}
    (h : I.map (algebraMap A D) ≤ K) : I.map (algebraMap A (D ⧸ K)) = ⊥ := by
  rw [IsScalarTower.algebraMap_eq A D (D ⧸ K), ← Ideal.map_map, Ideal.Quotient.algebraMap_eq,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact h

private theorem isDPMorphism_base_toBot
    {A D : Type u} [CommRing A] [CommRing D] {I : Ideal A}
    (γ : DividedPowers I) (f : A →+* D)
    (hI : I.map f = ⊥) :
    IsDPMorphism γ (dividedPowersBot D) f := by
  refine ⟨?_, ?_⟩
  · exact hI ▸ le_rfl
  · intro n a ha
    have hbase : f a = 0 := by
      have hm : f a ∈ I.map f := Ideal.mem_map_of_mem f ha
      rw [hI] at hm
      exact Ideal.mem_bot.mp hm
    by_cases hn : n = 0
    · subst n
      rw [hbase, γ.dpow_zero ha, map_one]
      simp [dividedPowersBot]
    · have hmap : f (γ.dpow n a) = 0 := by
        have hm : f (γ.dpow n a) ∈ I.map f :=
          Ideal.mem_map_of_mem f (γ.dpow_mem hn ha)
        rw [hI] at hm
        exact Ideal.mem_bot.mp hm
      rw [hmap]
      simp [dividedPowersBot, hn]

/-- **Divided power ideals and factorials.** If `n! = 0` in `A`, every element `x` of a
divided power ideal of an `A`-algebra satisfies `x ^ n = 0`, since
`x ^ n = n! δₙ(x)` (`DividedPowers.factorial_mul_dpow_eq_pow`). The exponent `n` depends
neither on the ideal nor on the divided powers, and no compatibility with a divided power
structure on `A` is needed. -/
theorem dividedPowers_pow_eq_zero_of_factorial_eq_zero {A : Type*} [CommRing A] {n : ℕ}
    (hn : ((Nat.factorial n : ℕ) : A) = 0) {D : Type*} [CommRing D] [Algebra A D]
    {K : Ideal D} (δ : DividedPowers K) {x : D} (hx : x ∈ K) : x ^ n = 0 := by
  rw [← DividedPowers.factorial_mul_dpow_eq_pow δ hx, ← map_natCast (algebraMap A D), hn,
    map_zero, zero_mul]

/-- If `p ^ N = 0` in `A` for some `p > 0`, then `(p ^ N)! = 0` in `A`, since `p ^ N`
divides `(p ^ N)!`. -/
theorem natCast_factorial_pow_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : 0 < p)
    {N : ℕ} (hN : (p : A) ^ N = 0) : ((Nat.factorial (p ^ N) : ℕ) : A) = 0 := by
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pow_pos hp) le_rfl
  rw [hk, Nat.cast_mul, Nat.cast_pow, hN, zero_mul]

/-- If `p` is nilpotent in `A`, every divided power ideal of an `A`-algebra has a
bounded nilpotence exponent. -/
theorem dividedPowers_bounded
    (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] {I : Ideal A}
    [IsCrystallineBase p A I] {D : Type u} [CommRing D] [Algebra A D]
    {K : Ideal D} (δ : DividedPowers K) :
    ∃ m : ℕ, ∀ x : D, x ∈ K → x ^ m = 0 := by
  obtain ⟨N, hN⟩ := IsCrystallineBase.p_nilpotent (p := p) (A := A) (I := I)
  exact ⟨p ^ N, fun _ ↦ dividedPowers_pow_eq_zero_of_factorial_eq_zero
    (natCast_factorial_pow_eq_zero (Fact.out : p.Prime).pos hN) δ⟩

/-- A compatible divided power envelope of an object `X = (π : B → C)` of
`INF(C/A)`: an `A`-algebra `D_X` with an `A`-algebra map `φ : B → D_X`, an
ideal `K_X` of `D_X` containing `J_X D_X + I D_X`, where `J_X = ker π`, and
divided powers on `K_X`, satisfying the universal property `IsDPEnvelope`. -/
structure EnvelopeChoice (X : InfinitesimalThickening A C) where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra A carrier]
  map : X.carrier →ₐ[A] carrier
  pdIdeal : Ideal carrier
  dividedPowers : DividedPowers pdIdeal
  isEnvelope : @IsDPEnvelope A _ I γ X.carrier X.commRing X.algebra
    (RingHom.ker X.π.toRingHom) carrier commRing algebra map pdIdeal dividedPowers

namespace EnvelopeChoice

variable {X : InfinitesimalThickening A C}

instance carrierCommRing (E : EnvelopeChoice (γ := γ) X) : CommRing E.carrier :=
  E.commRing

instance carrierAlgebra (E : EnvelopeChoice (γ := γ) X) : Algebra A E.carrier :=
  E.algebra

@[simp]
theorem map_comp_id (E : EnvelopeChoice (γ := γ) X) :
    E.map.comp (AlgHom.id A X.carrier) = E.map := by
  simp

/-- If `I C = 0`, there is a unique divided power morphism `q : D_X → C`, for the
zero divided power ideal of `C`, with `q ∘ φ = π`. -/
theorem existsUnique_projection (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) :
    ∃! ψ : E.carrier →ₐ[A] C,
      ψ.comp E.map = X.π ∧
        IsDPMorphism E.dividedPowers (dividedPowersBot C)
          ψ.toRingHom := by
  apply E.isEnvelope.isInitial (⊥ : Ideal C) X.π
    (dividedPowersBot C)
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change X.π x = 0
      exact hx
    · simp [hIC]
  · refine ⟨?_, ?_⟩
    · simp [hIC]
    · intro n a ha
      have hbase : algebraMap A C a = 0 := by
        have hm : algebraMap A C a ∈ I.map (algebraMap A C) :=
          Ideal.mem_map_of_mem (algebraMap A C) ha
        rw [hIC] at hm
        exact Ideal.mem_bot.mp hm
      by_cases hn : n = 0
      · subst n
        rw [hbase, γ.dpow_zero ha, map_one]
        simp [dividedPowersBot]
      · have hmap : algebraMap A C (γ.dpow n a) = 0 := by
          have hm : algebraMap A C (γ.dpow n a) ∈ I.map (algebraMap A C) :=
            Ideal.mem_map_of_mem (algebraMap A C) (γ.dpow_mem hn ha)
          rw [hIC] at hm
          exact Ideal.mem_bot.mp hm
        rw [hmap]
        simp [dividedPowersBot, hn]

/-- The projection `q : D_X → C`, characterised by `q ∘ φ = π` and by being a
divided power morphism (`projection_spec`). -/
noncomputable def projection (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) : E.carrier →ₐ[A] C :=
  Classical.choose (existsUnique_projection E hIC)

theorem projection_spec (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) :
    (projection E hIC).comp E.map = X.π ∧
      IsDPMorphism E.dividedPowers (dividedPowersBot C)
        (projection E hIC).toRingHom :=
  (Classical.choose_spec (existsUnique_projection E hIC)).1

/-- The projection `q` is surjective, since `π` is. -/
theorem projection_surjective (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) :
    Function.Surjective (projection E hIC) := by
  intro c
  obtain ⟨b, hb⟩ := X.surjective c
  refine ⟨E.map b, ?_⟩
  exact (DFunLike.congr_fun (projection_spec E hIC).1 b).trans hb

/-- `K_X ⊆ ker q`. -/
theorem dividedPowersIdeal_le_projectionKernel
    (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) :
    E.pdIdeal ≤ RingHom.ker (projection E hIC).toRingHom := by
  change _ ≤ Ideal.comap (projection E hIC).toRingHom (⊥ : Ideal C)
  rw [← Ideal.map_le_iff_le_comap]
  exact (projection_spec E hIC).2.ideal_comp

/-- `ker q ⊆ K_X`. Put `S = K_X`. The quotient map `D_X → D_X / S` and the
composite `D_X → C → D_X / S` are divided power morphisms to the zero divided
power ideal solving the same universal problem, since `S` contains
`J_X D_X + I D_X`; so they agree, and hence `ker q ⊆ S`. -/
theorem projectionKernel_le_dividedPowersIdeal
    (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) :
    RingHom.ker (projection E hIC).toRingHom ≤ E.pdIdeal := by
  let q : E.carrier →ₐ[A] E.carrier ⧸ E.pdIdeal := Ideal.Quotient.mkₐ A E.pdIdeal
  have hηker (x : X.carrier) (hx : x ∈ RingHom.ker X.π.toRingHom) : q.comp E.map x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (E.isEnvelope.le (Ideal.mem_sup_left (Ideal.mem_map_of_mem E.map.toRingHom hx)))
  let i : C →ₐ[A] E.carrier ⧸ E.pdIdeal :=
    algHomFactorOfSurjective X.π X.surjective (q.comp E.map) hηker
  have hcomp : (i.comp (projection E hIC)).comp E.map = q.comp E.map := by
    rw [AlgHom.comp_assoc, (projection_spec E hIC).1]
    ext b
    exact algHomFactorOfSurjective_comp X.π X.surjective _ hηker b
  have hI0 : I.map (algebraMap A (E.carrier ⧸ E.pdIdeal)) = ⊥ :=
    map_algebraMap_quotient_eq_bot (le_trans le_sup_right E.isEnvelope.le)
  have hq_eq : q = i.comp (projection E hIC) :=
    (E.isEnvelope.isInitial ⊥ (q.comp E.map) (dividedPowersBot _)
      (sup_le (Ideal.map_le_iff_le_comap.mpr hηker) hI0.le)
      (isDPMorphism_base_toBot γ _ hI0)).unique
      ⟨rfl, isDPMorphism_quotientMk_bot E.dividedPowers⟩
      ⟨hcomp, IsDPMorphism.comp _ (isDPMorphism_toBot_of_ideal _ i.toRingHom (by simp))
        (projection_spec E hIC).2⟩
  intro x hx
  have hqx : q x = 0 := by
    rw [hq_eq, AlgHom.comp_apply]
    change projection E hIC x = 0 at hx
    rw [hx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hqx

/-- The kernel of the projection `q : D_X → C` is the ideal `K_X` carrying the
divided powers of the envelope. -/
theorem projectionKernel_eq_dividedPowersIdeal
    (E : EnvelopeChoice (γ := γ) X)
    (hIC : I.map (algebraMap A C) = ⊥) :
    RingHom.ker (projection E hIC).toRingHom = E.pdIdeal := by
  apply le_antisymm
  · exact projectionKernel_le_dividedPowersIdeal E hIC
  · exact dividedPowersIdeal_le_projectionKernel E hIC

/-- A compatible divided power envelope of `B` along `ker π`, in the sense of
`DPEnvelopeChoice`, is an envelope of the object `X = (π : B → C)`. -/
def ofDPEnvelopeChoice (X : InfinitesimalThickening A C)
    (E : DPEnvelopeChoice γ (RingHom.ker X.π.toRingHom)) :
    EnvelopeChoice (γ := γ) X :=
  { carrier := E.carrier
    commRing := E.commRing
    algebra := E.algebra
    map := E.map
    pdIdeal := E.pdIdeal
    dividedPowers := E.dividedPowers
    isEnvelope := E.isEnvelope }

end EnvelopeChoice

/-! ## Existence of envelopes -/

/-- Every object `X = (π : B → C)` of `INF(C/A)` has a compatible divided power
envelope along `ker π`. An envelope family is chosen from this proposition by
`EnvelopeFamily.ofExistenceData`. It always holds
(`InfinitesimalSite.envelopeExistenceData`, a consequence of
`DPEnvelope.hasDPEnvelope`). -/
structure EnvelopeExistenceData : Prop where
  exists_envelope :
    ∀ X : InfinitesimalThickening A C,
      Nonempty (DPEnvelopeChoice γ (RingHom.ker X.π.toRingHom))

namespace EnvelopeExistenceData

variable (H : EnvelopeExistenceData (A := A) (C := C) (γ := γ))

/-- Envelopes exist at every object if `HasDPEnvelope` holds for the kernel of
every object. -/
theorem of_hasDPEnvelope
    (h : ∀ X : InfinitesimalThickening A C,
      HasDPEnvelope γ (RingHom.ker X.π.toRingHom)) :
    EnvelopeExistenceData (A := A) (C := C) (γ := γ) where
  exists_envelope X := by
    letI := h X
    exact HasDPEnvelope.exists_envelope

end EnvelopeExistenceData

namespace InfinitesimalThickening.Hom

variable {X Y Z : InfinitesimalThickening A C}

/-- A morphism of `INF(C/A)` maps the kernel of `π` into the kernel of `π'`. -/
theorem kernel_map_mem (f : InfinitesimalThickening.Hom X Y)
    {x : X.carrier} (hx : x ∈ RingHom.ker X.π.toRingHom) :
    f.toAlgHom x ∈ RingHom.ker Y.π.toRingHom := by
  change Y.π (f.toAlgHom x) = 0
  rw [f.overC_apply]
  exact hx

theorem kernel_map_le (f : InfinitesimalThickening.Hom X Y) :
    Ideal.map f.toAlgHom.toRingHom (RingHom.ker X.π.toRingHom) ≤
      RingHom.ker Y.π.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact kernel_map_mem f hx

end InfinitesimalThickening.Hom

namespace EnvelopeChoice

variable {X Y Z : InfinitesimalThickening A C}

/-- For `f : X → Y`, the composite `φ_Y ∘ f` maps `J_X` into the divided power
ideal `K_Y` of `D_Y`. -/
theorem target_ideal_le
    (f : InfinitesimalThickening.Hom X Y)
    (E_Y : EnvelopeChoice (γ := γ) Y) :
    Ideal.map (E_Y.map.comp f.toAlgHom).toRingHom
        (RingHom.ker X.π.toRingHom) ⊔ I.map (algebraMap A E_Y.carrier) ≤
      E_Y.pdIdeal := by
  refine sup_le ?_ (le_sup_right.trans E_Y.isEnvelope.le)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change E_Y.map (f.toAlgHom x) ∈ E_Y.pdIdeal
  exact E_Y.isEnvelope.le (Ideal.mem_sup_left (Ideal.mem_map_of_mem E_Y.map.toRingHom
    (InfinitesimalThickening.Hom.kernel_map_mem f hx)))

/-- For `f : X → Y` there is a unique divided power morphism `ψ : D_X → D_Y` with
`ψ ∘ φ_X = φ_Y ∘ f`. -/
theorem existsUnique_comparison
    (f : InfinitesimalThickening.Hom X Y)
    (E_X : EnvelopeChoice (γ := γ) X)
    (E_Y : EnvelopeChoice (γ := γ) Y) :
    ∃! ψ : E_X.carrier →ₐ[A] E_Y.carrier,
      ψ.comp E_X.map = E_Y.map.comp f.toAlgHom ∧
        IsDPMorphism E_X.dividedPowers E_Y.dividedPowers ψ.toRingHom := by
  exact E_X.isEnvelope.isInitial E_Y.pdIdeal
    (E_Y.map.comp f.toAlgHom) E_Y.dividedPowers
    (target_ideal_le f E_Y) E_Y.isEnvelope.compat

/-- The comparison map `c(f) : D_X → D_Y` along a morphism `f : X → Y`
(`existsUnique_comparison`). -/
noncomputable def comparison
    (f : InfinitesimalThickening.Hom X Y)
    (E_X : EnvelopeChoice (γ := γ) X)
    (E_Y : EnvelopeChoice (γ := γ) Y) : E_X.carrier →ₐ[A] E_Y.carrier :=
  Classical.choose (existsUnique_comparison f E_X E_Y)

theorem comparison_spec
    (f : InfinitesimalThickening.Hom X Y)
    (E_X : EnvelopeChoice (γ := γ) X)
    (E_Y : EnvelopeChoice (γ := γ) Y) :
    (comparison f E_X E_Y).comp E_X.map = E_Y.map.comp f.toAlgHom ∧
      IsDPMorphism E_X.dividedPowers E_Y.dividedPowers
        (comparison f E_X E_Y).toRingHom := by
  exact (Classical.choose_spec (existsUnique_comparison f E_X E_Y)).1

/-- The comparison maps lie over `C`: `q_Y ∘ c(f) = q_X`. -/
theorem comparison_overC
    (f : InfinitesimalThickening.Hom X Y)
    (E_X : EnvelopeChoice (γ := γ) X)
    (E_Y : EnvelopeChoice (γ := γ) Y)
    (hIC : I.map (algebraMap A C) = ⊥) :
    (projection E_Y hIC).comp (comparison f E_X E_Y) =
      projection E_X hIC := by
  apply (existsUnique_projection E_X hIC).unique
  · constructor
    · calc
        ((projection E_Y hIC).comp (comparison f E_X E_Y)).comp E_X.map
            = (projection E_Y hIC).comp
                ((comparison f E_X E_Y).comp E_X.map) := by
                  rw [AlgHom.comp_assoc]
        _ = (projection E_Y hIC).comp (E_Y.map.comp f.toAlgHom) := by
              rw [(comparison_spec f E_X E_Y).1]
        _ = ((projection E_Y hIC).comp E_Y.map).comp f.toAlgHom := by
              rw [← AlgHom.comp_assoc]
        _ = Y.π.comp f.toAlgHom := by rw [(projection_spec E_Y hIC).1]
        _ = X.π := f.overC
    · exact DividedPowers.IsDPMorphism.comp _
        (projection_spec E_Y hIC).2 (comparison_spec f E_X E_Y).2
  · exact projection_spec E_X hIC

/-- `c(id) = id`. -/
theorem comparison_id
    (E : EnvelopeChoice (γ := γ) X) :
    comparison (𝟙 X) E E = AlgHom.id A E.carrier := by
  apply (existsUnique_comparison (𝟙 X) E E).unique
  · exact comparison_spec (𝟙 X) E E
  · constructor
    · change E.map = E.map.comp (AlgHom.id A X.carrier)
      simp
    · exact IsDPEnvelope.identity_spec E.map E.dividedPowers |>.2

/-- `c(g ∘ f) = c(g) ∘ c(f)`. -/
theorem comparison_comp
    (f : InfinitesimalThickening.Hom X Y)
    (g : InfinitesimalThickening.Hom Y Z)
    (E_X : EnvelopeChoice (γ := γ) X)
    (E_Y : EnvelopeChoice (γ := γ) Y)
    (E_Z : EnvelopeChoice (γ := γ) Z) :
    comparison (InfinitesimalThickening.Hom.comp f g) E_X E_Z =
      (comparison g E_Y E_Z).comp (comparison f E_X E_Y) := by
  apply (existsUnique_comparison (InfinitesimalThickening.Hom.comp f g) E_X E_Z).unique
  · exact comparison_spec (InfinitesimalThickening.Hom.comp f g) E_X E_Z
  · have hf := comparison_spec f E_X E_Y
    have hg := comparison_spec g E_Y E_Z
    constructor
    · rw [AlgHom.comp_assoc, hf.1, ← AlgHom.comp_assoc, hg.1]
      rfl
    · exact DividedPowers.IsDPMorphism.comp E_Z.dividedPowers hg.2 hf.2

/-- For two envelopes `E`, `F` of the same object, the comparison maps along the
identity satisfy `c_{F,E} ∘ c_{E,F} = id`. -/
theorem comparison_comp_comparison_left
    (X : InfinitesimalThickening A C)
    (E F : EnvelopeChoice (γ := γ) X) :
    (comparison (𝟙 X) F E).comp (comparison (𝟙 X) E F) =
      AlgHom.id A E.carrier := by
  have h := comparison_comp (𝟙 X) (𝟙 X) E F E
  rw [show InfinitesimalThickening.Hom.comp (𝟙 X) (𝟙 X) = 𝟙 X by rfl,
    comparison_id] at h
  exact h.symm

/-- For two envelopes `E`, `F` of the same object, the comparison maps along the
identity satisfy `c_{E,F} ∘ c_{F,E} = id`. -/
theorem comparison_comp_comparison_right
    (X : InfinitesimalThickening A C)
    (E F : EnvelopeChoice (γ := γ) X) :
    (comparison (𝟙 X) E F).comp (comparison (𝟙 X) F E) =
      AlgHom.id A F.carrier := by
  have h := comparison_comp (𝟙 X) (𝟙 X) F E F
  rw [show InfinitesimalThickening.Hom.comp (𝟙 X) (𝟙 X) = 𝟙 X by rfl,
    comparison_id] at h
  exact h.symm

/-- Comparison maps commute with changes of envelopes: for `f : X ⟶ Y` and
envelopes `E_X`, `F_X` of `X` and `E_Y`, `F_Y` of `Y`, both composites
`E_X → E_Y → F_Y` and `E_X → F_X → F_Y` are the comparison map along `f`. -/
theorem comparison_id_comp_comparison
    {X Y : InfinitesimalThickening A C} (f : X ⟶ Y) (E_X F_X : EnvelopeChoice (γ := γ) X)
    (E_Y F_Y : EnvelopeChoice (γ := γ) Y) :
    (comparison (𝟙 Y) E_Y F_Y).comp (comparison f E_X E_Y) =
      (comparison f F_X F_Y).comp (comparison (𝟙 X) E_X F_X) := by
  rw [← comparison_comp, ← comparison_comp]
  exact congrArg (comparison · E_X F_Y)
    ((Category.comp_id f).trans (Category.id_comp f).symm)

end EnvelopeChoice

end AffineCrystalline.InfinitesimalSite
