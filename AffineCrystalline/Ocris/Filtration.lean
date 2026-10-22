/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.Cohomology
import AffineCrystalline.InfinitesimalSite.Filtration
import AffineCrystalline.Cohomology.Cech
import Mathlib.CategoryTheory.Limits.Final

/-!
# `ocris` on the subcategories `INF^{(e)}`

The big infinitesimal site `INF(C/A)` is filtered by the full subcategories
`INF^{(e)}` (`Level A C e`) of thickenings of exponent `e`.  Fix a positive integer
`e` with `e! = 0` in `A`.  For a prime `p` and `e = p ^ f`, the level `INF^{(p ^ f)}`
is the Frobenius level denoted `INF_f` in the accompanying article, and the condition
reads `(p ^ f)! = 0` in `A`; it holds for `f = N` if `p ^ N = 0` in `A`
(`natCast_factorial_pow_eq_zero`).

* The truncation functor `T_e : INF(C/A) ⥤ INF^{(e)}` is left adjoint to the
  inclusion `INF^{(e)} → INF(C/A)` (`Level.truncationAdjunction`).  Restriction
  along a left adjoint preserves derived limits
  (`Cohomology.derivedLimitIsoOfAdjunction`), so the derived limit of a diagram
  `G` on `INF^{(e)}` is the derived limit on `INF(C/A)` of `G ∘ T_e`.
* Every element `x` of a divided power ideal of an `A`-algebra satisfies
  `x ^ e = e! • x^{[e]} = 0` (`dividedPowers_pow_eq_zero_of_factorial_eq_zero`).
  Hence a compatible divided power envelope of `T_e(X)` is an envelope of `X`
  (`EnvelopeChoice.truncate_isInitial`), and the maps
  `Ocris(X) → Ocris(T_e(X))` form a natural isomorphism
  (`EnvelopeFamily.ocrisTruncationIso`).
* Consequently the derived global sections of `ocris` on `INF(C/A)` and on
  `INF^{(e)}` agree (`ocrisDerivedGlobalSectionsIsoLevel`).
* `INF^{(e)}` carries the Čech nerve `X^{(e)}(•)` of its weakly initial object, so the
  derived global sections of `ocris` on `INF^{(e)}` are computed by the Čech
  complex `n ↦ Ocris(X^{(e)}(n))` (`ocrisCechZigzag`).
* `Ocris(X^{(e)}(n))` has the universal property of the PD envelope of the
  polynomial presentation `A[x_{i,c} : i ∈ [n], c ∈ C] → C`
  (`ocrisCech_isEnvelope`), so this Čech complex is a Čech–Alexander complex.

## Main definitions

* `Cohomology.derivedLimitIsoOfAdjunction`: derived limits are invariant under
  restriction along a left adjoint.
* `EnvelopeFamily.levelOcrisModule`, `EnvelopeFamily.levelOcrisDerivedGlobalSections`:
  `ocris` on `INF^{(e)}` and its derived global sections.
* `EnvelopeFamily.ocrisTruncationIso`: `Ocris ∘ T_e ≅ Ocris` if `e! = 0` in `A`.
* `EnvelopeFamily.ocrisDerivedGlobalSectionsIsoLevel`:
  `RΓ(INF(C/A), Ocris) ≅ RΓ(INF^{(e)}, Ocris)` if `e! = 0` in `A`.
* `Level.cechNerveData`: the Čech nerve of `INF^{(e)}`.
* `EnvelopeFamily.ocrisCechComplex`, `EnvelopeFamily.ocrisCechZigzag`: the Čech
  complex of `ocris` on `INF^{(e)}` and its comparison with `RΓ(INF^{(e)}, Ocris)`.

## Main results

* `EnvelopeChoice.truncate_isInitial`: the envelope of a truncation is an
  envelope of the original presentation.
* `EnvelopeChoice.comparison_toTruncate_bijective`: the comparison map
  `D_X → D_{T_e(X)}` is bijective.
* `EnvelopeFamily.ocrisCech_isEnvelope`: `Ocris(X^{(e)}(n))` is a PD envelope of
  `A[x_{i,c}] → C`.

## References

* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
* B. Bhatt, A. J. de Jong, *Crystalline cohomology and de Rham cohomology*,
  arXiv:1110.5001
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace AffineCrystalline.Cohomology

universe s r

/-- Derived limits are invariant under restriction along a left adjoint: for
`L ⊣ Rt` with `L : J ⥤ P`, `R lim_P G ≅ R lim_J (L ⋙ G)`.  The functor `L` is
initial, and restriction along `L` preserves injectives because it has the
exact left adjoint given by restriction along `Rt`. -/
noncomputable def derivedLimitIsoOfAdjunction
    {J P : Type (s + 1)} [Category.{s} J] [Category.{s} P]
    {R : Type r} [CommRing R] [Small.{s + 1} R]
    (L : J ⥤ P) (Rt : P ⥤ J) (adj : L ⊣ Rt) (G : P ⥤ ModuleCat.{s + 1} R) :
    ((lim : (P ⥤ ModuleCat.{s + 1} R) ⥤ ModuleCat.{s + 1} R).rightDerivedToHomotopyCategory).obj
        G ≅
      ((lim : (J ⥤ ModuleCat.{s + 1} R) ⥤ ModuleCat.{s + 1} R).rightDerivedToHomotopyCategory).obj
        (L ⋙ G) := by
  letI : Functor.Initial L := Functor.initial_of_adjunction adj
  let F := (Functor.whiskeringLeft J P (ModuleCat.{s + 1} R)).obj L
  let limJ := (lim : (J ⥤ ModuleCat.{s + 1} R) ⥤ ModuleCat.{s + 1} R)
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let hinj : ∀ (X : P ⥤ ModuleCat.{s + 1} R), Injective X → Injective (F.obj X) := by
    intro X hX
    exact injective_whiskeringLeft_obj_of_adjunction L Rt adj X
  let e : F ⋙ limJ ≅ (lim : (P ⥤ ModuleCat.{s + 1} R) ⥤ ModuleCat.{s + 1} R) :=
    Functor.Initial.limIso L
  exact ((additiveDerivedIso e).symm.app G) ≪≫
    rightDerivedToHomotopyCategoryCompIso F hinj limJ G

end AffineCrystalline.Cohomology

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

open InfinitesimalThickening

/-! ## Envelopes of truncations are envelopes of the presentation -/

section TruncationEnvelope

variable {B : Type u} [CommRing B] [Algebra A B]

/-- The kernel of the truncation `B / (x ^ e : x ∈ ker π) → C` is the image of
`ker π`. -/
theorem ker_truncate_eq_map (π : B →ₐ[A] C) (hπ : Function.Surjective π) (e : ℕ)
    (he0 : 0 < e) :
    RingHom.ker (truncate π hπ e he0).π.toRingHom =
      (RingHom.ker π.toRingHom).map (truncateMk π hπ e he0).toRingHom := by
  apply le_antisymm
  · intro y hy
    obtain ⟨b, rfl⟩ := truncateMk_surjective π hπ e he0 y
    have hb : b ∈ RingHom.ker π.toRingHom := hy
    exact Ideal.mem_map_of_mem _ hb
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact hb

/-- If `n! = 0` in `A`, an algebra map `φ' : B → D'` sending `ker π` into a divided
power ideal kills the truncation ideal `(x ^ n : x ∈ ker π)`, since every element of a
divided power ideal of an `A`-algebra has vanishing `n`-th power
(`dividedPowers_pow_eq_zero_of_factorial_eq_zero`). -/
theorem truncIdeal_le_ker_of_dividedPowers {n : ℕ} (hn : ((Nat.factorial n : ℕ) : A) = 0)
    (π : B →ₐ[A] C) {D' : Type u} [CommRing D'] [Algebra A D'] {K' : Ideal D'}
    (δ' : DividedPowers K') (φ' : B →ₐ[A] D')
    (hker : ∀ x ∈ RingHom.ker π.toRingHom, φ' x ∈ K') :
    truncIdeal π n ≤ RingHom.ker φ'.toRingHom :=
  powIdeal_le_ker φ'.toRingHom fun x hx ↦
    dividedPowers_pow_eq_zero_of_factorial_eq_zero hn δ' (hker x hx)

/-- **The envelope of a truncation is an envelope of the original presentation.**
If `n! = 0` in `A`, every compatible divided-power target kills the
`n`-th powers of `ker(B → C)`, so a compatible divided-power envelope of the
truncation `B / (x ^ n : x ∈ ker)` has the universal property of a
divided-power envelope of `(B, ker(B → C))` along the composite map. -/
theorem EnvelopeChoice.truncate_isInitial (π : B →ₐ[A] C) (hπ : Function.Surjective π)
    (n : ℕ) (hn0 : 0 < n) (hn : ((Nat.factorial n : ℕ) : A) = 0)
    (Ech : EnvelopeChoice (γ := γ) (truncate π hπ n hn0))
    {D' : Type u} [CommRing D'] [Algebra A D'] (K' : Ideal D') (φ' : B →ₐ[A] D')
    (δ' : DividedPowers K')
    (hK : (RingHom.ker π.toRingHom).map φ'.toRingHom ⊔ I.map (algebraMap A D') ≤ K')
    (hcompat : DividedPowers.IsDPMorphism γ δ' (algebraMap A D')) :
    ∃! ψ : Ech.carrier →ₐ[A] D',
      ψ.comp (Ech.map.comp (truncateMk π hπ n hn0)) = φ' ∧
        DividedPowers.IsDPMorphism Ech.dividedPowers δ' ψ.toRingHom := by
  have hkill := truncIdeal_le_ker_of_dividedPowers hn π δ' φ'
    fun x hx ↦ hK (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx))
  let φ'' : (truncate π hπ n hn0).carrier →ₐ[A] D' :=
    Ideal.Quotient.liftₐ (truncIdeal π n) φ' fun b hb ↦ hkill hb
  have hφ'' : φ''.comp (truncateMk π hπ n hn0) = φ' := AlgHom.ext fun _ ↦ rfl
  have hK'' : (RingHom.ker (truncate π hπ n hn0).π.toRingHom).map φ''.toRingHom ⊔
      I.map (algebraMap A D') ≤ K' := by
    rwa [ker_truncate_eq_map, Ideal.map_map, show φ''.toRingHom.comp
      (truncateMk π hπ n hn0).toRingHom = φ'.toRingHom from congrArg AlgHom.toRingHom hφ'']
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, huniq⟩ := Ech.isEnvelope.isInitial K' φ'' δ' hK'' hcompat
  refine ⟨ψ, ⟨?_, hψ2⟩, fun ψ' ⟨hψ'1, hψ'2⟩ ↦ huniq ψ' ⟨?_, hψ'2⟩⟩
  · rw [← AlgHom.comp_assoc, hψ1, hφ'']
  · refine (AlgHom.cancel_right (truncateMk_surjective π hπ n hn0)).1 ?_
    rw [AlgHom.comp_assoc, hψ'1, hφ'']

/-- **Envelopes are invariant under truncation.** If `n! = 0` in `A`,
the comparison map `D_X → D_{T_n(X)}` along the quotient map `X → T_n(X)` is
bijective; its inverse is the divided power morphism given by
`EnvelopeChoice.truncate_isInitial`. -/
theorem EnvelopeChoice.comparison_toTruncate_bijective (X : InfinitesimalThickening A C)
    (n : ℕ) (hn0 : 0 < n) (hn : ((Nat.factorial n : ℕ) : A) = 0)
    (E_X : EnvelopeChoice (γ := γ) X)
    (E_T : EnvelopeChoice (γ := γ) (truncate X.π X.surjective n hn0)) :
    Function.Bijective (comparison (toTruncate X n hn0) E_X E_T) := by
  obtain ⟨ψ, ⟨hψ, hψDP⟩, -⟩ := truncate_isInitial X.π X.surjective n hn0 hn E_T
    E_X.pdIdeal E_X.map E_X.dividedPowers E_X.isEnvelope.le E_X.isEnvelope.compat
  set c := comparison (toTruncate X n hn0) E_X E_T
  have hc := comparison_spec (toTruncate X n hn0) E_X E_T
  have hψc : ψ.comp c = AlgHom.id A E_X.carrier := by
    refine E_X.isEnvelope.algHom_ext (DividedPowers.IsDPMorphism.comp _ hψDP hc.2)
      (IsDPEnvelope.identity_spec E_X.map E_X.dividedPowers).2 ?_
    rw [AlgHom.comp_assoc, hc.1]
    exact hψ.trans (AlgHom.id_comp _).symm
  have hcψ : c.comp ψ = AlgHom.id A E_T.carrier := by
    refine E_T.isEnvelope.algHom_ext (DividedPowers.IsDPMorphism.comp _ hc.2 hψDP)
      (IsDPEnvelope.identity_spec E_T.map E_T.dividedPowers).2 ?_
    refine (AlgHom.cancel_right (truncateMk_surjective X.π X.surjective n hn0)).1
      (AlgHom.ext fun b ↦ ?_)
    have h₁ : ψ (E_T.map (truncateMk X.π X.surjective n hn0 b)) = E_X.map b :=
      DFunLike.congr_fun hψ b
    have h₂ : c (E_X.map b) = E_T.map (truncateMk X.π X.surjective n hn0 b) :=
      DFunLike.congr_fun hc.1 b
    change c (ψ (E_T.map (truncateMk X.π X.surjective n hn0 b))) = _
    rw [h₁, h₂]
    rfl
  exact Function.bijective_iff_has_inverse.2
    ⟨ψ, fun x ↦ DFunLike.congr_fun hψc x, fun y ↦ DFunLike.congr_fun hcψ y⟩

end TruncationEnvelope

/-! ## `ocris` on `INF^{(e)}` -/

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))

/-- The `ocris` module diagram on `INF^{(e)}`: the restriction of `ocrisModuleLarge`
along the inclusion `INF^{(e)} → INF(C/A)`. The arguments `p` and `_hIC` record the
crystalline setting (`p` nilpotent in `A`, `I C = 0`) in which this diagram is
studied; they do not enter the definition. -/
noncomputable def levelOcrisModule (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
    (_hIC : I.map (algebraMap A C) = ⊥) (e : ℕ) : Level A C e ⥤ ModuleCat.{u + 1} A :=
  Level.ι e ⋙ CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E

section Level

variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
variable (hIC : I.map (algebraMap A C) = ⊥) (e : ℕ)

/-- `levelOcrisModule` is the restriction of `ocrisModuleLarge` to `INF^{(e)}`. -/
theorem levelOcrisModule_eq :
    E.levelOcrisModule p hIC e =
      Level.ι e ⋙ CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E :=
  rfl

/-- The derived global sections `RΓ(INF^{(e)}, Ocris)`, the right-derived limit of
`ocris` on `INF^{(e)}`. -/
noncomputable def levelOcrisDerivedGlobalSections :
    HomotopyCategory (ModuleCat.{u + 1} A) (ComplexShape.up ℕ) :=
  ((lim : (Level A C e ⥤ ModuleCat.{u + 1} A) ⥤
      ModuleCat.{u + 1} A).rightDerivedToHomotopyCategory).obj (E.levelOcrisModule p hIC e)

end Level

/-- If `n! = 0` in `A`, the map `Ocris(X) → Ocris(T_n(X))` induced by the quotient
map `X → T_n(X)` is an isomorphism. -/
theorem isIso_ocrisModuleLarge_map_toTruncate (n : ℕ) [NeZero n]
    (hn : ((Nat.factorial n : ℕ) : A) = 0) (X : InfinitesimalThickening A C) :
    IsIso ((CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E).map
      (toTruncate X n (NeZero.pos n))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Equiv.ulift.symm.bijective.comp
    ((EnvelopeChoice.comparison_toTruncate_bijective X n (NeZero.pos n) hn _ _).comp
      Equiv.ulift.bijective)

/-- **`ocris` is invariant under truncation.** If `n! = 0` in `A`, the maps
`Ocris(X) → Ocris(T_n(X))` induced by the quotient maps `X → T_n(X)`, that is, by
the unit of the truncation adjunction, form a natural isomorphism between the
restriction of `ocris` along `T_n ⋙ ι_n : INF(C/A) ⥤ INF(C/A)` and `ocris`. -/
noncomputable def ocrisTruncationIso (n : ℕ) [NeZero n]
    (hn : ((Nat.factorial n : ℕ) : A) = 0) :
    Level.truncation n ⋙ Level.ι n ⋙ CategoryTheory.opOp (InfinitesimalThickening A C) ⋙
        ocrisModuleLarge E ≅
      CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E :=
  haveI : ∀ X, IsIso ((Functor.whiskerRight (Level.truncationAdjunction n).unit
      (CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E)).app X) :=
    E.isIso_ocrisModuleLarge_map_toTruncate n hn
  haveI : IsIso (Functor.whiskerRight (Level.truncationAdjunction n).unit
      (CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E)) :=
    NatIso.isIso_of_isIso_app _
  (asIso (Functor.whiskerRight (Level.truncationAdjunction n).unit
    (CategoryTheory.opOp (InfinitesimalThickening A C) ⋙ ocrisModuleLarge E))).symm

variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
variable (hIC : I.map (algebraMap A C) = ⊥)
variable (n : ℕ) [NeZero n] (hn : ((Nat.factorial n : ℕ) : A) = 0)

/-- **Restriction to `INF^{(n)}`.**  If `n! = 0` in `A`,
`RΓ(INF(C/A), Ocris) ≅ RΓ(INF^{(n)}, Ocris)`.  Restriction along the truncation
functor `T_n`, which is left adjoint to the inclusion `INF^{(n)} → INF(C/A)`,
preserves derived limits (`Cohomology.derivedLimitIsoOfAdjunction`), and the
restriction of `ocris` along `T_n` is `ocris` itself (`ocrisTruncationIso`). -/
noncomputable def ocrisDerivedGlobalSectionsIsoLevel :
    ocrisDerivedGlobalSections E ≅ E.levelOcrisDerivedGlobalSections p hIC n :=
  ((lim : (InfinitesimalThickening A C ⥤ ModuleCat.{u + 1} A) ⥤
      ModuleCat.{u + 1} A).rightDerivedToHomotopyCategory.mapIso
        (E.ocrisTruncationIso n hn)).symm ≪≫
    (Cohomology.derivedLimitIsoOfAdjunction (Level.truncation n) (Level.ι n)
      (Level.truncationAdjunction n) (E.levelOcrisModule p hIC n)).symm

end EnvelopeFamily

/-! ## The Čech nerve of `INF^{(e)}` -/

namespace Level

variable (e : ℕ) [NeZero e]

/-- The Čech nerve data of `INF^{(e)}`: `X^{(e)}(n)` corepresents `(n+1)`-tuples of
sections, and every object has a section. -/
noncomputable def cechNerveData : Cohomology.Cech.CechNerveData (Level A C e) where
  X := cechNerve e
  S Z := Z.obj.Sections
  nonempty Z := Z.obj.sections_nonempty
  equiv n Z := cechHomEquiv n Z
  equiv_map f Z g := cechHomEquiv_cechMap f.toOrderHom Z g

end Level

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
variable (hIC : I.map (algebraMap A C) = ⊥)
variable (e : ℕ) [NeZero e]

/-- The Čech complex `n ↦ Ocris(X^{(e)}(n))` of the `ocris` diagram on `INF^{(e)}`. -/
noncomputable def ocrisCechComplex : CochainComplex (ModuleCat.{u + 1} A) ℕ :=
  Cohomology.Cech.cech (Level.cechNerveData e) (E.levelOcrisModule p hIC e)

/-- The `n`-th term of the Čech complex is `Ocris(X^{(e)}(n))`. -/
theorem ocrisCechComplex_X (n : ℕ) :
    (E.ocrisCechComplex p hIC e).X n =
      ModuleCat.of A (ULift.{u + 1, u} (E.envelope (Level.cechObj e n).obj).carrier) :=
  rfl

/-- **Čech computation of `ocris` cohomology on `INF^{(e)}`.**  The complex
`lim I^•` computing the derived global sections of `ocris` on `INF^{(e)}`
(for the chosen injective resolution `I^•`) and the Čech complex
`n ↦ Ocris(X^{(e)}(n))` are connected by an explicit zigzag of
quasi-isomorphisms. -/
noncomputable def ocrisCechZigzag :
    Cohomology.Cech.Zigzag
      (Cohomology.Cech.limComplex (injectiveResolution (E.levelOcrisModule p hIC e)))
      (E.ocrisCechComplex p hIC e) :=
  Cohomology.Cech.cechZigzag (Level.cechNerveData e)
    (injectiveResolution (E.levelOcrisModule p hIC e))

/-- The derived global sections on `INF^{(e)}` are represented by the complex
`lim I^•` of the chosen injective resolution `I^•`. -/
noncomputable def levelOcrisDerivedGlobalSectionsIsoLimComplex :
    E.levelOcrisDerivedGlobalSections p hIC e ≅
      (HomotopyCategory.quotient (ModuleCat.{u + 1} A) (ComplexShape.up ℕ)).obj
        (Cohomology.Cech.limComplex (injectiveResolution (E.levelOcrisModule p hIC e))) :=
  (injectiveResolution (E.levelOcrisModule p hIC e)).isoRightDerivedToHomotopyCategoryObj _

end EnvelopeFamily


namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))

/-- **The Čech complex of `ocris` is a Čech–Alexander complex.**  If
`e! = 0` in `A`, the value of `ocris` at the `n`-th Čech object of `INF^{(e)}` is
a compatible divided-power envelope of the polynomial presentation
`A[x_{i,c} : i ∈ [n], c ∈ C] → C`: it has the universal property of the
envelope along the composite map. -/
theorem ocrisCech_isEnvelope (e : ℕ) [NeZero e] (he : ((Nat.factorial e : ℕ) : A) = 0)
    (n : ℕ)
    {D' : Type u} [CommRing D'] [Algebra A D'] (K' : Ideal D')
    (φ' : MvPolynomial (Fin (n + 1) × C) A →ₐ[A] D') (δ' : DividedPowers K')
    (hK : (RingHom.ker (cechπ (A := A) (C := C) n).toRingHom).map φ'.toRingHom ⊔
      I.map (algebraMap A D') ≤ K')
    (hcompat : DividedPowers.IsDPMorphism γ δ' (algebraMap A D')) :
    ∃! ψ : (E.envelope (Level.cechObj e n).obj).carrier →ₐ[A] D',
      ψ.comp ((E.envelope (Level.cechObj e n).obj).map.comp (Level.cechMk e n)) = φ' ∧
        DividedPowers.IsDPMorphism (E.envelope (Level.cechObj e n).obj).dividedPowers δ'
          ψ.toRingHom :=
  EnvelopeChoice.truncate_isInitial (cechπ n) (cechπ_surjective n) e (NeZero.pos e)
    he (E.envelope (Level.cechObj e n).obj) K' φ' δ' hK hcompat

end EnvelopeFamily

end AffineCrystalline.InfinitesimalSite
