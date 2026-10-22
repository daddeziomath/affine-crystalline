/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.Cohomology
import AffineCrystalline.DeRham
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.Single

/-!
# Functoriality of the PD de Rham complex and the de Rham complex of `ocris`

Let `f : (B, J, δ_B) → (D, K, δ_D)` be a morphism of `A`-algebras compatible
with divided powers.  We construct the induced maps on PD differentials
`Ω_{B,δ_B} → Ω_{D,δ_D}` (`pdKaehlerMap`), on their exterior powers
(`pdExteriorMap`), and the induced cochain map of PD de Rham complexes
`Ω^•_{B,δ_B} → Ω^•_{D,δ_D}` (`pdDeRhamMap`), and prove functoriality.  The
proofs use that each `Ω^n` is spanned over `A` by the elements
`b₀ db₁ ∧ ⋯ ∧ dbₙ` (`riouSourceGenerator_span`).

Applied to envelopes, this gives the functor
`X ↦ Ω^•_{Ocris(X)}` on `INF(C/A)` (`ocrisDeRhamComplex`), whose transition
maps are induced by the comparison maps of the universal property, together
with the augmentation `Ω^•_{Ocris(X)} → Ocris(X)` (`ocrisDeRhamAugmentation`).

## Main definitions

* `DeRham.pdKaehlerMap`, `DeRham.pdExteriorMap`, `DeRham.pdDeRhamMap`: the maps
  induced by a PD morphism on PD differentials, PD forms and PD de Rham
  complexes.
* `EnvelopeFamily.envelopeDeRhamMap`: the cochain map between PD de Rham
  complexes of envelopes induced by a morphism of thickenings.
* `EnvelopeFamily.ocrisDeRhamComplex`: the functor `X ↦ Ω^•_{Ocris(X)}`.
* `EnvelopeFamily.ocrisModuleLargeOnThickening`,
  `EnvelopeFamily.ocrisComplexOnThickening`: `ocris` as a covariant functor on
  thickenings.
* `EnvelopeFamily.ocrisDeRhamAugmentation`: the augmentation
  `Ω^•_{Ocris(X)} → Ocris(X)[0]`.
* `EnvelopeFamily.ocrisDeRhamComplexIso`: independence of the envelope family.

## Main results

* `DeRham.riouSourceGenerator_span`: the forms `b₀ db₁ ∧ ⋯ ∧ dbₙ` span `Ω^n`.
* `DeRham.pdTerm_linearMap_ext`: linear maps out of `Ω^n_{B,δ_B}` are determined
  by their values on the forms `b₀ db₁ ∧ ⋯ ∧ dbₙ`.
* `DeRham.pdExteriorMap_id`, `DeRham.pdExteriorMap_comp`: functoriality.
* `DeRham.pdDeRhamComplex_d_generator`:
  `d(b₀ db₁ ∧ ⋯ ∧ dbₙ) = db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ`.
* `DeRham.pdExteriorMap_d_naturality`: the induced maps commute with `d`.
* `DeRham.zeroEquiv_comp_pdExteriorMap_zero`: in degree zero the induced map is `f`.

## References

* [Stacks Project, Tag 07HQ](https://stacks.math.columbia.edu/tag/07HQ)
-/

open CategoryTheory
open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B D : Type u}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra A D]
variable {J : Ideal B} {K : Ideal D}

/-- Let `D` be a `B`-algebra such that `B → D` is a PD morphism. Then the composite
`B → D → Ω_{D,δ_D}` of the structure map with the universal PD derivation is a
PD derivation. -/
theorem isPDDerivation_pdD_comp_algebraMap [Algebra B D] [IsScalarTower A B D]
    (deltaB : DividedPowers J) (deltaD : DividedPowers K)
    (hf : IsDPMorphism deltaB deltaD (algebraMap B D)) :
    IsPDDerivation deltaB (PDKaehler (A := A) deltaD)
      ((pdD deltaD).comp (IsScalarTower.toAlgHom A B D).toLinearMap) where
  leibniz b b' := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      map_mul, (pdD_isPDDerivation deltaD).leibniz, algebraMap_smul]
  dpow n hn b hb := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
    rw [← hf.dpow_comp b hb, ← algebraMap_smul D, ← hf.dpow_comp b hb]
    exact (pdD_isPDDerivation deltaD).dpow n hn _
      (hf.ideal_comp (Ideal.mem_map_of_mem _ hb))

/-- The map `Ω_{B,δ_B} → Ω_{D,δ_D}` on PD differentials induced by an
`A`-algebra map compatible with divided powers. -/
noncomputable def pdKaehlerMap (deltaB : DividedPowers J)
    (deltaD : DividedPowers K) (f : B →ₐ[A] D)
    (hf : IsDPMorphism deltaB deltaD f.toRingHom) :
    PDKaehler (A := A) deltaB →ₗ[A] PDKaehler (A := A) deltaD := by
  letI : Algebra B D := f.toRingHom.toAlgebra
  letI : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  let theta : B →ₗ[A] PDKaehler (A := A) deltaD :=
    (pdD deltaD).comp f.toLinearMap
  have htheta : IsPDDerivation deltaB (PDKaehler (A := A) deltaD) theta :=
    isPDDerivation_pdD_comp_algebraMap deltaB deltaD hf
  exact (PDKaehler.lift deltaB (PDKaehler (A := A) deltaD) theta htheta).restrictScalars A

@[simp]
theorem pdKaehlerMap_pdD (deltaB : DividedPowers J)
    (deltaD : DividedPowers K) (f : B →ₐ[A] D)
    (hf : IsDPMorphism deltaB deltaD f.toRingHom) (b : B) :
    pdKaehlerMap deltaB deltaD f hf (pdD deltaB b) =
      pdD deltaD (f b) := by
  simp [pdKaehlerMap, PDKaehler.lift, pdD_apply,
    IsPDDerivation.toDerivation]

/-- The map `Ω^n_{B,δ_B} → Ω^n_{D,δ_D}` on PD `n`-forms induced by a
divided-power morphism.  The source exterior power is formed over `B` and the
target over `D`; the result is an `A`-linear map. -/
noncomputable def pdExteriorMap (deltaB : DividedPowers J)
    (deltaD : DividedPowers K) (f : B →ₐ[A] D)
    (hf : IsDPMorphism deltaB deltaD f.toRingHom) (n : ℕ) :
    PDTerm (A := A) deltaB n →ₗ[A] PDTerm (A := A) deltaD n := by
  letI : Algebra B D := f.toRingHom.toAlgebra
  letI : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  let theta : B →ₗ[A] PDKaehler (A := A) deltaD :=
    (pdD deltaD).comp f.toLinearMap
  have htheta : IsPDDerivation deltaB (PDKaehler (A := A) deltaD) theta :=
    isPDDerivation_pdD_comp_algebraMap deltaB deltaD hf
  let oneForms : PDKaehler (A := A) deltaB →ₗ[B]
      PDKaehler (A := A) deltaD :=
    PDKaehler.lift deltaB (PDKaehler (A := A) deltaD) theta htheta
  let targetAltB : (PDKaehler (A := A) deltaD) [⋀^Fin n]→ₗ[B]
      PDTerm (A := A) deltaD n :=
    { toMultilinearMap :=
        (exteriorPower.ιMulti D n).toMultilinearMap.restrictScalars B
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact (exteriorPower.ιMulti D n).map_eq_zero_of_eq v hv hij }
  let sourceAlt : (PDKaehler (A := A) deltaB) [⋀^Fin n]→ₗ[B]
      PDTerm (A := A) deltaD n :=
    targetAltB.compLinearMap oneForms
  exact (exteriorPower.alternatingMapLinearEquiv sourceAlt).restrictScalars A

@[simp]
theorem pdExteriorMap_ιMulti (deltaB : DividedPowers J)
    (deltaD : DividedPowers K) (f : B →ₐ[A] D)
    (hf : IsDPMorphism deltaB deltaD f.toRingHom) (n : ℕ)
    (v : Fin n → PDKaehler (A := A) deltaB) :
    pdExteriorMap deltaB deltaD f hf n (exteriorPower.ιMulti B n v) =
      exteriorPower.ιMulti D n
        (fun i ↦ pdKaehlerMap deltaB deltaD f hf (v i)) := by
  simp only [pdExteriorMap, LinearMap.coe_restrictScalars,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    pdKaehlerMap]
  rfl

theorem pdExteriorMap_smul (deltaB : DividedPowers J)
    (deltaD : DividedPowers K) (f : B →ₐ[A] D)
    (hf : IsDPMorphism deltaB deltaD f.toRingHom) (n : ℕ)
    (b : B) (x : PDTerm (A := A) deltaB n) :
    pdExteriorMap deltaB deltaD f hf n (b • x) =
      f b • pdExteriorMap deltaB deltaD f hf n x := by
  letI : Algebra B D := f.toRingHom.toAlgebra
  simp only [pdExteriorMap, LinearMap.coe_restrictScalars, map_smul]
  change (algebraMap B D b : D) •
      (pdExteriorMap deltaB deltaD f hf n x) =
    (f b : D) • pdExteriorMap deltaB deltaD f hf n x
  rfl

@[simp]
theorem pdExteriorMap_generator (deltaB : DividedPowers J)
    (deltaD : DividedPowers K) (f : B →ₐ[A] D)
    (hf : IsDPMorphism deltaB deltaD f.toRingHom) (n : ℕ)
    (b : B) (g : Fin n → B) :
    pdExteriorMap deltaB deltaD f hf n
        (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g)) =
      f b • exteriorPower.ιMulti D n (fun i ↦ pdD deltaD (f (g i))) := by
  rw [pdExteriorMap_smul, pdExteriorMap_ιMulti]
  apply congrArg (fun z : PDTerm (A := A) deltaD n ↦ (f b : D) • z)
  apply congrArg (exteriorPower.ιMulti D n)
  funext i
  simpa using pdKaehlerMap_pdD deltaB deltaD f hf (g i)

@[simp]
theorem pdTermMap_sourceGenerator (deltaB : DividedPowers J) (n : ℕ)
    (b : B) (g : Fin n → B) :
    pdTermMap (A := A) deltaB n
        (RiouPresentation.sourceGenerator (A := A) (B := B) n b g) =
      b • exteriorPower.ιMulti B n (pdD deltaB ∘ g) := by
  simp only [pdTermMap, pdTermMapB, RiouPresentation.sourceGenerator,
    LinearMap.coe_restrictScalars, map_smul, exteriorPower.map_apply_ιMulti]
  congr 1

private theorem riouSourceGeneratorSpanA_smul (n : ℕ) (c : B)
    {w : OrdinaryTerm (A := A) (B := B) n}
    (hw : w ∈ Submodule.span A
      (Set.range fun p : B × (Fin n → B) ↦
        RiouPresentation.sourceGenerator (A := A) (B := B) n p.1 p.2)) :
    c • w ∈ Submodule.span A
      (Set.range fun p : B × (Fin n → B) ↦
        RiouPresentation.sourceGenerator (A := A) (B := B) n p.1 p.2) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      rcases hw with ⟨⟨b, g⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨c * b, g⟩, ?_⟩
      simp [RiouPresentation.sourceGenerator, mul_smul]
  | zero => simp
  | add x y _ _ hx hy => simpa [smul_add] using add_mem hx hy
  | smul a x _ hx =>
      rw [smul_comm c a]
      exact Submodule.smul_mem _ a hx

/-- The generators `b₀ db₁ ∧ ⋯ ∧ dbₙ` span each term of the ordinary de Rham
complex as an `A`-module. -/
theorem riouSourceGenerator_span (n : ℕ) :
    Submodule.span A
      (Set.range fun p : B × (Fin n → B) ↦
        RiouPresentation.sourceGenerator (A := A) (B := B) n p.1 p.2) = ⊤ := by
  let P := DeRhamComplex.presentationDifferentialsUp A B n
  let S : Submodule A (OrdinaryTerm (A := A) (B := B) n) :=
    Submodule.span A (Set.range fun p : B × (Fin n → B) ↦
      RiouPresentation.sourceGenerator (A := A) (B := B) n p.1 p.2)
  have hspanB : Submodule.span B (Set.range P.var) = ⊤ := by
    rw [← P.toSolution.range_π]
    exact LinearMap.range_eq_top.2 P.toIsPresentation.surjective_π
  have hcontained (w : OrdinaryTerm (A := A) (B := B) n)
      (hw : w ∈ Submodule.span B (Set.range P.var)) : w ∈ S := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨g, rfl⟩
      rw [DeRhamComplex.presentationDifferentialsUp_var]
      apply Submodule.subset_span
      refine ⟨⟨1, g⟩, ?_⟩
      simp [RiouPresentation.sourceGenerator]
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul c x _ hx => exact riouSourceGeneratorSpanA_smul (A := A) n c hx
  change S = ⊤
  apply le_antisymm
  · exact le_top
  · intro w _
    apply hcontained
    rw [hspanB]
    exact Submodule.mem_top

/-- Two `A`-linear maps out of `Ω^n_{B,δ_B}` which agree on the generators
`b₀ db₁ ∧ ⋯ ∧ dbₙ` are equal. -/
theorem pdTerm_linearMap_ext (deltaB : DividedPowers J) {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} {F G : PDTerm (A := A) deltaB n →ₗ[A] M}
    (hgen : ∀ (b : B) (g : Fin n → B),
      F (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g)) =
        G (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g))) :
    F = G := by
  refine (LinearMap.cancel_right (pdTermMap_surjective (A := A) (B := B) deltaB n)).1 ?_
  refine LinearMap.ext_on_range (riouSourceGenerator_span (A := A) (B := B) n) fun p ↦ ?_
  simpa only [LinearMap.comp_apply, pdTermMap_sourceGenerator] using hgen p.1 p.2

private theorem pdTermMap_ext_of_riou_generators
    (deltaB : DividedPowers J) {E : Type u} [CommRing E] [Algebra A E]
    {L : Ideal E} (deltaE : DividedPowers L) (n : ℕ)
    (F G : PDTerm (A := A) deltaB n →ₗ[A]
      PDTerm (A := A) deltaE n)
    (hgen : ∀ (b : B) (g : Fin n → B),
      F (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g)) =
        G (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g))) :
    F = G :=
  pdTerm_linearMap_ext deltaB hgen

/-- The identity PD morphism induces the identity on PD forms in every
degree. -/
theorem pdExteriorMap_id (deltaB : DividedPowers J)
    (hf : IsDPMorphism deltaB deltaB (AlgHom.id A B).toRingHom) (n : ℕ) :
    pdExteriorMap deltaB deltaB (AlgHom.id A B) hf n = LinearMap.id := by
  apply pdTermMap_ext_of_riou_generators (A := A) (B := B)
    deltaB deltaB n _ _
  intro b g
  simpa [AlgHom.id_apply, Function.comp_def] using
    pdExteriorMap_generator deltaB deltaB (AlgHom.id A B) hf n b g

/-- The maps on PD forms respect composition of PD morphisms. -/
theorem pdExteriorMap_comp
    (deltaB : DividedPowers J) {D : Type u} [CommRing D] [Algebra A D]
    {K : Ideal D} (deltaD : DividedPowers K)
    {E : Type u} [CommRing E] [Algebra A E] {L : Ideal E}
    (deltaE : DividedPowers L)
    (f : B →ₐ[A] D) (hf : IsDPMorphism deltaB deltaD f.toRingHom)
    (g : D →ₐ[A] E) (hg : IsDPMorphism deltaD deltaE g.toRingHom)
    (n : ℕ) :
    (pdExteriorMap deltaD deltaE g hg n).comp
        (pdExteriorMap deltaB deltaD f hf n) =
      pdExteriorMap deltaB deltaE (g.comp f)
        (DividedPowers.IsDPMorphism.comp deltaE hg hf) n := by
  apply pdTermMap_ext_of_riou_generators (A := A) (B := B)
    deltaB deltaE n _ _
  intro b h
  have hinner : pdExteriorMap deltaB deltaD f hf n
      (b • exteriorPower.ιMulti B n (pdD deltaB ∘ h)) =
      f b • exteriorPower.ιMulti D n (pdD deltaD ∘ fun i ↦ f (h i)) := by
    simpa [Function.comp_def] using
      pdExteriorMap_generator deltaB deltaD f hf n b h
  have hcomposite := pdExteriorMap_generator deltaB deltaE (g.comp f)
    (DividedPowers.IsDPMorphism.comp deltaE hg hf) n b h
  calc
    (pdExteriorMap deltaD deltaE g hg n).comp
        (pdExteriorMap deltaB deltaD f hf n)
        (b • exteriorPower.ιMulti B n (pdD deltaB ∘ h)) =
      pdExteriorMap deltaD deltaE g hg n
        (f b • exteriorPower.ιMulti D n (pdD deltaD ∘ fun i ↦ f (h i))) := by
          rw [LinearMap.comp_apply, hinner]
    _ = g (f b) • exteriorPower.ιMulti E n
          (fun i ↦ pdD deltaE (g (f (h i)))) := by
          simpa [Function.comp_def] using
            pdExteriorMap_generator deltaD deltaE g hg n (f b)
              (fun i ↦ f (h i))
    _ = pdExteriorMap deltaB deltaE (g.comp f)
          (DividedPowers.IsDPMorphism.comp deltaE hg hf) n
          (b • exteriorPower.ιMulti B n (pdD deltaB ∘ h)) := by
          simpa [AlgHom.comp_apply] using hcomposite.symm

/-- The PD de Rham differential on generators:
`d(b₀ db₁ ∧ ⋯ ∧ dbₙ) = db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ`. -/
theorem pdDeRhamComplex_d_generator (deltaB : DividedPowers J) (n : ℕ)
    (b : B) (g : Fin n → B) :
    ((pdDeRhamComplex (A := A) deltaB).d n (n + 1)).hom
        (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g)) =
      exteriorPower.ιMulti B (n + 1)
        (pdD deltaB ∘ RiouPresentation.finInsert b g) := by
  let x := RiouPresentation.sourceGenerator (A := A) (B := B) n b g
  have hdesc := descendLinearMap_comp
    (quotientTermMap (A := A) (pdRelations (A := A) deltaB) n)
    (quotientTermMap (A := A) (pdRelations (A := A) deltaB) (n + 1) ∘ₗ
      DeRhamComplex.d A B n)
    (quotientTermMap_surjective (A := A) (pdRelations (A := A) deltaB) n)
    (pdQuotientRelationStable deltaB n)
  have happ := LinearMap.congr_fun hdesc x
  rw [LinearMap.comp_apply] at happ
  rw [← pdTermMap_sourceGenerator deltaB n b g]
  simp only [pdDeRhamComplex, deRhamComplexOfQuotient, CochainComplex.of_d]
  change descendLinearMap
      (quotientTermMap (A := A) (pdRelations (A := A) deltaB) n)
      (quotientTermMap (A := A) (pdRelations (A := A) deltaB) (n + 1) ∘ₗ
        DeRhamComplex.d A B n)
      (quotientTermMap_surjective (A := A) (pdRelations (A := A) deltaB) n)
      (pdQuotientRelationStable deltaB n)
      (quotientTermMap (A := A) (pdRelations (A := A) deltaB) n x) = _
  rw [happ, LinearMap.comp_apply, DeRhamComplex.d_sourceGenerator, quotientTermMap,
    LinearMap.restrictScalars_apply, RiouPresentation.targetGenerator,
    exteriorPower.map_apply_ιMulti]
  congr 1

/-- The map induced by a PD morphism `f` sends `db₁ ∧ ⋯ ∧ dbₙ` to
`df(b₁) ∧ ⋯ ∧ df(bₙ)`. -/
theorem pdExteriorMap_ιMulti_pdD (deltaB : DividedPowers J) (deltaD : DividedPowers K)
    (f : B →ₐ[A] D) (hf : IsDPMorphism deltaB deltaD f.toRingHom) (n : ℕ) (g : Fin n → B) :
    pdExteriorMap deltaB deltaD f hf n (exteriorPower.ιMulti B n (pdD deltaB ∘ g)) =
      exteriorPower.ιMulti D n (pdD deltaD ∘ f ∘ g) := by
  rw [pdExteriorMap_ιMulti]
  exact congrArg (exteriorPower.ιMulti D n) (funext fun i ↦ pdKaehlerMap_pdD _ _ _ _ (g i))

/-- The maps on PD forms induced by a PD morphism commute with the PD de Rham
differentials. -/
theorem pdExteriorMap_d_naturality
    (deltaB : DividedPowers J) {E : Type u} [CommRing E] [Algebra A E]
    {L : Ideal E} (deltaE : DividedPowers L)
    (f : B →ₐ[A] E) (hf : IsDPMorphism deltaB deltaE f.toRingHom)
    (n : ℕ) :
    ((pdDeRhamComplex (A := A) deltaE).d n (n + 1)).hom ∘ₗ
        pdExteriorMap deltaB deltaE f hf n =
      pdExteriorMap deltaB deltaE f hf (n + 1) ∘ₗ
        ((pdDeRhamComplex (A := A) deltaB).d n (n + 1)).hom := by
  refine pdTerm_linearMap_ext deltaB fun b g ↦ ?_
  have hfin : ⇑f ∘ RiouPresentation.finInsert b g =
      RiouPresentation.finInsert (f b) (⇑f ∘ g) := by
    funext i
    induction i using Fin.cases <;> rfl
  change ((pdDeRhamComplex (A := A) deltaE).d n (n + 1)).hom
      (pdExteriorMap deltaB deltaE f hf n (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g))) =
    pdExteriorMap deltaB deltaE f hf (n + 1)
      (((pdDeRhamComplex (A := A) deltaB).d n (n + 1)).hom
        (b • exteriorPower.ιMulti B n (pdD deltaB ∘ g)))
  rw [pdExteriorMap_generator, pdDeRhamComplex_d_generator, pdExteriorMap_ιMulti_pdD, hfin]
  exact pdDeRhamComplex_d_generator deltaE n (f b) (⇑f ∘ g)

/-- The cochain map `Ω^•_{B,δ_B} → Ω^•_{E,δ_E}` of PD de Rham complexes induced
by a PD morphism. -/
noncomputable def pdDeRhamMap
    (deltaB : DividedPowers J) {E : Type u} [CommRing E] [Algebra A E]
    {L : Ideal E} (deltaE : DividedPowers L)
    (f : B →ₐ[A] E) (hf : IsDPMorphism deltaB deltaE f.toRingHom) :
    pdDeRhamComplex (A := A) deltaB ⟶
      pdDeRhamComplex (A := A) (B := E) deltaE where
  f n := ModuleCat.ofHom (pdExteriorMap deltaB deltaE f hf n)
  comm' i j hij := by
    subst j
    apply ModuleCat.hom_ext
    exact pdExteriorMap_d_naturality deltaB deltaE f hf i

/-- The identity PD morphism induces the identity cochain map. -/
theorem pdDeRhamMap_id (deltaB : DividedPowers J)
    (hf : IsDPMorphism deltaB deltaB (AlgHom.id A B).toRingHom) :
    pdDeRhamMap deltaB deltaB (AlgHom.id A B) hf = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact pdExteriorMap_id deltaB hf n

/-- The induced cochain maps respect composition of PD morphisms. -/
theorem pdDeRhamMap_comp
    (deltaB : DividedPowers J) {D : Type u} [CommRing D] [Algebra A D]
    {K : Ideal D} (deltaD : DividedPowers K)
    {E : Type u} [CommRing E] [Algebra A E] {L : Ideal E}
    (deltaE : DividedPowers L)
    (f : B →ₐ[A] D) (hf : IsDPMorphism deltaB deltaD f.toRingHom)
    (g : D →ₐ[A] E) (hg : IsDPMorphism deltaD deltaE g.toRingHom) :
    pdDeRhamMap deltaB deltaD f hf ≫ pdDeRhamMap deltaD deltaE g hg =
      pdDeRhamMap deltaB deltaE (g.comp f)
        (DividedPowers.IsDPMorphism.comp deltaE hg hf) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact pdExteriorMap_comp deltaB deltaD deltaE f hf g hg n

/-- In degree zero, under the identifications `Ω^0_{B,δ_B} ≅ B` and
`Ω^0_{D,δ_D} ≅ D`, the map induced on PD forms is the underlying algebra map
`f`. -/
theorem zeroEquiv_comp_pdExteriorMap_zero
    (deltaB : DividedPowers J) (deltaD : DividedPowers K)
    (f : B →ₐ[A] D) (hf : IsDPMorphism deltaB deltaD f.toRingHom) :
    ((exteriorPower.zeroEquiv D (PDKaehler (A := A) deltaD)).restrictScalars
          A).toLinearMap.comp
        (pdExteriorMap deltaB deltaD f hf 0) =
      f.toLinearMap.comp
        ((exteriorPower.zeroEquiv B (PDKaehler (A := A) deltaB)).restrictScalars
          A).toLinearMap := by
  refine pdTerm_linearMap_ext deltaB fun b g ↦ ?_
  simp [pdExteriorMap_generator]

end AffineCrystalline.DeRham

/-! ## The PD de Rham complex of `ocris` -/

namespace AffineCrystalline.InfinitesimalSite.EnvelopeFamily

open CategoryTheory
open DividedPowers

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

/-- The universe lift `ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A`. -/
private abbrev largeLift : ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A :=
  ModuleCat.uliftFunctor.{u + 1, u} A

/-- The universe lift applied degreewise to cochain complexes. -/
private abbrev largeLiftComplex :
    CochainComplex (ModuleCat.{u} A) ℕ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℕ :=
  (largeLift (A := A)).mapHomologicalComplex (ComplexShape.up ℕ)

/-- For a morphism `f : X ⟶ Y` of thickenings, the cochain map
`Ω^•_{Ocris(X)} → Ω^•_{Ocris(Y)}` induced by the comparison map of envelopes. -/
noncomputable def envelopeDeRhamMap
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    {X Y : InfinitesimalThickening A C}
    (f : X ⟶ Y) :
    pdDeRhamComplex (A := A)
        (E.envelope X).dividedPowers ⟶
      pdDeRhamComplex (A := A)
        (E.envelope Y).dividedPowers :=
  AffineCrystalline.DeRham.pdDeRhamMap (E.envelope X).dividedPowers
    (E.envelope Y).dividedPowers
    (EnvelopeChoice.comparison f (E.envelope X) (E.envelope Y))
    (EnvelopeChoice.comparison_spec f (E.envelope X) (E.envelope Y)).2

/-- `envelopeDeRhamMap` respects composition. -/
theorem envelopeDeRhamMap_comp
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    {X Y Z : InfinitesimalThickening A C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    envelopeDeRhamMap E f ≫ envelopeDeRhamMap E g =
      envelopeDeRhamMap E (f ≫ g) := by
  rw [envelopeDeRhamMap, envelopeDeRhamMap, envelopeDeRhamMap,
    AffineCrystalline.DeRham.pdDeRhamMap_comp]
  congr 1
  exact (EnvelopeChoice.comparison_comp f g _ _ _).symm

/-- The functor `X ↦ Ω^•_{Ocris(X)}` from `INF(C/A)` to cochain complexes of
`ModuleCat.{u + 1} A`. -/
noncomputable def ocrisDeRhamComplex
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    InfinitesimalThickening A C ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℕ where
  obj X := (largeLiftComplex (A := A)).obj
    (pdDeRhamComplex (A := A) (E.envelope X).dividedPowers)
  map f := (largeLiftComplex (A := A)).map (envelopeDeRhamMap E f)
  map_id X := by
    simp only [envelopeDeRhamMap, EnvelopeChoice.comparison_id,
      AffineCrystalline.DeRham.pdDeRhamMap_id]
    exact (largeLiftComplex (A := A)).map_id _
  map_comp f g := by
    rw [← (largeLiftComplex (A := A)).map_comp]
    exact congrArg ((largeLiftComplex (A := A)).map)
      (envelopeDeRhamMap_comp E f g).symm

@[simp]
theorem ocrisDeRhamComplex_obj
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    (X : InfinitesimalThickening A C) :
    (ocrisDeRhamComplex E).obj X =
      (largeLiftComplex (A := A)).obj
        (pdDeRhamComplex (A := A) (E.envelope X).dividedPowers) :=
  rfl

/-- The module diagram `X ↦ Ocris(X)`, as a covariant functor on
`InfinitesimalThickening A C`. -/
noncomputable def ocrisModuleLargeOnThickening
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    InfinitesimalThickening A C ⥤ ModuleCat.{u + 1} A where
  obj X := ModuleCat.of A (ULift.{u + 1, u} (E.envelope X).carrier)
  map f := ModuleCat.ofHom <| uliftLinearMap
    (EnvelopeChoice.comparison f (E.envelope _) (E.envelope _)).toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    change EnvelopeChoice.comparison (𝟙 X) (E.envelope X) (E.envelope X)
        x.down = x.down
    simp only [EnvelopeChoice.comparison_id]
    rfl
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    ext x
    change EnvelopeChoice.comparison (f ≫ g) (E.envelope X) (E.envelope Z)
        x.down = EnvelopeChoice.comparison g (E.envelope Y) (E.envelope Z)
          (EnvelopeChoice.comparison f (E.envelope X) (E.envelope Y) x.down)
    exact congrArg (fun h ↦ h x.down)
      (EnvelopeChoice.comparison_comp f g
        (E.envelope X) (E.envelope Y) (E.envelope Z))

/-- The diagram `X ↦ Ocris(X)[0]` of complexes concentrated in degree zero, as a
covariant functor on `InfinitesimalThickening A C`. -/
noncomputable def ocrisComplexOnThickening
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    InfinitesimalThickening A C ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℕ :=
  CategoryTheory.opOp (InfinitesimalThickening A C) ⋙
    EnvelopeFamily.ocrisComplex E

/-- The augmentation `Ω^•_{Ocris(X)} → Ocris(X)[0]`.  In degree zero it is the
identification `Ω^0_{Ocris(X)} ≅ Ocris(X)`; in positive degrees it is zero. -/
noncomputable def envelopeDeRhamAugmentationMap
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
    (X : InfinitesimalThickening A C) :
    (ocrisDeRhamComplex E).obj X ⟶
      (CochainComplex.single₀ (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A (ULift.{u + 1, u} (E.envelope X).carrier)) := by
  let e := (exteriorPower.zeroEquiv (E.envelope X).carrier
      (PDKaehler (A := A) (E.envelope X).dividedPowers)).restrictScalars A
  exact (CochainComplex.toSingle₀Equiv
      ((ocrisDeRhamComplex E).obj X)
      ((ocrisModuleLargeOnThickening E).obj X)).symm
    (ModuleCat.ofHom <| uliftLinearMap e.toLinearMap)

/-- The augmentation `Ω^•_{Ocris(X)} → Ocris(X)[0]`, natural in `X`. -/
noncomputable def ocrisDeRhamAugmentation
    (E : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocrisDeRhamComplex E ⟶ ocrisComplexOnThickening E where
  app X := envelopeDeRhamAugmentationMap E X
  naturality := by
    intro X Y f
    apply (CochainComplex.toSingle₀Equiv
      ((ocrisDeRhamComplex E).obj X)
      ((ocrisModuleLargeOnThickening E).obj Y)).injective
    apply ModuleCat.hom_ext
    ext x
    apply ULift.down_injective
    exact congrArg (fun h ↦ h x.down)
      (AffineCrystalline.DeRham.zeroEquiv_comp_pdExteriorMap_zero
        (E.envelope X).dividedPowers (E.envelope Y).dividedPowers
        (EnvelopeChoice.comparison f (E.envelope X) (E.envelope Y))
        (EnvelopeChoice.comparison_spec f
          (E.envelope X) (E.envelope Y)).2)

/-- For envelope families `E`, `F` and a morphism `f : X ⟶ Y`, the cochain map
from the PD de Rham complex of `E`'s envelope of `X` to that of `F`'s envelope
of `Y`. -/
noncomputable def envelopeDeRhamFamilyMap
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ))
    {X Y : InfinitesimalThickening A C} (f : X ⟶ Y) :
    (ocrisDeRhamComplex E).obj X ⟶ (ocrisDeRhamComplex F).obj Y :=
  (largeLiftComplex (A := A)).map <|
    AffineCrystalline.DeRham.pdDeRhamMap
      (E.envelope X).dividedPowers (F.envelope Y).dividedPowers
      (EnvelopeChoice.comparison f (E.envelope X) (F.envelope Y))
      (EnvelopeChoice.comparison_spec f (E.envelope X) (F.envelope Y)).2

/-- `envelopeDeRhamFamilyMap` respects composition. -/
theorem envelopeDeRhamFamilyMap_comp
    (E F G : EnvelopeFamily (A := A) (C := C) (γ := γ))
    {X Y Z : InfinitesimalThickening A C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    envelopeDeRhamFamilyMap E F f ≫ envelopeDeRhamFamilyMap F G g =
      envelopeDeRhamFamilyMap E G (f ≫ g) := by
  change (largeLiftComplex (A := A)).map _ ≫ (largeLiftComplex (A := A)).map _ =
    (largeLiftComplex (A := A)).map _
  rw [← (largeLiftComplex (A := A)).map_comp, AffineCrystalline.DeRham.pdDeRhamMap_comp]
  congr 2
  exact (EnvelopeChoice.comparison_comp f g _ _ _).symm

/-- The PD de Rham diagrams `ocrisDeRhamComplex` obtained from two envelope
families are naturally isomorphic. -/
noncomputable def ocrisDeRhamComplexIso
    (E F : EnvelopeFamily (A := A) (C := C) (γ := γ)) :
    ocrisDeRhamComplex E ≅ ocrisDeRhamComplex F :=
  NatIso.ofComponents
    (fun X ↦
      { hom := envelopeDeRhamFamilyMap E F (𝟙 X)
        inv := envelopeDeRhamFamilyMap F E (𝟙 X)
        hom_inv_id := by
          rw [envelopeDeRhamFamilyMap_comp E F E (𝟙 X) (𝟙 X)]
          exact (ocrisDeRhamComplex E).map_id X
        inv_hom_id := by
          rw [envelopeDeRhamFamilyMap_comp F E F (𝟙 X) (𝟙 X)]
          exact (ocrisDeRhamComplex F).map_id X })
    (by
      intro X Y f
      change envelopeDeRhamFamilyMap E E f ≫
          envelopeDeRhamFamilyMap E F (𝟙 Y) =
        envelopeDeRhamFamilyMap E F (𝟙 X) ≫
          envelopeDeRhamFamilyMap F F f
      calc
        _ = envelopeDeRhamFamilyMap E F (f ≫ 𝟙 Y) :=
          envelopeDeRhamFamilyMap_comp E E F f (𝟙 Y)
        _ = envelopeDeRhamFamilyMap E F (𝟙 X ≫ f) := by rfl
        _ = _ := (envelopeDeRhamFamilyMap_comp E F F (𝟙 X) f).symm)

end AffineCrystalline.InfinitesimalSite.EnvelopeFamily

