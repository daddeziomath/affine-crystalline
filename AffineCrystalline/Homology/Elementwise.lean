/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Elementwise exactness and quasi-isomorphisms of `ℕ`-indexed cochain complexes of modules

For cochain complexes of modules indexed by `ℕ` (with `ComplexShape.up ℕ`),
exactness in degree `n` and the property of being a quasi-isomorphism in degree
`n` are characterized by statements about elements.  The previous index is
written `n - 1` (truncated subtraction): in degree `0` the incoming
differential `d 0 0` vanishes, so the criteria specialize to the injectivity
statements describing `H⁰` as the module of cocycles.

## Main results

* `AffineCrystalline.Homology.exactAt_iff_elementwise`: `K` is exact in degree
  `n` iff every cocycle of degree `n` is a coboundary.
* `AffineCrystalline.Homology.moduleCat_quasiIso_iff_elementwise`: the
  elementwise criterion for a morphism of short complexes of modules to be a
  quasi-isomorphism, via the explicit homology `ker g ⧸ range f`.
* `AffineCrystalline.Homology.quasiIsoAt_iff_elementwise`: `f : K ⟶ L` is a
  quasi-isomorphism in degree `n` iff every cocycle of `L` is cohomologous to the
  image of a cocycle of `K`, and every cocycle of `K` whose image is a
  coboundary is itself a coboundary.
* `AffineCrystalline.Homology.quasiIso_of_elementwise`: the corresponding
  criterion for `f` to be a quasi-isomorphism.

These criteria are the interface through which the bicomplex arguments of
`AffineCrystalline.Homology.TotM` and its sequels are carried out.
-/

open CategoryTheory

universe v u

namespace AffineCrystalline.Homology

variable {R : Type u} [Ring R]

/-- For `ComplexShape.up ℕ`, the previous index of `n` is `n - 1`. -/
theorem upNat_prev (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  cases n with
  | zero => simp
  | succ n => simp

/-- For `ComplexShape.up ℕ`, the next index of `n` is `n + 1`. -/
theorem upNat_next (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 := by
  simp

/-- Elementwise form of the commutation of a morphism of complexes with the
differentials. -/
theorem hom_comm_apply {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (f : K ⟶ L) (i j : ι) (x : K.X i) :
    (L.d i j).hom ((f.f i).hom x) = (f.f j).hom ((K.d i j).hom x) := by
  change (f.f i ≫ L.d i j).hom x = (K.d i j ≫ f.f j).hom x
  rw [f.comm]

/-- Elementwise form of `d ≫ d = 0`. -/
theorem d_comp_d_apply {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j k : ι) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := by
  change (K.d i j ≫ K.d j k).hom x = 0
  rw [K.d_comp_d]
  rfl

/-- A cochain complex of modules is exact in degree `n` iff every element `x`
of degree `n` with `d x = 0` is of the form `d y`. -/
theorem exactAt_iff_elementwise (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    K.ExactAt n ↔ ∀ x : K.X n, (K.d n (n + 1)).hom x = 0 →
      ∃ y : K.X (n - 1), (K.d (n - 1) n).hom y = x := by
  rw [HomologicalComplex.exactAt_iff' K (n - 1) n (n + 1) (upNat_prev n) (upNat_next n),
    ShortComplex.moduleCat_exact_iff]
  rfl

section ShortComplex

variable {S₁ S₂ : ShortComplex (ModuleCat.{v} R)} (φ : S₁ ⟶ S₂)

/-- The linear map `ker S₁.g → ker S₂.g` between the modules of cycles induced by a
morphism `φ : S₁ ⟶ S₂` of short complexes of modules. -/
def moduleCatCyclesMap : LinearMap.ker S₁.g.hom →ₗ[R] LinearMap.ker S₂.g.hom :=
  φ.τ₂.hom.restrict fun x hx ↦ by
    change (φ.τ₂ ≫ S₂.g).hom x = 0
    rw [φ.comm₂₃]
    change φ.τ₃.hom (S₁.g.hom x) = 0
    rw [LinearMap.mem_ker.1 hx, map_zero]

/-- The map induced on cycles by a morphism of short complexes of modules sends boundaries to
boundaries. -/
theorem moduleCatCyclesMap_range_le :
    LinearMap.range S₁.moduleCatToCycles ≤
      (LinearMap.range S₂.moduleCatToCycles).comap (moduleCatCyclesMap φ) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨φ.τ₁.hom y, Subtype.ext ?_⟩
  change (φ.τ₁ ≫ S₂.f).hom y = (S₁.f ≫ φ.τ₂).hom y
  rw [φ.comm₁₂]

/-- The linear map between the explicit homology modules `ker g ⧸ range f` induced by a
morphism of short complexes of modules. -/
def moduleCatHomologyMap :
    (LinearMap.ker S₁.g.hom ⧸ LinearMap.range S₁.moduleCatToCycles) →ₗ[R]
      (LinearMap.ker S₂.g.hom ⧸ LinearMap.range S₂.moduleCatToCycles) :=
  Submodule.mapQ _ _ (moduleCatCyclesMap φ) (moduleCatCyclesMap_range_le φ)

/-- The left homology map data of a morphism of short complexes of modules with respect to the
explicit left homology data `ShortComplex.moduleCatLeftHomologyData`. -/
def moduleCatLeftHomologyMapData :
    ShortComplex.LeftHomologyMapData φ S₁.moduleCatLeftHomologyData
      S₂.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (moduleCatCyclesMap φ)
  φH := ModuleCat.ofHom (moduleCatHomologyMap φ)
  commi := by
    ext
    rfl
  commf' := by
    ext y
    apply Subtype.ext
    change (S₁.f ≫ φ.τ₂).hom y = (φ.τ₁ ≫ S₂.f).hom y
    rw [φ.comm₁₂]
  commπ := by
    ext
    rfl

/-- A morphism of short complexes of modules is a quasi-isomorphism iff the induced map on the
explicit homology modules `ker g ⧸ range f` is bijective. -/
theorem moduleCat_quasiIso_iff_bijective :
    ShortComplex.QuasiIso φ ↔ Function.Bijective (moduleCatHomologyMap φ) := by
  rw [(moduleCatLeftHomologyMapData φ).quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  rfl

/-- The map induced on homology by a morphism `φ` of short complexes of modules is surjective
iff every cycle of the target is homologous to the image of a cycle of the source. -/
theorem moduleCatHomologyMap_surjective_iff :
    Function.Surjective (moduleCatHomologyMap φ) ↔
      ∀ y : S₂.X₂, S₂.g.hom y = 0 →
        ∃ x : S₁.X₂, S₁.g.hom x = 0 ∧ ∃ z : S₂.X₁, φ.τ₂.hom x = y + S₂.f.hom z := by
  constructor
  · intro h y hy
    obtain ⟨c, hc⟩ := h (Submodule.Quotient.mk ⟨y, hy⟩)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [moduleCatHomologyMap, Submodule.mapQ_apply, Submodule.Quotient.eq] at hc
    obtain ⟨z, hz⟩ := hc
    have hz' : S₂.f.hom z = φ.τ₂.hom x.1 - y := congrArg Subtype.val hz
    exact ⟨x.1, x.2, z, by rw [hz']; abel⟩
  · intro h c
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨x, hx, z, hz⟩ := h y.1 y.2
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [moduleCatHomologyMap, Submodule.mapQ_apply, Submodule.Quotient.eq]
    refine ⟨z, Subtype.ext ?_⟩
    change S₂.f.hom z = φ.τ₂.hom x - y.1
    rw [hz]
    abel

/-- The map induced on homology by a morphism `φ` of short complexes of modules is injective
iff every cycle of the source whose image is a boundary is itself a boundary. -/
theorem moduleCatHomologyMap_injective_iff :
    Function.Injective (moduleCatHomologyMap φ) ↔
      ∀ x : S₁.X₂, S₁.g.hom x = 0 → ∀ z : S₂.X₁, φ.τ₂.hom x = S₂.f.hom z →
        ∃ w : S₁.X₁, S₁.f.hom w = x := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x hx z hz
    have h0 : moduleCatHomologyMap φ (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
      rw [moduleCatHomologyMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨z, Subtype.ext hz.symm⟩
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).1 (h _ h0)
    exact ⟨w, congrArg Subtype.val hw⟩
  · intro h c hc
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [moduleCatHomologyMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨z, hz⟩ := hc
    obtain ⟨w, hw⟩ := h x.1 x.2 z (congrArg Subtype.val hz).symm
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, Subtype.ext hw⟩

/-- Elementwise criterion for a morphism of short complexes of modules to be a
quasi-isomorphism. -/
theorem moduleCat_quasiIso_iff_elementwise :
    ShortComplex.QuasiIso φ ↔
      (∀ y : S₂.X₂, S₂.g.hom y = 0 →
        ∃ x : S₁.X₂, S₁.g.hom x = 0 ∧ ∃ z : S₂.X₁, φ.τ₂.hom x = y + S₂.f.hom z) ∧
      (∀ x : S₁.X₂, S₁.g.hom x = 0 → ∀ z : S₂.X₁, φ.τ₂.hom x = S₂.f.hom z →
        ∃ w : S₁.X₁, S₁.f.hom w = x) := by
  rw [moduleCat_quasiIso_iff_bijective, Function.Bijective, and_comm,
    moduleCatHomologyMap_surjective_iff, moduleCatHomologyMap_injective_iff]

end ShortComplex

/-- Elementwise criterion for a quasi-isomorphism in degree `n`: surjectivity
and injectivity of the induced map on `Hⁿ`, stated with cocycles and
coboundaries. -/
theorem quasiIsoAt_iff_elementwise {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    QuasiIsoAt f n ↔
      (∀ y : L.X n, (L.d n (n + 1)).hom y = 0 →
        ∃ x : K.X n, (K.d n (n + 1)).hom x = 0 ∧
          ∃ z : L.X (n - 1), (f.f n).hom x = y + (L.d (n - 1) n).hom z) ∧
      (∀ x : K.X n, (K.d n (n + 1)).hom x = 0 → ∀ z : L.X (n - 1),
        (f.f n).hom x = (L.d (n - 1) n).hom z →
          ∃ w : K.X (n - 1), (K.d (n - 1) n).hom w = x) := by
  rw [quasiIsoAt_iff' f (n - 1) n (n + 1) (upNat_prev n) (upNat_next n)]
  exact moduleCat_quasiIso_iff_elementwise _

/-- A morphism of cochain complexes of modules satisfying the elementwise
surjectivity and injectivity conditions in every degree is a
quasi-isomorphism. -/
theorem quasiIso_of_elementwise {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L)
    (hsurj : ∀ n (y : L.X n), (L.d n (n + 1)).hom y = 0 →
        ∃ x : K.X n, (K.d n (n + 1)).hom x = 0 ∧
          ∃ z : L.X (n - 1), (f.f n).hom x = y + (L.d (n - 1) n).hom z)
    (hinj : ∀ n (x : K.X n), (K.d n (n + 1)).hom x = 0 → ∀ z : L.X (n - 1),
        (f.f n).hom x = (L.d (n - 1) n).hom z →
          ∃ w : K.X (n - 1), (K.d (n - 1) n).hom w = x) :
    QuasiIso f :=
  ⟨fun n ↦ (quasiIsoAt_iff_elementwise f n).2 ⟨hsurj n, hinj n⟩⟩

end AffineCrystalline.Homology
