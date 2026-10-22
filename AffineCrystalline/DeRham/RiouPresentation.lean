/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.RiouBasic
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.Algebra.Module.Presentation.Tautological
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Presentations and Riou's generator formula

This file collects the presentation-theoretic ingredients of Riou's
construction of the de Rham differential on `⋀[B]^• Ω[B⁄A]`. The differential
is determined by the generator formula
`b₀ db₁ ∧ ⋯ ∧ dbₙ ↦ db₀ ∧ db₁ ∧ ⋯ ∧ dbₙ`, and a map defined on the generators of
a presentation descends to a linear map as soon as it respects the relations.
The exterior powers are formed over `B`, while the differential is only
`A`-linear; accordingly, the presentations used to define it are presentations
of `A`-modules.

## Main definitions

* `exteriorPresentation n`: the `B`-linear presentation of `⋀[B]^n Ω[B⁄A]` by
  the wedges of `n` one-forms.
* `sourceGenerator n b₀ g`, `targetGenerator n b₀ g`: the elements
  `b₀ dg₁ ∧ ⋯ ∧ dgₙ` and `db₀ ∧ dg₁ ∧ ⋯ ∧ dgₙ`.
* `RelationSolution P N`: solutions in `N` of the relations of a
  presentation `P`, and `RelationSolution.descend`, the induced linear map.
* `degreeZeroDifferential`: the degree-zero differential `B → ⋀[B]^1 Ω[B⁄A]`.
* `HigherDifferentialData n`, `differential`: an `A`-linear presentation of
  `⋀[B]^n Ω[B⁄A]` with a solution of its relations in `⋀[B]^(n + 1) Ω[B⁄A]`,
  and the induced map.

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
-/

open scoped CategoryTheory

universe u

noncomputable section

namespace AffineCrystalline.DeRham.RiouPresentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## Exterior-power presentations and the generator formula -/

/-- The `B`-linear presentation of `⋀[B]^n Ω[B⁄A]` whose generators are the
wedges `m₁ ∧ ⋯ ∧ mₙ` of one-forms. -/
noncomputable def exteriorPresentation (n : ℕ) :
    Module.Presentation B (⋀[B]^n Ω[B⁄A]) :=
  exteriorPower.presentation B n (Ω[B⁄A])

@[simp]
theorem exteriorPresentation_var (n : ℕ) (g : Fin n → Ω[B⁄A]) :
    (exteriorPresentation (A := A) (B := B) n).var g =
      exteriorPower.ιMulti B n g := by
  rfl

/-- The `(n + 1)`-tuple `(b₀, g₀, …, gₙ₋₁)`. -/
def finInsert (b₀ : B) {n : ℕ} (g : Fin n → B) : Fin (n + 1) → B
  | ⟨0, _⟩ => b₀
  | ⟨n + 1, _⟩ => g ⟨n, by omega⟩

omit [CommRing B] in
@[simp] theorem finInsert_zero (b₀ : B) {n : ℕ} (g : Fin n → B) :
    finInsert b₀ g 0 = b₀ := rfl

omit [CommRing B] in
@[simp] theorem finInsert_succ (b₀ : B) {n : ℕ} (g : Fin n → B) (i : Fin n) :
    finInsert b₀ g i.succ = g i := rfl

/-- The source generator `b₀ db₁ ∧ ... ∧ dbₙ` in Riou's presentation. -/
def sourceGenerator (n : ℕ) (b₀ : B) (g : Fin n → B) : ⋀[B]^n Ω[B⁄A] :=
  b₀ • exteriorPower.ιMulti B n (KaehlerDifferential.D A B ∘ g)

/-- Riou's generator formula
`b₀ db₁ ∧ ... ∧ dbₙ ↦ db₀ ∧ db₁ ∧ ... ∧ dbₙ`. -/
def targetGenerator (n : ℕ) (b₀ : B) (g : Fin n → B) :
    ⋀[B]^(n + 1) Ω[B⁄A] :=
  exteriorPower.ιMulti B (n + 1)
    (KaehlerDifferential.D A B ∘ finInsert b₀ g)

@[simp]
theorem targetGenerator_zero (b₀ : B) :
    targetGenerator (A := A) (B := B) 0 b₀ (fun i ↦ Fin.elim0 i) =
      exteriorPower.ιMulti B 1 (fun _ ↦ KaehlerDifferential.D A B b₀) := by
  rfl

/-! ## Presentation descent -/

/-- Solutions in `N` of the relations of a presentation `P` of `M`, i.e.
assignments of elements of `N` to the generators of `P` respecting all its
relations. By the universal property of `P`, they correspond to `A`-linear
maps `M → N`. -/
abbrev RelationSolution {M : Type u} [AddCommGroup M] [Module A M]
    (P : Module.Presentation A M) (N : Type u) [AddCommGroup N] [Module A N] :=
  P.toRelations.Solution N

namespace RelationSolution

variable {M N : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- The `A`-linear map `M → N` determined by a solution of the relations. -/
noncomputable def descend (P : Module.Presentation A M)
    (c : RelationSolution P N) : M →ₗ[A] N :=
  P.toIsPresentation.desc c

/-- The value of `descend` on a generator. -/
@[simp]
  theorem descend_var (P : Module.Presentation A M)
    (c : RelationSolution P N) (g : P.G) :
    c.descend P (P.var g) = c.var g :=
  P.toIsPresentation.desc_var c g

end RelationSolution

/-! ## The degree-zero differential -/

/-- The degree-zero differential `B → ⋀[B]^1 Ω[B⁄A]`. -/
noncomputable abbrev degreeZeroDifferential :
    B →ₗ[A] ⋀[B]^1 Ω[B⁄A] :=
  (AffineCrystalline.DeRham.ordinaryDerivationToDegreeOne
    (A := A) (B := B)).hom

/-- Under `⋀[B]^1 Ω[B⁄A] ≃ Ω[B⁄A]`, the degree-zero differential is the
universal derivation. -/
theorem degreeZeroDifferential_spec :
    (AffineCrystalline.DeRham.oneFormsEquiv (A := A) (B := B)
      Ω[B⁄A]).toLinearMap ∘ₗ
        degreeZeroDifferential (A := A) (B := B) =
      (KaehlerDifferential.D A B).toLinearMap :=
  AffineCrystalline.DeRham.ordinaryDerivationToDegreeOne_spec

/-! ## Higher differentials from presentation data -/

/-- Data for a differential `⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]`: an `A`-linear
presentation `P` of `⋀[B]^n Ω[B⁄A]`, a solution `solution` of its relations
in `⋀[B]^(n + 1) Ω[B⁄A]`, and an `A`-linear endomorphism `target` of
`⋀[B]^(n + 1) Ω[B⁄A]`. The associated map is `differential`. -/
structure HigherDifferentialData (n : ℕ) where
  P : Module.Presentation.{u, u} A (⋀[B]^n Ω[B⁄A])
  target : ⋀[B]^(n + 1) Ω[B⁄A] →ₗ[A] ⋀[B]^(n + 1) Ω[B⁄A]
  solution : RelationSolution P (⋀[B]^(n + 1) Ω[B⁄A])

/-- The `A`-linear map determined by `HigherDifferentialData`. -/
noncomputable def differential (data : HigherDifferentialData (A := A) (B := B) n) :
    (⋀[B]^n Ω[B⁄A]) →ₗ[A] ⋀[B]^(n + 1) Ω[B⁄A] :=
  data.solution.descend data.P

/-- The value of `differential data` on a presentation generator. -/
@[simp]
theorem differential_var (data : HigherDifferentialData (A := A) (B := B) n)
    (g : data.P.G) :
    differential data (data.P.var g) = data.solution.var g :=
  RelationSolution.descend_var data.P data.solution g

end AffineCrystalline.DeRham.RiouPresentation
