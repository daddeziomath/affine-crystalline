/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.Construction.RelationExteriorQuotient
import AffineCrystalline.DeRham.RiouBasic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Descent of differentials to the PD de Rham terms

Let `δ` be a divided-power structure on an ideal `J ⊆ B`. The quotient map
`Ω[B⁄A] → PDKaehler δ` induces surjective `A`-linear maps
`pdTermMap δ n : ⋀[B]^n Ω[B⁄A] → ⋀[B]^n (PDKaehler δ)` in every degree. A family
of `A`-linear maps `d n : ⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]` descends to the
PD terms exactly when each `d n` maps the kernel of `pdTermMap δ n` into the
kernel of `pdTermMap δ (n + 1)`; this is the condition `PDRelationStable`. If
moreover `d (n + 1) ∘ d n = 0`, the descended maps also square to zero.

The descent is an instance of a general lemma, `descendLinearMap`, which
factors a linear map through a surjection whose kernel it kills.

For the de Rham differential `DeRhamComplex.d`, the condition
`PDRelationStable δ` amounts to `QuotientRelationStable (pdRelations δ)`, which
is proved in all degrees as `pdQuotientRelationStable`.

## Main definitions

* `OrdinaryTerm n`, `PDTerm δ n`: the modules `⋀[B]^n Ω[B⁄A]` and
  `⋀[B]^n (PDKaehler δ)`.
* `pdTermMapB δ n`, `pdTermMap δ n`: the map induced by the quotient
  `Ω[B⁄A] → PDKaehler δ`, as a `B`-linear and as an `A`-linear map.
* `pdRelationPower δ n`: the kernel of `pdTermMap δ n`.
* `descendLinearMap q f hq hker`: the factorisation of `f` through a surjection
  `q` with `ker q ≤ ker f`.
* `PDRelationStable δ d`: the stability condition described above.
* `descendedDifferential δ d hstable n`: the descended map on the PD terms.

## Main results

* `descendLinearMap_comp`: `descendLinearMap q f hq hker ∘ q = f`.
* `descendedDifferential_comp_pdTermMap`: the quotient maps intertwine `d` and
  the descended maps.
* `descendedDifferential_comp_self`: the descended maps square to zero if `d`
  does.
* `pdRelationGenerator_mem_pdRelationPower_one`: every defining PD relation lies
  in the degree-one kernel.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

open scoped CategoryTheory
open DividedPowers

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-! ## Exterior-power quotient maps -/

/-- The ordinary de Rham term in degree `n`. -/
abbrev OrdinaryTerm (n : ℕ) : Type u := ⋀[B]^n Ω[B⁄A]

/-- The PD de Rham term in degree `n`. -/
abbrev PDTerm (n : ℕ) : Type u := ⋀[B]^n (PDKaehler (A := A) δ)

/-- The `B`-linear map `⋀[B]^n Ω[B⁄A] → ⋀[B]^n (PDKaehler δ)` induced by the
quotient map. -/
noncomputable def pdTermMapB (n : ℕ) : OrdinaryTerm (A := A) (B := B) n →ₗ[B]
    PDTerm (A := A) (B := B) δ n :=
  exteriorPower.map n ((pdRelations (A := A) δ).mkQ)

/-- The map `pdTermMapB δ n`, regarded as an `A`-linear map. -/
noncomputable def pdTermMap (n : ℕ) : OrdinaryTerm (A := A) (B := B) n →ₗ[A]
    PDTerm (A := A) (B := B) δ n :=
  (pdTermMapB (A := A) (B := B) δ n).restrictScalars A

/-- The map `pdTermMapB δ n` is surjective. -/
theorem pdTermMapB_surjective (n : ℕ) :
    Function.Surjective (pdTermMapB (A := A) (B := B) δ n) :=
  exteriorPower.map_surjective (Submodule.mkQ_surjective _)

/-- The map `pdTermMap δ n` is surjective. -/
theorem pdTermMap_surjective (n : ℕ) :
    Function.Surjective (pdTermMap (A := A) (B := B) δ n) :=
  pdTermMapB_surjective (A := A) (B := B) δ n

/-- The kernel of `pdTermMap δ n`: the elements of `⋀[B]^n Ω[B⁄A]` that vanish
in `⋀[B]^n (PDKaehler δ)`. -/
abbrev pdRelationPower (n : ℕ) : Submodule A (OrdinaryTerm (A := A) (B := B) n) :=
  LinearMap.ker (pdTermMap (A := A) (B := B) δ n)

@[simp]
theorem mem_pdRelationPower_iff {n : ℕ} {ω : OrdinaryTerm (A := A) (B := B) n} :
    ω ∈ pdRelationPower (A := A) (B := B) δ n ↔
      pdTermMap (A := A) (B := B) δ n ω = 0 :=
  Iff.rfl

/-! ## Descent along a surjection -/

section GenericDescent

variable {R M N P : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Factor a linear map `f : M → P` through a surjective linear map
`q : M → N` with `ker q ≤ ker f`. The construction composes the map
`M ⧸ ker q → P` induced by `f` with the inverse of the isomorphism
`M ⧸ ker q ≃ N` induced by `q`. -/
noncomputable def descendLinearMap (q : M →ₗ[R] N) (f : M →ₗ[R] P)
    (hq : Function.Surjective q) (hker : LinearMap.ker q ≤ LinearMap.ker f) :
    N →ₗ[R] P := by
  let qbar : M ⧸ LinearMap.ker q →ₗ[R] N :=
    Submodule.liftQ (LinearMap.ker q) q le_rfl
  have hqbar_surjective : Function.Surjective qbar := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨(LinearMap.ker q).mkQ x, by
      simp [qbar]
    ⟩
  have hqbar_injective : Function.Injective qbar := by
    have hkerbar : LinearMap.ker qbar = (⊥ : Submodule R (M ⧸ LinearMap.ker q)) := by
      dsimp [qbar]
      rw [Submodule.ker_liftQ, Submodule.mkQ_map_self]
    exact LinearMap.ker_eq_bot.mp hkerbar
  let e : (M ⧸ LinearMap.ker q) ≃ₗ[R] N :=
    LinearEquiv.ofBijective qbar ⟨hqbar_injective, hqbar_surjective⟩
  exact (Submodule.liftQ (LinearMap.ker q) f hker).comp e.symm.toLinearMap

/-- The defining property of `descendLinearMap`. -/
theorem descendLinearMap_comp (q : M →ₗ[R] N) (f : M →ₗ[R] P)
    (hq : Function.Surjective q) (hker : LinearMap.ker q ≤ LinearMap.ker f) :
    descendLinearMap q f hq hker ∘ₗ q = f := by
  apply LinearMap.ext
  intro x
  simp only [descendLinearMap, LinearMap.comp_apply]
  have hx : q x = Submodule.liftQ (LinearMap.ker q) q le_rfl ((LinearMap.ker q).mkQ x) := rfl
  rw [hx, LinearEquiv.coe_coe]
  exact (congrArg (Submodule.liftQ _ f hker) (LinearEquiv.ofBijective_symm_apply_apply _ _)).trans
    (Submodule.liftQ_apply _ _ _)

end GenericDescent

/-! ## PD-stable families and their descent -/

/-- A family of `A`-linear maps `d n : ⋀[B]^n Ω[B⁄A] → ⋀[B]^(n + 1) Ω[B⁄A]` is
PD-stable if, in every degree, `d n` maps the kernel `pdRelationPower δ n` into
the kernel of `pdTermMap δ (n + 1)`.

For the de Rham differential `DeRhamComplex.d`, this is (up to unfolding
definitions) `QuotientRelationStable (pdRelations δ)`, proved as
`pdQuotientRelationStable`. -/
def PDRelationStable
    (d : ∀ n : ℕ, OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1)) : Prop :=
  ∀ n : ℕ,
    pdRelationPower (A := A) (B := B) δ n ≤
      LinearMap.ker
        (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d n)

/-- The map `⋀[B]^n (PDKaehler δ) → ⋀[B]^(n + 1) (PDKaehler δ)` induced by a
PD-stable family `d`. -/
noncomputable def descendedDifferential
    (d : ∀ n : ℕ, OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (hstable : PDRelationStable (A := A) (B := B) δ d) (n : ℕ) :
    PDTerm (A := A) (B := B) δ n →ₗ[A]
      PDTerm (A := A) (B := B) δ (n + 1) :=
  descendLinearMap
    (pdTermMap (A := A) (B := B) δ n)
    (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d n)
    (pdTermMap_surjective (A := A) (B := B) δ n)
    (hstable n)

/-- The quotient maps intertwine `d` and the descended maps. -/
theorem descendedDifferential_comp_pdTermMap
    (d : ∀ n : ℕ, OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (hstable : PDRelationStable (A := A) (B := B) δ d) (n : ℕ) :
    descendedDifferential (A := A) (B := B) δ d hstable n ∘ₗ
        pdTermMap (A := A) (B := B) δ n =
      pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d n :=
  descendLinearMap_comp
    (pdTermMap (A := A) (B := B) δ n)
    (pdTermMap (A := A) (B := B) δ (n + 1) ∘ₗ d n)
    (pdTermMap_surjective (A := A) (B := B) δ n)
    (hstable n)

/-- If `d (n + 1) ∘ d n = 0` for all `n`, then the descended maps also square
to zero. -/
theorem descendedDifferential_comp_self
    (d : ∀ n : ℕ, OrdinaryTerm (A := A) (B := B) n →ₗ[A]
      OrdinaryTerm (A := A) (B := B) (n + 1))
    (hstable : PDRelationStable (A := A) (B := B) δ d)
    (hd : ∀ n : ℕ, d (n + 1) ∘ₗ d n = 0) (n : ℕ) :
    descendedDifferential (A := A) (B := B) δ d hstable (n + 1) ∘ₗ
        descendedDifferential (A := A) (B := B) δ d hstable n = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := pdTermMap_surjective (A := A) (B := B) δ n y
  have hcomp :
      (descendedDifferential (A := A) (B := B) δ d hstable (n + 1) ∘ₗ
        descendedDifferential (A := A) (B := B) δ d hstable n) ∘ₗ
          pdTermMap (A := A) (B := B) δ n = 0 := by
    rw [LinearMap.comp_assoc, descendedDifferential_comp_pdTermMap (A := A) (B := B) δ d hstable n,
      ← LinearMap.comp_assoc,
      descendedDifferential_comp_pdTermMap (A := A) (B := B) δ d hstable (n + 1),
      LinearMap.comp_assoc, hd n, LinearMap.comp_zero]
  simpa [LinearMap.comp_apply] using congrArg (fun F ↦ F x) hcomp

/-! ## Degree one -/

/-- Every defining PD relation, viewed in `⋀[B]^1 Ω[B⁄A]`, lies in the kernel
`pdRelationPower δ 1`. -/
theorem pdRelationGenerator_mem_pdRelationPower_one
    (n : ℕ) (hn : 1 ≤ n) (x : B) (hx : x ∈ J) :
    exteriorPower.ιMulti B 1 (fun _ : Fin 1 ↦ pdRelationGenerator δ n x) ∈
      pdRelationPower (A := A) (B := B) δ 1 := by
  rw [mem_pdRelationPower_iff, pdTermMap, LinearMap.restrictScalars_apply, pdTermMapB,
    exteriorPower.map_apply_ιMulti]
  exact (exteriorPower.ιMulti B 1).map_coord_zero 0
    (mkQ_pdRelationGenerator_eq_zero (A := A) (B := B) δ n hn x hx)

end AffineCrystalline.DeRham
