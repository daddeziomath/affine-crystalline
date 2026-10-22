/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Abstract de Rham-type complexes

A lightweight interface for non-negatively graded cochain complexes of
`B`-modules `X 0 → X 1 → X 2 → ⋯`, recorded by their objects, their degree `+1`
differentials and the relations `d ∘ d = 0`, together with the conversion to
Mathlib's `CochainComplex`. No particular choice of objects or differentials is
assumed.

## Main definitions

* `AffineCrystalline.DeRham.Abstract B`: the data `(X, d, d_comp_d)` of a
  non-negatively graded complex of `B`-modules.
* `AffineCrystalline.DeRham.Abstract.toCochainComplex`: the associated object of
  `CochainComplex (ModuleCat B) ℕ`.
-/

open scoped CategoryTheory

namespace AffineCrystalline
namespace DeRham

universe u v

/--
A non-negatively graded cochain complex of `B`-modules: objects `X n`,
differentials `d n : X n ⟶ X (n + 1)` and the relations `d (n + 1) ∘ d n = 0`.
Indexing the differential by its source degree only is convenient for graded
constructions such as exterior powers.
-/
structure Abstract (B : Type u) [CommRing B] where
  /-- The object in each non-negative degree. -/
  X : ℕ → ModuleCat.{v} B
  /-- The degree `+1` differential. -/
  d : ∀ n : ℕ, X n ⟶ X (n + 1)
  /-- Consecutive differentials compose to zero. -/
  d_comp_d : ∀ n : ℕ, d n ≫ d (n + 1) = 0

namespace Abstract

variable {B : Type u} [CommRing B]

/-- The cochain complex in `CochainComplex (ModuleCat B) ℕ` defined by `C`. -/
def toCochainComplex (C : Abstract.{u, v} B) :
    CochainComplex (ModuleCat.{v} B) ℕ :=
  CochainComplex.of C.X C.d C.d_comp_d

@[simp]
theorem toCochainComplex_X (C : Abstract.{u, v} B) (n : ℕ) :
    C.toCochainComplex.X n = C.X n :=
  rfl

@[simp]
theorem toCochainComplex_d (C : Abstract.{u, v} B) (n : ℕ) :
    C.toCochainComplex.d n (n + 1) = C.d n :=
  CochainComplex.of_d C.X C.d n

theorem toCochainComplex_d_ne (C : Abstract.{u, v} B)
    {m n : ℕ} (h : m + 1 ≠ n) : C.toCochainComplex.d m n = 0 :=
  CochainComplex.of_d_ne C.X C.d h

@[simp]
theorem d_square_zero (C : Abstract.{u, v} B) (n : ℕ) :
    C.d n ≫ C.d (n + 1) = 0 :=
  C.d_comp_d n

@[simp, reassoc]
theorem toCochainComplex_d_comp_d (C : Abstract.{u, v} B)
    (i j k : ℕ) :
    C.toCochainComplex.d i j ≫ C.toCochainComplex.d j k = 0 :=
  HomologicalComplex.d_comp_d C.toCochainComplex i j k

end Abstract

end DeRham
end AffineCrystalline
