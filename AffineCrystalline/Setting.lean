/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The standing hypotheses

Throughout the library `p` is a prime and `(A, I, γ)` is a divided power ring
with `p ∈ I` and `p` nilpotent in `A`. Since `p` is nilpotent, every integer
prime to `p` is a unit in `A`, so `A` is a `ℤ_(p)`-algebra. In the main
results one also fixes an `A`-algebra `C` with `I C = 0`, written
`hIC : I.map (algebraMap A C) = ⊥`, and an integer `e` with `(p ^ e)! = 0` in `A`,
which determines the Frobenius level `Level A C (p ^ e)` on which cohomology is
computed. If `p ^ N = 0` in `A`, then `(p ^ N)! = 0` in `A`, so `e = N` is allowed.

## Main definitions

* `IsCrystallineBase p A I`: the class recording `p ∈ I` and the nilpotence
  of `p` in `A`.

## References

* [Stacks Project, Chapter *Crystalline Cohomology*](https://stacks.math.columbia.edu/tag/07GI)
-/

open scoped TensorProduct
open scoped Simplicial
open scoped CategoryTheory
open DividedPowers

universe u
section Setting

variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] (I : Ideal A) (γ : DividedPowers I)

/-- The standing hypotheses on the divided power base `(A, I, γ)`: `p ∈ I` and
`p ^ N = 0` in `A` for some `N`. It is a class so that it is found by instance
search. -/
class IsCrystallineBase : Prop where
  p_mem : (p : A) ∈ I
  p_nilpotent : ∃ N : ℕ, (p : A) ^ N = 0

end Setting
