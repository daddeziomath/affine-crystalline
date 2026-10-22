/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.QuotientComplex
import AffineCrystalline.DeRham.ExteriorPowerQuotient
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Kernel of the quotient map on de Rham terms

Let `N ⊆ Ω[B⁄A]` be a `B`-submodule. We identify the kernel of the `A`-linear
map `quotientTermMap N n : ⋀[B]^n Ω[B⁄A] → ⋀[B]^n (Ω[B⁄A] ⧸ N)` with the
restriction of scalars of the `B`-submodule `exteriorQuotientRelations N n`,
which is spanned by the wedges `m₁ ∧ ⋯ ∧ mₙ` having at least one factor in `N`.

## Main results

* `quotientTermMap_ker`: `ker (quotientTermMap N n)` is
  `(exteriorQuotientRelations N n).restrictScalars A`.
-/

universe u

noncomputable section

namespace AffineCrystalline.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The kernel of `quotientTermMap N n` is spanned by the wedges having one
factor in `N`. -/
theorem quotientTermMap_ker (N : Submodule B (Ω[B⁄A])) (n : ℕ) :
    LinearMap.ker (quotientTermMap (A := A) N n) =
      (exteriorQuotientRelations N n).restrictScalars A := by
  ext x
  change exteriorPower.map n N.mkQ x = 0 ↔
    x ∈ exteriorQuotientRelations N n
  rw [← LinearMap.mem_ker, exteriorPower_ker_map_mkQ]

end AffineCrystalline.DeRham
