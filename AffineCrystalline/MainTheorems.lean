/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Envelope.Construction
import AffineCrystalline.Ocris.CechPoincare
import AffineCrystalline.Ocris.CechAlexander

/-!
# The main theorems

Divided power envelopes exist (`AffineCrystalline.DPEnvelope.hasDPEnvelope`), so
every object of `INF(C/A)` has a compatible divided power envelope and the
structure sheaf `ocris` is defined without further input. In this file we state
the de Rham and Čech–Alexander comparison theorems for the envelope family
`envelopeFamily` chosen in this way. The statements for an arbitrary
`EnvelopeFamily` are `EnvelopeFamily.crystallineCohomologyIsoDeRham`,
`EnvelopeFamily.affineDeRhamComparison` and
`EnvelopeFamily.crystallineCohomologyIsoCechAlexander`; they hold on the level
`Level A C n` of thickenings of exponent `n` for every `n > 0` with `n! = 0` in `A`.

Here the main theorems are stated on the Frobenius level
`INF_e = Level A C (p ^ e)`, the full subcategory of thickenings whose kernel is killed
by `x ↦ x ^ (p ^ e)`, under the hypothesis `(p ^ e)! = 0` in `A`. If `p ^ N = 0` in `A`,
this hypothesis holds for `e = N` (`natCast_factorial_pow_eq_zero`). More precisely,
since the `p`-adic valuation of `(p ^ e)!` is `(p ^ e - 1) / (p - 1)`, the hypothesis
holds as soon as `p ^ ((p ^ e - 1) / (p - 1)) = 0` in `A`; when `p` is nilpotent the two
conditions are equivalent, because the prime-to-`p` part of `(p ^ e)!` is then a unit.
Thus `e` of the order of `log_p N` suffices. This remark is not formalised.

## Main results

* `envelopeExistenceData`: every object of `INF(C/A)` has a compatible divided
  power envelope.
* `crystallineCohomologyIsoDeRham`: `H^k(RΓ(INF(C/A), Ocris)) ≃ H^k(Ω•_{D(0)})`.
* `affineDeRhamComparison`: `lim I•` and `Ω•_{D(0)}` are connected by
  quasi-isomorphisms.
* `crystallineCohomologyIsoCechAlexander`:
  `H^k(RΓ(INF(C/A), Ocris)) ≃ H^k(D(0) → D(1) → D(2) → ⋯)`.
-/

open CategoryTheory

universe u

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} (γ : DividedPowers I)

/-- Every object `π : B → C` of `INF(C/A)` has a divided power envelope of
`ker(π)` compatible with `γ`. -/
theorem envelopeExistenceData : EnvelopeExistenceData (A := A) (C := C) (γ := γ) :=
  EnvelopeExistenceData.of_hasDPEnvelope fun _ ↦ inferInstance

/-- A choice of compatible divided power envelopes at every object of
`INF(C/A)`. -/
noncomputable def envelopeFamily : EnvelopeFamily (A := A) (C := C) (γ := γ) :=
  EnvelopeFamily.ofExistenceData (envelopeExistenceData γ)

variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
  (hIC : I.map (algebraMap A C) = ⊥) (e : ℕ) (he : ((Nat.factorial (p ^ e) : ℕ) : A) = 0)

include hIC he

/-- **Crystalline cohomology is divided power de Rham cohomology (affine
case).** Let `INF_e = Level A C (p ^ e)` be the Frobenius level of thickenings whose
kernel is killed by `x ↦ x ^ (p ^ e)`, and assume `(p ^ e)! = 0` in `A`. Then the `k`-th
cohomology of `RΓ(INF(C/A), Ocris)` is isomorphic to the `k`-th cohomology of the
divided power de Rham complex of the envelope `D(0)` of `A[x_c : c ∈ C] → C`, the value
of `Ocris` at the first Čech object of `INF_e`. -/
theorem crystallineCohomologyIsoDeRham (k : ℕ) :
    Nonempty (((HomotopyCategory.homologyFunctor (ModuleCat.{u + 1} A) (ComplexShape.up ℕ) k).obj
        (envelopeFamily (C := C) γ).ocrisDerivedGlobalSections) ≅
      ((envelopeFamily (C := C) γ).ocrisDeRhamComplex.obj
        (Level.cechObj (p ^ e) 0).obj).homology k) :=
  (envelopeFamily (C := C) γ).crystallineCohomologyIsoDeRham p hIC (p ^ e) he k

/-- If `(p ^ e)! = 0` in `A`, the complex `lim I•` computing the derived global sections
of `ocris` on the Frobenius level `INF_e = Level A C (p ^ e)` and the divided power
de Rham complex of `D(0)` are connected by quasi-isomorphisms. -/
theorem affineDeRhamComparison :
    Homology.QuasiIsoEquiv
      (Cohomology.Cech.limComplex
        (injectiveResolution ((envelopeFamily (C := C) γ).levelOcrisModule p hIC (p ^ e))))
      ((envelopeFamily (C := C) γ).ocrisDeRhamComplex.obj (Level.cechObj (p ^ e) 0).obj) :=
  (envelopeFamily (C := C) γ).affineDeRhamComparison p hIC (p ^ e) he

/-- **Crystalline cohomology is Čech–Alexander cohomology (affine case).** If
`(p ^ e)! = 0` in `A`, the `k`-th cohomology of `RΓ(INF(C/A), Ocris)` is the `k`-th
cohomology of the Čech–Alexander complex `n ↦ Ocris(X_e(n))` of the Frobenius level
`INF_e = Level A C (p ^ e)`. -/
theorem crystallineCohomologyIsoCechAlexander (k : ℕ) :
    Nonempty (((HomotopyCategory.homologyFunctor (ModuleCat.{u + 1} A) (ComplexShape.up ℕ) k).obj
        (envelopeFamily (C := C) γ).ocrisDerivedGlobalSections) ≅
      ((envelopeFamily (C := C) γ).ocrisCechComplex p hIC (p ^ e)).homology k) :=
  (envelopeFamily (C := C) γ).crystallineCohomologyIsoCechAlexander p hIC (p ^ e) he k

end AffineCrystalline.InfinitesimalSite
