/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.DeRhamComparison
import AffineCrystalline.Cohomology.CechDerived

/-!
# Crystalline cohomology via the Čech–Alexander complex

Let `e` be a positive integer with `e! = 0` in `A`.  Let `X^{(e)}(•)` be the Čech nerve of
the weakly initial object of `INF^{(e)}` (`Level A C e`), and put
`D(n) = Ocris(X^{(e)}(n))`.  By `ocrisCech_isEnvelope`, `D(n)` is a PD envelope of
the polynomial presentation `A[x_{i,c} : i ∈ [n], c ∈ C] → C`.

This file shows that the cohomology of `RΓ(INF(C/A), Ocris)` is the cohomology
of the Čech–Alexander complex

  `D(0) → D(1) → D(2) → ⋯`.

The argument uses neither the relative Poincaré lemma nor the vanishing lemma:
derived global sections on `INF(C/A)` agree with those on `INF^{(e)}`
(`ocrisDerivedGlobalSectionsIsoLimComplex`), and higher derived limits on
`INF^{(e)}` are computed by the Čech complex of the Čech nerve
(`Cohomology.Cech.rightDerivedLimIsoCech`).

For a prime `p` and the Frobenius level `e = p ^ f`, the site `INF_f` of the
accompanying article, the hypothesis reads `(p ^ f)! = 0` in `A`; it holds for
`f = N` if `p ^ N = 0` in `A` (`natCast_factorial_pow_eq_zero`).

## Main results

* `EnvelopeFamily.levelRightDerivedIsoCechAlexander`: `R^n lim` of `ocris` on
  `INF^{(e)}` is the `n`-th cohomology of the Čech–Alexander complex.
* `EnvelopeFamily.crystallineCohomologyIsoCechAlexander`: if `e! = 0` in `A`,
  `H^k(RΓ(INF(C/A), Ocris)) ≅ H^k(D(•))`.
* `EnvelopeFamily.cechAlexander_homology_independent`: the cohomology of the
  Čech–Alexander complex does not depend on the choice of `e` with `e! = 0` in `A`.

## References

* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
* B. Bhatt, A. J. de Jong, *Crystalline cohomology and de Rham cohomology*,
  arXiv:1110.5001
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace AffineCrystalline.InfinitesimalSite

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
variable (hIC : I.map (algebraMap A C) = ⊥)

section Level

variable (e : ℕ) [NeZero e]

/-- **Čech–Alexander computation on `INF^{(e)}`.**  The higher derived limits of
`ocris` on `INF^{(e)}` (`Level A C e`) are the cohomology modules of the
Čech–Alexander complex `n ↦ Ocris(X^{(e)}(n))`. -/
noncomputable def levelRightDerivedIsoCechAlexander (n : ℕ) :
    ((lim : (Level A C e ⥤ ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A).rightDerived n).obj
        (E.levelOcrisModule p hIC e) ≅
      (E.ocrisCechComplex p hIC e).homology n :=
  Cohomology.Cech.rightDerivedLimIsoCech (Level.cechNerveData e) _ n

end Level

section Comparison

variable (n : ℕ) [NeZero n]

/-- **Crystalline cohomology is Čech–Alexander cohomology (affine case).**
If `n! = 0` in `A`, the `k`-th cohomology of `RΓ(INF(C/A), Ocris)` is the `k`-th
cohomology of the Čech–Alexander complex `D(•) = Ocris(X^{(n)}(•))`.  For the
Frobenius level `n = p ^ e`, the site `INF_e` of the accompanying article, the
hypothesis reads `(p ^ e)! = 0` in `A`. -/
theorem crystallineCohomologyIsoCechAlexander (hn : ((Nat.factorial n : ℕ) : A) = 0)
    (k : ℕ) :
    Nonempty (((HomotopyCategory.homologyFunctor (ModuleCat.{u + 1} A) (ComplexShape.up ℕ) k).obj
        (ocrisDerivedGlobalSections E)) ≅ (E.ocrisCechComplex p hIC n).homology k) :=
  ⟨(HomotopyCategory.homologyFunctor _ _ k).mapIso
      (E.ocrisDerivedGlobalSectionsIsoLimComplex p hIC n hn) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ k).app _ ≪≫
    (E.ocrisCechZigzag p hIC n).homologyIso k⟩

/-- The cohomology of the Čech–Alexander complex `Ocris(X^{(n)}(•))` does not depend
on the choice of `n` with `n! = 0` in `A`: both sides compute `RΓ(INF(C/A), Ocris)`. -/
theorem cechAlexander_homology_independent (n' : ℕ) [NeZero n']
    (hn : ((Nat.factorial n : ℕ) : A) = 0) (hn' : ((Nat.factorial n' : ℕ) : A) = 0) (k : ℕ) :
    Nonempty ((E.ocrisCechComplex p hIC n).homology k ≅
      (E.ocrisCechComplex p hIC n').homology k) := by
  obtain ⟨φ⟩ := E.crystallineCohomologyIsoCechAlexander p hIC n hn k
  obtain ⟨ψ⟩ := E.crystallineCohomologyIsoCechAlexander p hIC n' hn' k
  exact ⟨φ.symm ≪≫ ψ⟩

end Comparison

end EnvelopeFamily

end AffineCrystalline.InfinitesimalSite
