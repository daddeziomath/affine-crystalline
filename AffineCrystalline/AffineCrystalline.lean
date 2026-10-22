/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Setting
import AffineCrystalline.SquareZero
import AffineCrystalline.PDDifferentials
import AffineCrystalline.PDDifferentials.Representability
import AffineCrystalline.DeRham
import AffineCrystalline.InfinitesimalSite.Basic
import AffineCrystalline.InfinitesimalSite.Envelope
import AffineCrystalline.InfinitesimalSite.EnvelopeConstruction
import AffineCrystalline.DeRham.Abstract
import AffineCrystalline.DeRham.PDRelations
import AffineCrystalline.DeRham.RiouBasic
import AffineCrystalline.DeRham.RiouPresentation
import AffineCrystalline.DeRham.Presentation.Tautological
import AffineCrystalline.DeRham.PDDescent
import AffineCrystalline.DeRham.PDComplexCriterion
import AffineCrystalline.DeRham.HigherDifferential
import AffineCrystalline.DeRham.RiouRelationInduction
import AffineCrystalline.DeRham.PDKaehlerQuotient
import AffineCrystalline.DeRham.RiouComplex
import AffineCrystalline.DeRham.RiouDegreeOne
import AffineCrystalline.DeRham.RiouDegreeTwo
import AffineCrystalline.DeRham.RiouFull
import AffineCrystalline.DeRham.ExteriorPowerQuotient
import AffineCrystalline.DeRham.QuotientComplex
import AffineCrystalline.DeRham.QuotientKernel
import AffineCrystalline.DeRham.PDStabilityFull
import AffineCrystalline.DeRham.Construction.ExteriorSquareZero
import AffineCrystalline.DeRham.Construction.RelationExteriorQuotient
import AffineCrystalline.DeRham.CharacteristicZero
import AffineCrystalline.Envelope.Universal
import AffineCrystalline.Envelope.Construction
import AffineCrystalline.Envelope.Existence
import AffineCrystalline.Envelope.PDKaehlerComparison
import AffineCrystalline.Envelope.SpecialCases
import AffineCrystalline.Envelope.FreeConstruction.RatAlgebra
import AffineCrystalline.Envelope.FreeConstruction.DPAlgebraAugmentation
import AffineCrystalline.Envelope.FreeConstruction.PositiveDPStructure
import AffineCrystalline.Envelope.FreeConstruction.RelationGenerators
import AffineCrystalline.Envelope.FreeConstruction.PositiveIdeal
import AffineCrystalline.Envelope.FreeConstruction.RobyDpowConstruction
import AffineCrystalline.Envelope.FreeConstruction.IncludedEnvelopeConstruction
import AffineCrystalline.Envelope.FreeConstruction.J12Stability
import AffineCrystalline.Envelope.FreeConstruction.RobyBasisFinite
import AffineCrystalline.Envelope.FreeConstruction.RobyBasisPositive
import AffineCrystalline.Envelope.FreeConstruction.GeneralEnvelopeQuotient
import AffineCrystalline.Envelope.FreeConstruction.UniversalProperty
import AffineCrystalline.Envelope.FreeConstruction.UniversalDP
import AffineCrystalline.Envelope.FreeConstruction.UniversalDPConstruction
import AffineCrystalline.Envelope.FreeConstruction.RatEnvelope
import AffineCrystalline.Envelope.FreeConstruction.RobyIndependence
import AffineCrystalline.Envelope.FreeConstruction.RobyBasisGrade
import AffineCrystalline.Envelope.FreeConstruction.RobyBasisIndependence
import AffineCrystalline.Envelope.FreeConstruction.J12GeneratorStability
import AffineCrystalline.Envelope.FreeConstruction.J12HigherStability
import AffineCrystalline.Ocris
import AffineCrystalline.InfinitesimalSite.Topology
import AffineCrystalline.Ocris.Cohomology
import AffineCrystalline.Ocris.DeRham
import AffineCrystalline.InfinitesimalSite.Filtration
import AffineCrystalline.Homology.Elementwise
import AffineCrystalline.Homology.TotM
import AffineCrystalline.Cohomology.Cech
import AffineCrystalline.Ocris.Filtration
import AffineCrystalline.Homology.TotQuasiIso
import AffineCrystalline.Homology.TotProjection
import AffineCrystalline.Homology.CosimplicialTot
import AffineCrystalline.Ocris.DeRhamComparison
import AffineCrystalline.Homology.CosimplicialContraction
import AffineCrystalline.Ocris.PDDerivationExtension
import AffineCrystalline.Ocris.PresentedEnvelope
import AffineCrystalline.Ocris.CechVanishing
import AffineCrystalline.DeRham.FormCalculus
import AffineCrystalline.DeRham.OneVariablePoincare
import AffineCrystalline.Ocris.PresentedEnvelopeTools
import AffineCrystalline.Ocris.CechPoincare
import AffineCrystalline.Ocris.CechAlexander
import AffineCrystalline.Cohomology.CechDerived
import AffineCrystalline.MainTheorems

/-!
# Affine crystalline cohomology in Lean

Let `p` be a prime, `(A, I, γ)` a divided power ring with `p ∈ I` and `p` nilpotent
in `A`, and `C` an `A`-algebra with `I C = 0`. This library computes the
crystalline cohomology of `C` over `A`, with trivial coefficients, in terms of
divided power envelopes of polynomial presentations of `C`.

Cohomology is taken on the big infinitesimal site `INF(C/A)`
(`InfinitesimalThickening A C`): its objects are surjections of `A`-algebras
`B → C` whose kernel has a bounded nilpotence exponent, and its morphisms are
`A`-algebra maps over `C`; no divided powers are part of the objects. Divided
powers enter only through the structure sheaf `ocris`, which sends a thickening
to a compatible divided power envelope of its kernel and is used only through
the universal property `IsDPEnvelope`. Envelopes exist
(`DPEnvelope.hasDPEnvelope`, in `Envelope/Construction.lean`); the results are
stated for an arbitrary `EnvelopeFamily`, and in `MainTheorems.lean` for the
family `envelopeFamily` obtained from this existence theorem.

Fix `e` with `(p ^ e)! = 0` in `A`, and let `INF_e = Level A C (p ^ e)` be the
Frobenius level: the full subcategory of thickenings whose kernel is killed by
`x ↦ x ^ (p ^ e)`. If `p ^ N = 0` in `A`, one may take `e = N`
(`natCast_factorial_pow_eq_zero`); more precisely, since the `p`-adic valuation of
`(p ^ e)!` is `(p ^ e - 1) / (p - 1)`, the condition holds as soon as
`p ^ ((p ^ e - 1) / (p - 1)) = 0` in `A`. Every element `x` of a divided power ideal
of an `A`-algebra satisfies `x ^ (p ^ e) = (p ^ e)! x^{[p ^ e]} = 0`
(`dividedPowers_pow_eq_zero_of_factorial_eq_zero`). Let `X_e(•)` be the Čech nerve
of the weakly initial object of `INF_e`, and put `D(n) = Ocris(X_e(n))`, a divided
power envelope of `A[x_{i,c} : i ∈ [n], c ∈ C] → C`. The truncation functor
`INF(C/A) ⥤ INF_e` is left adjoint to the inclusion and does not change `Ocris`, so
`RΓ(INF(C/A), Ocris) ≅ RΓ(INF_e, Ocris)`
(`EnvelopeFamily.ocrisDerivedGlobalSectionsIsoLevel`, in `Ocris/Filtration.lean`);
the latter is computed by the Čech complex of `X_e(•)`.

The library indexes the exponent filtration by an arbitrary exponent `n`: we write
`INF^{(n)}` for the full subcategory `Level A C n` of thickenings of exponent `n`,
so that `INF_e = INF^{(p ^ e)}`. The comparison results for an arbitrary envelope
family are proved on `INF^{(n)}` for every `n > 0` with `n! = 0` in `A`, and use
neither `p` nor the nilpotence of `p`; the Frobenius levels are the special case
`n = p ^ e`.

## Main results

* `DPEnvelope.hasDPEnvelope` (`Envelope/Construction.lean`): every ideal of an
  `A`-algebra has a divided power envelope compatible with `γ`.
* `crystallineCohomologyIsoDeRham`, `affineDeRhamComparison`,
  `crystallineCohomologyIsoCechAlexander` (`MainTheorems.lean`): the statements
  below for the envelope family given by `DPEnvelope.hasDPEnvelope`.
* `EnvelopeFamily.crystallineCohomologyIsoDeRham`
  (`Ocris/CechPoincare.lean`): `H^k(RΓ(INF(C/A), Ocris)) ≅ H^k(Ω^•_{D(0)})`, where
  `Ω^•_{D(0)}` is the divided power de Rham complex of the envelope `D(0)` of
  `A[x_c : c ∈ C] → C`.
* `EnvelopeFamily.affineDeRhamComparison`
  (`Ocris/CechPoincare.lean`): the complex computing `RΓ(INF(C/A), Ocris)` is
  connected to `Ω^•_{D(0)}` by a zigzag of quasi-isomorphisms.
* `EnvelopeFamily.crystallineCohomologyIsoCechAlexander`
  (`Ocris/CechAlexander.lean`): `H^n(RΓ(INF(C/A), Ocris))` is the `n`-th
  cohomology of the Čech–Alexander complex `D(0) → D(1) → D(2) → ⋯`.

## Organisation

* `Setting`, `SquareZero`: the standing hypotheses and divided powers on
  square-zero extensions.
* `PDDifferentials`: divided power derivations and the module `Ω_{B,δ}` of
  divided power Kähler differentials, the predicate `IsDPEnvelope`, and the
  differentials of an envelope.
* `DeRham`: the de Rham complex (following J. Riou's construction via
  presentations of modules), its divided power quotient, and the one-variable
  divided power Poincaré lemma.
* `Envelope`: the existence of divided power envelopes, consequences of their
  universal property, independence of the choice, special cases, and results
  on divided power algebras towards an explicit construction.
* `InfinitesimalSite`: the site `INF(C/A)`, the exponent filtration by the
  subcategories `INF^{(e)}`, the truncation functor `INF(C/A) ⥤ INF^{(e)}` and its
  adjunction with the inclusion, binary coproducts and Čech nerves, envelopes of
  thickenings, and the chaotic topology.
* `ocris`: the structure sheaf, its derived global sections, their restriction
  to `INF^{(e)}`, the PD de Rham complex on the site, the vanishing lemma, the
  relative Poincaré lemma, and the two comparison theorems.
* `Cohomology`: Čech computation of higher derived limits, and enough injectives
  in functor categories.
* `Homology`: total complexes of bicomplexes, cosimplicial contractions, and the
  Bhatt–de Jong lemma for cosimplicial cochain complexes.

## References

* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* B. Bhatt, A. J. de Jong, *Crystalline cohomology and de Rham cohomology*,
  arXiv:1110.5001
* P. Berthelot, A. Ogus, *Notes on crystalline cohomology*, Princeton
  University Press, 1978
-/
