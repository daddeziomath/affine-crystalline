# Affine crystalline cohomology and de Rham cohomology in Lean 4

[![CI](https://github.com/daddeziomath/affine-crystalline/actions/workflows/ci.yml/badge.svg)](https://github.com/daddeziomath/affine-crystalline/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23573534.svg)](https://doi.org/10.5281/zenodo.23573534)

A Lean 4 formalisation, built on Mathlib, of the **comparison between crystalline
cohomology and divided power de Rham cohomology** for an affine scheme `Spec C`
over a divided power base `(A, I, γ)` in which `p` is nilpotent, together with
the **existence of divided power envelopes**. The library contains no `sorry`,
and the main theorems have no hypotheses beyond the standard setting.

The cohomology is computed on a **bounded infinitesimal site**: its objects are
surjections of `A`-algebras `π : B → C`, without divided powers, whose kernel
has a uniform nilpotence exponent,

```
∃ e, ∀ x ∈ ker π, x ^ e = 0.
```

This is a property, not extra data, so truncations, coproducts and Čech nerves
are ordinary commutative algebra. Divided powers enter only through the
structure sheaf `Ocris`, which sends a thickening to its divided power envelope
and is used only through the universal property of envelopes (`IsDPEnvelope`).
In a divided power ideal, `x ^ n = n! · x^{[n]}`. Hence, when `n! = 0` in `A`,
every divided power ideal of an `A`-algebra satisfies `x ^ n = 0`, the envelope of
a thickening `B → C` is also the envelope of its truncation
`B / (x ^ n : x ∈ ker)`, and the latter lies in the subsite of thickenings of
exponent `n`. Since truncation is left adjoint to the inclusion of this subsite,
the cohomology of `Ocris` on `INF(C/A)` is already computed there. The main
theorems use the **Frobenius levels** `INF_e`, the thickenings whose kernel is
killed by `x ↦ x ^ (p ^ e)`, under the hypothesis `(p ^ e)! = 0` in `A`.

## Main results

Let `(A, I, γ)` be a divided power ring with `p` prime, `p ∈ I` and `p`
nilpotent in `A`, let `C` be an `A`-algebra with `I · C = 0`, and let `e` be an
integer with `(p ^ e)! = 0` in `A`. Write `INF(C/A)` for the big infinitesimal
site, `INF_e` (`Level A C (p ^ e)`) for its subsite of thickenings whose kernel is
killed by `x ↦ x ^ (p ^ e)`, `X_e(n)` for the Čech objects of `INF_e`, and
`D(n) = Ocris(X_e(n))`; then `D(n)` is a compatible divided power envelope of
`A[x_{i,c} : i ∈ [n], c ∈ C] → C`. For every `k`:

| Statement | Lean |
| --- | --- |
| `H^k(RΓ(INF(C/A), Ocris)) ≅ H^k(Ω•_{D(0)})` | `crystallineCohomologyIsoDeRham` |
| `lim I•` and `Ω•_{D(0)}` are connected by quasi-isomorphisms | `affineDeRhamComparison` |
| `H^k(RΓ(INF(C/A), Ocris)) ≅ H^k(D(0) → D(1) → D(2) → ⋯)` | `crystallineCohomologyIsoCechAlexander` |
| Every ideal of an `A`-algebra has a divided power envelope compatible with `γ` | `DPEnvelope.hasDPEnvelope` |

If `(p : A) ^ N = 0`, the hypothesis `(p ^ e)! = 0` holds for `e = N`
(`natCast_factorial_pow_eq_zero`). Since the `p`-adic valuation of `(p ^ e)!` is
`(p ^ e - 1) / (p - 1)`, it already holds as soon as `p ^ ((p ^ e - 1) / (p - 1)) = 0`
in `A`, so `e` of the order of `log_p N` suffices (this remark is not formalised).

The three comparison theorems are stated in
[`MainTheorems.lean`](AffineCrystalline/MainTheorems.lean), in the namespace
`AffineCrystalline.InfinitesimalSite`, for the envelope family `envelopeFamily`
obtained from the existence of envelopes:

```lean
theorem crystallineCohomologyIsoDeRham (k : ℕ) :
    Nonempty (((HomotopyCategory.homologyFunctor (ModuleCat.{u + 1} A)
        (ComplexShape.up ℕ) k).obj (envelopeFamily (C := C) γ).ocrisDerivedGlobalSections) ≅
      ((envelopeFamily (C := C) γ).ocrisDeRhamComplex.obj
        (Level.cechObj (p ^ e) 0).obj).homology k)
```

with the section variables

```lean
variable (p : ℕ) [Fact p.Prime] [IsCrystallineBase p A I]
  (hIC : I.map (algebraMap A C) = ⊥) (e : ℕ) (he : ((Nat.factorial (p ^ e) : ℕ) : A) = 0)
```

The same statements for an arbitrary family of envelopes are in the namespace
`AffineCrystalline.InfinitesimalSite.EnvelopeFamily`, in
[`Ocris/CechPoincare.lean`](AffineCrystalline/Ocris/CechPoincare.lean) and
[`Ocris/CechAlexander.lean`](AffineCrystalline/Ocris/CechAlexander.lean); they are
proved on the subsite `Level A C n` of thickenings of exponent `n`, for every
`n > 0` with `n! = 0` in `A`, without using that `p` is nilpotent. The
existence of envelopes is proved in
[`Envelope/Construction.lean`](AffineCrystalline/Envelope/Construction.lean),
following the representability argument of Stacks, Tag 07H8. All these results
depend only on the axioms `propext`, `Classical.choice` and `Quot.sound` (see
[`scripts/CheckAxioms.lean`](scripts/CheckAxioms.lean)).

## Other results

The library also contains, among others:

- divided power Kähler differentials, their universal property, and the
  isomorphism `Ω_D ≅ D ⊗_B Ω_{B/A}` for a divided power envelope `D` of `B`;
- the divided power de Rham complex in all degrees, following J. Riou's
  construction of the de Rham complex through presentations of modules;
- a one-variable divided power Poincaré lemma and the relative Poincaré lemma
  for the Čech nerve, proved from the universal property of envelopes only;
- first-quadrant bicomplexes, acyclic assembly lemmas and the double complex
  lemma of Bhatt and de Jong;
- cosimplicial contractions and exactness of alternating coface complexes;
- enough injectives and limits in large functor categories, invariance of
  derived limits under restriction along a left adjoint, and the Čech
  computation `R^n lim F ≅ Ȟ^n(F)` for categories with Čech nerve data;
- divided power structures on products of ideals and their restriction to
  subrings, used in the construction of envelopes;
- results on divided power algebras (Roby monomials, relation ideals) towards an
  explicit description of envelopes.

## Building

You need [elan](https://github.com/leanprover/elan). The Lean toolchain and the
Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
git clone https://github.com/daddeziomath/affine-crystalline.git
cd REPO
lake exe cache get                        # download the prebuilt Mathlib
lake build                                # build the library
lake env lean scripts/CheckAxioms.lean    # print the axioms of the main theorems
```

## Repository map

| Path | Content |
| --- | --- |
| `AffineCrystalline/InfinitesimalSite/` | The big infinitesimal site, the subsites `Level A C n` of exponent `n` and the Frobenius levels `INF_e = Level A C (p ^ e)`, Frobenius exponents, the truncation adjunction, coproducts, the Čech nerve, envelope choices |
| `AffineCrystalline/Ocris.lean`, `Ocris/` | The structure sheaf `Ocris`, derived global sections, restriction to `Level A C n` when `n! = 0`, the Čech–Alexander theorem and the de Rham comparison |
| `AffineCrystalline/PDDifferentials.lean`, `PDDifferentials/` | Divided power Kähler differentials and envelopes (`IsDPEnvelope`) |
| `AffineCrystalline/DeRham/` | Algebraic and divided power de Rham complexes, form calculus, Poincaré lemma |
| `AffineCrystalline/Homology/` | Bicomplexes, total complexes, the Bhatt–de Jong lemma, cosimplicial contractions |
| `AffineCrystalline/Cohomology/` | Čech computation of derived limits, injectives in functor categories |
| `AffineCrystalline/Envelope/` | Existence of envelopes (`Construction.lean`), consequences of their universal property, special cases, divided power algebras |
| `AffineCrystalline/MainTheorems.lean` | The main theorems for the envelope family given by the existence theorem |
| `AffineCrystalline/AffineCrystalline.lean` | Imports the whole library |
| `scripts/CheckAxioms.lean` | Prints the axioms of the main theorems |

## Scope

The results concern the affine case with trivial coefficients. Crystalline
cohomology is computed as `RΓ(INF(C/A), Ocris)`; the library does not define
the crystalline site of divided power thickenings, and its comparison with
`RΓ(INF(C/A), Ocris)` is classical background, not part of the formalisation.
Also not formalised are: an explicit description of divided power envelopes as
quotients of divided power algebras, non-affine objects and the Zariski or
étale topology, globalisation to schemes, and coefficients in crystals.

## Acknowledgements

This work builds on Mathlib, and in particular on the divided power theory of
Antoine Chambert-Loir and María Inés de Frutos-Fernández. Two files in
`AffineCrystalline/DeRham/Presentation/` are due to Joël Riou and keep his
copyright notice.

This work was by the Agence Nationale de la Recherche (ANR-25-CE40-7869-01) and the IdEx University of Strasbourg (BORÉAL). We thank Anthropic for access to Claude through the Claude Team plan for scientists.

## Citing

See [`CITATION.cff`](CITATION.cff), or use GitHub's "Cite this repository" button.

## License

Apache License 2.0, the license of Mathlib; see [`LICENSE`](LICENSE).
