/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.Ocris.DeRhamComparison
import AffineCrystalline.Ocris.PresentedEnvelope
import AffineCrystalline.Homology.CosimplicialContraction

/-!
# The vanishing lemma for the Čech nerve of `INF^{(e)}`

Let `e` be a positive integer with `e! = 0` in `A`.  Let `X^{(e)}(•)` be the Čech nerve of
the weakly initial object of `INF^{(e)}` (`Level A C e`) and `D(n) = Ocris(X^{(e)}(n))`.
Then `D(n)` is a presented PD envelope of `A[x_{i,c} : i ∈ [n], c ∈ C] → C`
(`cech_isPresentedEnvelope`).  For `α : [n] → [1]` consider the operators

  `h_α = ⋀^{q+1} (dx_{i,c} ↦ [α(i) = 1] dx_{i,c})`

on `Ω^{q+1}_{D(n)}` (`PresentedEnvelope.partialExt`).  They are compatible with
the cosimplicial structure, `h_{const 1} = id`, and `h_{const 0} = 0` because
`q + 1 ≥ 1`.  Hence they form a cosimplicial contraction of
`n ↦ Ω^{q+1}_{D(n)}`, and the alternating complex of this cosimplicial module is
exact.  This is the second input of the Bhatt–de Jong lemma
(`PositiveCechExact`).  The proof uses no freeness property of `Ω_{D(n)}`.

## Main definitions

* `EnvelopeFamily.cechι`: the structure map `A[x_{i,c}] → D(n)`.
* `EnvelopeFamily.vertexPred`: the predicate `(i, c) ↦ [α(i) = 1]` of
  `α : [n] → [1]`.
* `EnvelopeFamily.cechContraction`: the cosimplicial contraction of
  `n ↦ Ω^{q+1}_{D(n)}`.

## Main results

* `EnvelopeFamily.cech_isPresentedEnvelope`: `D(n)` is a presented PD envelope
  of `A[x_{i,c}] → C`.
* `EnvelopeFamily.cech_comparison_X`: the cosimplicial maps `D(m) → D(n)` act
  on variables by `x_{i,c} ↦ x_{f(i),c}`.
* `EnvelopeFamily.positiveCechExact`: the vanishing lemma; `PositiveCechExact e`
  holds if `e! = 0` in `A`.

## References

* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 019U](https://stacks.math.columbia.edu/tag/019U)
* B. Bhatt, A. J. de Jong, *Crystalline cohomology and de Rham cohomology*,
  arXiv:1110.5001
-/

open CategoryTheory DividedPowers
open scoped Simplicial

universe u

namespace AffineCrystalline.InfinitesimalSite

open Homology InfinitesimalThickening

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable {I : Ideal A} {γ : DividedPowers I}

namespace EnvelopeFamily

variable (E : EnvelopeFamily (A := A) (C := C) (γ := γ))
variable (e : ℕ) [NeZero e] (he : ((Nat.factorial e : ℕ) : A) = 0)

/-- The structure map `A[x_{i,c}] → D(n)`. -/
noncomputable abbrev cechι (n : ℕ) :
    MvPolynomial (Fin (n + 1) × C) A →ₐ[A] (E.envelope (Level.cechObj e n).obj).carrier :=
  (E.envelope (Level.cechObj e n).obj).map.comp (Level.cechMk e n)

include he in
/-- If `e! = 0` in `A`, `D(n)` is a PD envelope of the polynomial presentation
`A[x_{i,c} : i ∈ [n], c ∈ C] → C`, in the sense of `IsPresentedEnvelope`. -/
theorem cech_isPresentedEnvelope (n : ℕ) :
    IsPresentedEnvelope γ (E.cechι e n) (RingHom.ker (cechπ (A := A) (C := C) n).toRingHom)
      (E.envelope (Level.cechObj e n).obj).dividedPowers where
  contain := by
    refine le_trans (sup_le_sup_right ?_ _) (E.envelope (Level.cechObj e n).obj).isEnvelope.le
    have hk : RingHom.ker (Level.cechObj (A := A) (C := C) e n).obj.π.toRingHom =
        (RingHom.ker (cechπ (A := A) (C := C) n).toRingHom).map
          (Level.cechMk (A := A) (C := C) e n).toRingHom :=
      ker_truncate_eq_map _ _ _ _
    rw [hk, Ideal.map_map]
    exact le_rfl
  compat := (E.envelope (Level.cechObj e n).obj).isEnvelope.compat
  initial K' φ' δ' hK hcompat :=
    E.ocrisCech_isEnvelope e he n K' φ' δ' hK hcompat

/-- The vertex predicate `(i, c) ↦ [α i = 1]` of `α : [n] → [1]`. -/
def vertexPred {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) : Fin (n + 1) × C → Prop :=
  fun ic ↦ α.toOrderHom ic.1 = 1

instance {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) : DecidablePred (vertexPred (C := C) α) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- For `f : [m] → [n]`, the comparison map `D(m) → D(n)` along the induced map
of Čech objects sends `x_{i,c}` to `x_{f(i),c}`. -/
theorem cech_comparison_X {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : Fin (m + 1) × C) :
    EnvelopeChoice.comparison ((Level.ι e).map ((Level.cechNerve e).map f))
        (E.envelope (Level.cechObj e m).obj) (E.envelope (Level.cechObj e n).obj)
        (E.cechι e m (MvPolynomial.X s)) =
      E.cechι e n (MvPolynomial.X (Prod.map f.toOrderHom id s)) := by
  have h := DFunLike.congr_fun
    (EnvelopeChoice.comparison_spec ((Level.ι e).map ((Level.cechNerve e).map f))
      (E.envelope (Level.cechObj e m).obj) (E.envelope (Level.cechObj e n).obj)).1
    (Level.cechMk e m (MvPolynomial.X s))
  refine h.trans ?_
  change (E.envelope (Level.cechObj e n).obj).map
    ((Level.cechMap (A := A) (C := C) (e := e) f.toOrderHom).hom.toAlgHom
      (Level.cechMk e m (MvPolynomial.X (s.1, s.2)))) = _
  rw [Level.cechMap_X]
  rfl

include he in
/-- **The cosimplicial contraction of positive-degree PD forms.**  The operators
`h_α = ⋀^{q+1} (dx_{i,c} ↦ [α(i) = 1] dx_{i,c})` on `Ω^{q+1}_{D(n)}`. -/
noncomputable def cechContraction (q : ℕ) :
    CosimplicialContraction (RawBi.component (E.levelCechDeRham e) (q + 1)) where
  h n α := ModuleCat.ofHom (uliftLinearMap ((PresentedEnvelope.partialExt
    (E.cech_isPresentedEnvelope e he n) (q + 1) (vertexPred α)).restrictScalars A))
  nat {m n} f α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.down_injective
    exact PresentedEnvelope.partialExt_natural (E.cech_isPresentedEnvelope e he m)
      (E.cech_isPresentedEnvelope e he n) _
      (EnvelopeChoice.comparison_spec ((Level.ι e).map ((Level.cechNerve e).map f))
        (E.envelope (Level.cechObj e m).obj) (E.envelope (Level.cechObj e n).obj)).2
      (Prod.map f.toOrderHom id) (E.cech_comparison_X e f) (q + 1) (vertexPred α) x.down
  zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.down_injective
    exact LinearMap.congr_fun (PresentedEnvelope.partialExt_of_forall_not
      (E.cech_isPresentedEnvelope e he n) q _ (fun s hs ↦ by
        change (0 : Fin 2) = 1 at hs
        exact absurd hs (by decide))) x.down
  one n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.down_injective
    exact LinearMap.congr_fun (PresentedEnvelope.partialExt_of_forall
      (E.cech_isPresentedEnvelope e he n) (q + 1) _ (fun s ↦ rfl)) x.down

include he in
/-- **Vanishing lemma** [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA):
if `e! = 0` in `A`, then for every `q` the alternating complex of the cosimplicial module
`n ↦ Ω^{q+1}_{D(n)}` is exact. -/
theorem positiveCechExact : E.PositiveCechExact e := fun q n ↦
  (E.cechContraction e he q).exactAt n

end EnvelopeFamily

end AffineCrystalline.InfinitesimalSite
