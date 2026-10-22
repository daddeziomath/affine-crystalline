/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exterior powers of a quotient module

Let `M` be a module over a commutative ring `R`, `N ⊆ M` a submodule and `n ∈ ℕ`.
We show that the kernel of the map `⋀^n M → ⋀^n (M/N)` induced by the quotient map
is the submodule spanned by the wedges `m₁ ∧ ⋯ ∧ mₙ` with some `mᵢ ∈ N`.

One inclusion is immediate. For the other, we use the universal property of
`⋀^n (M/N)` to construct a map `⋀^n (M/N) → ⋀^n M / R_n`, where `R_n` is the
relation submodule, by choosing lifts of elements of `M/N`; the relations ensure
that the result does not depend on the choice of lifts. This map is a left inverse
of the map `⋀^n M / R_n → ⋀^n (M/N)` induced by the quotient map.

## Main definitions

* `exteriorQuotientRelations N n`: the submodule of `⋀^n M` spanned by the wedges
  with at least one factor in `N`.

## Main results

* `exteriorPower_ker_map_mkQ`: the kernel of `⋀^n M → ⋀^n (M/N)` equals
  `exteriorQuotientRelations N n`.
-/

universe u v

noncomputable section

namespace AffineCrystalline.DeRham

open Function

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The wedges `m₁ ∧ ⋯ ∧ mₙ` in `⋀^n M` with at least one factor in `N`. -/
def exteriorQuotientRelationFamily (N : Submodule R M) (n : ℕ) :
    Set (⋀[R]^n M) :=
  {ω | ∃ (i : Fin n) (m : Fin n → M), m i ∈ N ∧
    ω = exteriorPower.ιMulti R n m}

/-- The submodule of `⋀^n M` spanned by the wedges with at least one factor in `N`. -/
def exteriorQuotientRelations (N : Submodule R M) (n : ℕ) :
    Submodule R (⋀[R]^n M) :=
  Submodule.span R (exteriorQuotientRelationFamily N n)

/-- The wedges with a factor in `N` are killed by `⋀^n M → ⋀^n (M/N)`. -/
theorem exteriorQuotientRelationFamily_subset_ker
    (N : Submodule R M) (n : ℕ) :
    exteriorQuotientRelationFamily N n ⊆
      LinearMap.ker (exteriorPower.map n N.mkQ) := by
  rintro ω ⟨i, m, hmi, rfl⟩
  change exteriorPower.map n N.mkQ (exteriorPower.ιMulti R n m) = 0
  rw [exteriorPower.map_apply_ιMulti]
  exact (exteriorPower.ιMulti R n).toMultilinearMap.map_coord_zero i
    ((Submodule.Quotient.mk_eq_zero _).2 hmi)

/-- Wedges with a factor in `N` lie in the kernel of `⋀^n M → ⋀^n (M/N)`. -/
theorem exteriorQuotientRelations_le_ker
    (N : Submodule R M) (n : ℕ) :
    exteriorQuotientRelations N n ≤
      LinearMap.ker (exteriorPower.map n N.mkQ) := by
  rw [exteriorQuotientRelations, Submodule.span_le]
  exact exteriorQuotientRelationFamily_subset_ker N n

namespace ExteriorPowerQuotient

variable (N : Submodule R M) (n : ℕ)

/-- The quotient `⋀^n M / exteriorQuotientRelations N n`. -/
abbrev RelationQuotient : Type max u v :=
  (⋀[R]^n M) ⧸ exteriorQuotientRelations N n

/-- A chosen lift to `M` of an element of `M/N`. -/
noncomputable def representative : (M ⧸ N) → M :=
  Classical.choose N.mkQ_surjective.hasRightInverse

/-- The chosen lift `representative N x` is a lift of `x`. -/
theorem representative_spec (x : M ⧸ N) :
    N.mkQ (representative N x) = x :=
  Classical.choose_spec N.mkQ_surjective.hasRightInverse x

@[simp]
theorem quotientMk_representative (x : M ⧸ N) :
    (Submodule.Quotient.mk (representative N x) : M ⧸ N) = x := by
  change N.mkQ (representative N x) = x
  exact representative_spec N x

/-- A wedge with a factor in `N` vanishes modulo the relations. -/
theorem mkQ_ιMulti_eq_zero_of_mem (i : Fin n) (m : Fin n → M)
    (hmi : m i ∈ N) :
    (exteriorQuotientRelations N n).mkQ (exteriorPower.ιMulti R n m) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨i, m, hmi, rfl⟩

/-- Modulo the relations, changing one factor of a wedge by an element of `N`
does not change its class. -/
theorem mkQ_ιMulti_update_eq [DecidableEq (Fin n)]
    (m : Fin n → M) (i : Fin n) (x y : M)
    (hxy : x - y ∈ N) :
    (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (Function.update m i x)) =
      (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (Function.update m i y)) := by
  rw [← sub_eq_zero, ← map_sub]
  calc
    (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (Function.update m i x) -
          exteriorPower.ιMulti R n (Function.update m i y)) =
      (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (Function.update m i (x - y))) := by
          congr 1
          exact (exteriorPower.ιMulti R n).toMultilinearMap.map_update_sub m i x y |>.symm
    _ = 0 := mkQ_ιMulti_eq_zero_of_mem N n i
      (Function.update m i (x - y)) (by simpa)

/-- Modulo the relations, the wedge of the chosen lifts of `Function.update x i a` may be
computed using any lift `y` of `a` in the `i`-th slot. -/
theorem mkQ_ιMulti_representative_comp_update [DecidableEq (Fin n)]
    (x : Fin n → M ⧸ N) (i : Fin n) (a : M ⧸ N) (y : M) (hy : N.mkQ y = a) :
    (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (representative N ∘ Function.update x i a)) =
      (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (Function.update (representative N ∘ x) i y)) := by
  rw [Function.comp_update]
  refine mkQ_ιMulti_update_eq N n _ i _ _ ((Submodule.Quotient.eq N).1 ?_)
  rw [quotientMk_representative]
  exact hy.symm

/-- The alternating map `(M/N)^n → ⋀^n M / exteriorQuotientRelations N n` sending
`(x₁, …, xₙ)` to the class of `m₁ ∧ ⋯ ∧ mₙ`, where `mᵢ` is a lift of `xᵢ`. It does
not depend on the choice of lifts, by `mkQ_ιMulti_update_eq`. -/
noncomputable def liftAlternating :
    (M ⧸ N) [⋀^Fin n]→ₗ[R] RelationQuotient N n where
  toFun x := (exteriorQuotientRelations N n).mkQ
    (exteriorPower.ιMulti R n (representative N ∘ x))
  map_update_add' x i a b := by
    rw [mkQ_ιMulti_representative_comp_update N n x i (a + b)
        (representative N a + representative N b) (by simp only [map_add, representative_spec]),
      (exteriorPower.ιMulti R n).map_update_add, map_add, Function.comp_update,
      Function.comp_update]
  map_update_smul' x i c a := by
    rw [mkQ_ιMulti_representative_comp_update N n x i (c • a) (c • representative N a)
        (by simp only [map_smul, representative_spec]),
      (exteriorPower.ιMulti R n).map_update_smul, map_smul, Function.comp_update]
  map_eq_zero_of_eq' x i j hij hne := by
    rw [(exteriorPower.ιMulti R n).map_eq_zero_of_eq (representative N ∘ x)
      (by simp only [Function.comp_apply, hij]) hne, map_zero]

/-- The linear map `⋀^n (M/N) → ⋀^n M / exteriorQuotientRelations N n` induced by
`liftAlternating`. -/
noncomputable def lift :
    (⋀[R]^n (M ⧸ N)) →ₗ[R] RelationQuotient N n :=
  exteriorPower.alternatingMapLinearEquiv (liftAlternating N n)

@[simp]
theorem lift_ιMulti (x : Fin n → (M ⧸ N)) :
    lift N n (exteriorPower.ιMulti R n x) =
      (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n (representative N ∘ x)) := by
  simp [lift, liftAlternating]

/-- Modulo the relations, a wedge only depends on its factors modulo `N`. -/
theorem mkQ_ιMulti_congr (m m' : Fin n → M)
    (h : ∀ i, N.mkQ (m i) = N.mkQ (m' i)) :
    (exteriorQuotientRelations N n).mkQ (exteriorPower.ιMulti R n m) =
      (exteriorQuotientRelations N n).mkQ (exteriorPower.ιMulti R n m') := by
  rw [← sub_eq_zero, ← map_sub]
  have htel := MultilinearMap.map_piecewise_sub_map_piecewise
    (exteriorPower.ιMulti R n).toMultilinearMap m m' m Finset.univ
  simp only [Finset.piecewise_univ] at htel
  calc
    (exteriorQuotientRelations N n).mkQ
        (exteriorPower.ιMulti R n m - exteriorPower.ιMulti R n m') =
      (exteriorQuotientRelations N n).mkQ
        (∑ i,
          exteriorPower.ιMulti R n (fun j ↦
            if j ∈ Finset.univ then
              if j < i then m j else if j = i then m j - m' j else m' j
            else m j)) := congrArg _ htel
    _ = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      apply mkQ_ιMulti_eq_zero_of_mem N n i
      simp only [Finset.mem_univ, ↓reduceIte, lt_self_iff_false]
      apply (Submodule.Quotient.mk_eq_zero _).1
      change N.mkQ (m i - m' i) = 0
      rw [map_sub, h i, sub_self]

/-- The composition `⋀^n M → ⋀^n (M/N) → ⋀^n M / exteriorQuotientRelations N n` of
the induced map with `lift N n` is the quotient map. -/
theorem lift_comp_map_mkQ :
    (lift N n).comp (exteriorPower.map n N.mkQ) =
      (exteriorQuotientRelations N n).mkQ := by
  apply exteriorPower.linearMap_ext
  ext m
  change lift N n (exteriorPower.map n N.mkQ
    (exteriorPower.ιMulti R n m)) =
      (exteriorQuotientRelations N n).mkQ (exteriorPower.ιMulti R n m)
  rw [exteriorPower.map_apply_ιMulti, lift_ιMulti]
  apply mkQ_ιMulti_congr N n
  intro i
  exact representative_spec N _

/-- The kernel of `⋀^n M → ⋀^n (M/N)` is contained in `exteriorQuotientRelations N n`. -/
theorem ker_map_le_relations :
    LinearMap.ker (exteriorPower.map n N.mkQ) ≤ exteriorQuotientRelations N n := by
  intro x hx
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← lift_comp_map_mkQ N n,
    LinearMap.comp_apply, LinearMap.mem_ker.1 hx, map_zero]

end ExteriorPowerQuotient

/-- The kernel of `⋀^n M → ⋀^n (M/N)` is spanned by the wedges with at least one
factor in `N`. -/
theorem exteriorPower_ker_map_mkQ (N : Submodule R M) (n : ℕ) :
    LinearMap.ker (exteriorPower.map n N.mkQ) = exteriorQuotientRelations N n := by
  apply le_antisymm
  · exact ExteriorPowerQuotient.ker_map_le_relations N n
  · exact exteriorQuotientRelations_le_ker N n

end AffineCrystalline.DeRham
