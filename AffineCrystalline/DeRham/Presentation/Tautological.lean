/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The tautological presentation of an algebra

For an `A`-algebra `B`, we present `B` as a quotient of the polynomial ring
`MvPolynomial B A`, with one variable `[b]` for each `b : B`, by the relations
`[b₁] + [b₂] - [b₁ + b₂]`, `[b₁] [b₂] - [b₁ b₂]` and `a - [algebraMap A B a]`.
The induced presentation of the `B`-module `Ω[B⁄A]` has generators `db` and
the corresponding additivity, Leibniz and `A`-linearity relations; it is the
starting point of the construction of the de Rham complex through
presentations of modules.

## Main definitions

* `generators`: the generators `[b]`, `b : B`, of `B` as an `A`-algebra.
* `Relation`, `relation`: the tautological relations.
* `algebraPresentation`: the resulting `Algebra.Presentation`.
* `differentialRelation`, `differentialPresentation`: the induced presentation
  of `Ω[B⁄A]`.

## Main results

* `quotientMap_fac`: the tautological relations generate the kernel of
  evaluation.
* `differentialRelation_add`, `differentialRelation_mul`,
  `differentialRelation_algebraMap`: the relations of `differentialPresentation`.

## References

Following J. Riou's construction of the de Rham complex through presentations
of modules.
-/

universe u v

noncomputable section

namespace AffineCrystalline.DeRham.Presentation.Tautological

open MvPolynomial

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-! ## Algebra generators and relations -/

/-- The variables of the tautological presentation are the elements of `B`. -/
noncomputable def generators : Algebra.Generators A B B where
  val := id
  σ' := X
  aeval_val_σ' := by simp

@[simp]
theorem generators_val (b : B) : (generators (A := A) (B := B)).val b = b := rfl

@[simp]
theorem generators_eval_X (b : B) :
    aeval (R := A) (generators (A := A) (B := B)).val
      (X b : MvPolynomial B A) = b := by
  simp

/-- The three tautological algebra relations. -/
inductive Relation
  | add (b₁ b₂ : B)
  | mul (b₁ b₂ : B)
  | algebraMap (a : A)

/-- The polynomial relation associated to a tautological algebra relation. -/
@[simp]
noncomputable def relation : Relation (A := A) (B := B) → MvPolynomial B A
  | .add b₁ b₂ => X b₁ + X b₂ - X (b₁ + b₂)
  | .mul b₁ b₂ => X b₁ * X b₂ - X (b₁ * b₂)
  | .algebraMap a => C a - X (algebraMap A B a)

/-- Each tautological relation evaluates to zero in `B`. -/
@[simp]
theorem relation_eval_zero (r : Relation (A := A) (B := B)) :
    aeval (generators (A := A) (B := B)).val (relation r) = 0 := by
  cases r <;> simp [relation]

theorem relation_mem_ker (r : Relation (A := A) (B := B)) :
    relation r ∈ (generators (A := A) (B := B)).ker :=
  relation_eval_zero r

/-- The tautological relations generate an ideal contained in the kernel of
evaluation. -/
theorem span_relation_le_ker :
    Ideal.span (Set.range (relation (A := A) (B := B))) ≤
      (generators (A := A) (B := B)).ker := by
  rw [Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  exact relation_mem_ker r

/-! ## The evaluation quotient -/

/-- The map `b ↦ [b]` from `B` to the quotient of `MvPolynomial B A` by the
tautological relations; the relations make it a ring homomorphism. -/
noncomputable def quotientMap : B →+*
    MvPolynomial B A ⧸ Ideal.span (Set.range (relation (A := A) (B := B))) where
  toFun b := Ideal.Quotient.mk _ (X b)
  map_zero' := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨Relation.add 0 0, by simp [relation]⟩
  map_add' b₁ b₂ := by
    symm
    rw [← map_add, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨Relation.add b₁ b₂, by simp [relation, sub_eq_add_neg]⟩
  map_one' := by
    symm
    rw [← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨Relation.algebraMap 1, by simp [relation]⟩
  map_mul' b₁ b₂ := by
    symm
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨Relation.mul b₁ b₂, by simp [relation, sub_eq_add_neg]⟩

/-- Composing evaluation `MvPolynomial B A → B` with `quotientMap` gives the
quotient map; hence the tautological relations generate the kernel of
evaluation. -/
theorem quotientMap_fac :
    (quotientMap (A := A) (B := B)).comp
        (algebraMap (generators (A := A) (B := B)).Ring B) =
      Ideal.Quotient.mk _ := by
  ext p
  · symm
    erw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    refine Ideal.subset_span ⟨Relation.algebraMap p, ?_⟩
    dsimp [quotientMap, relation]
    rw [MvPolynomial.C_eq_smul_one]
    congr 1
    simp [Algebra.Generators.algebraMap_eq, generators, Algebra.smul_def]
  · dsimp [quotientMap]
    congr 1
    simp [Algebra.Generators.algebraMap_eq]

/-- The tautological presentation of `B` as an `A`-algebra. That its relations
generate the kernel of evaluation follows from `quotientMap_fac`. -/
noncomputable abbrev algebraPresentation :
    Algebra.Presentation A B B (Relation (A := A) (B := B)) where
  toGenerators := generators (A := A) (B := B)
  relation := relation (A := A) (B := B)
  span_range_relation_eq_ker := by
    apply le_antisymm
    · exact span_relation_le_ker
    · intro p hp
      have h := DFunLike.congr_fun (quotientMap_fac (A := A) (B := B)) p
      change algebraMap (generators (A := A) (B := B)).Ring B p = 0 at hp
      change (quotientMap (A := A) (B := B))
          (algebraMap (generators (A := A) (B := B)).Ring B p) =
        (Ideal.Quotient.mk _) p at h
      rw [hp, map_zero] at h
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h.symm

@[simp]
theorem algebraPresentation_relation_eval (r : Relation (A := A) (B := B)) :
    aeval (algebraPresentation (A := A) (B := B)).val
      ((algebraPresentation (A := A) (B := B)).relation r) = 0 :=
  Algebra.Presentation.aeval_val_relation
    (algebraPresentation (A := A) (B := B)) r

@[simp]
theorem algebraPresentation_generator_eval (b : B) :
    aeval (R := A) (algebraPresentation (A := A) (B := B)).val
      (X b : MvPolynomial B A) = b := by
  simp [generators]

/-! ## The induced differential presentation -/

/-- The relations of the presentation of `Ω[B⁄A]` induced by
`algebraPresentation`, as elements of the free `B`-module on the generators
`db`. -/
noncomputable def differentialRelation (r : Relation (A := A) (B := B)) : B →₀ B :=
  (Algebra.Presentation.differentialsRelations
    (algebraPresentation (A := A) (B := B))).relation r

@[simp]
theorem differentialRelation_add (b₁ b₂ : B) :
    differentialRelation (A := A) (B := B) (.add b₁ b₂) =
      Finsupp.single b₁ 1 + Finsupp.single b₂ 1 - Finsupp.single (b₁ + b₂) 1 := by
  dsimp [differentialRelation, Algebra.Presentation.differentialsRelations,
    algebraPresentation, relation]
  simp only [map_sub, map_add, KaehlerDifferential.mvPolynomialBasis_repr_D_X]
  rw [Finsupp.mapRange_sub (by simp), Finsupp.mapRange_add (by simp)]
  simp

@[simp]
theorem differentialRelation_mul (b₁ b₂ : B) :
    differentialRelation (A := A) (B := B) (.mul b₁ b₂) =
      b₁ • Finsupp.single b₂ 1 + b₂ • Finsupp.single b₁ 1 -
        Finsupp.single (b₁ * b₂) 1 := by
  dsimp [differentialRelation, Algebra.Presentation.differentialsRelations,
    algebraPresentation, relation, generators]
  simp only [map_sub, Derivation.leibniz, map_add, map_smul,
    KaehlerDifferential.mvPolynomialBasis_repr_D_X]
  rw [Finsupp.mapRange_sub (by simp), Finsupp.mapRange_add (by simp)]
  simp [smul_eq_mul]

@[simp]
theorem differentialRelation_algebraMap (a : A) :
    differentialRelation (A := A) (B := B) (.algebraMap a) =
      -Finsupp.single (algebraMap A B a) 1 := by
  dsimp [differentialRelation, Algebra.Presentation.differentialsRelations,
    algebraPresentation, relation]
  rw [MvPolynomial.C_eq_smul_one]
  simp only [map_sub, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero, zero_sub,
    map_neg, KaehlerDifferential.mvPolynomialBasis_repr_D_X]
  rw [Finsupp.mapRange_neg (by simp)]
  simp

/-- The presentation of the Kähler module induced by the tautological algebra presentation. -/
noncomputable abbrev differentialPresentation :
    Module.Presentation B (Ω[B⁄A]) where
  G := B
  R := Relation (A := A) (B := B)
  relation := differentialRelation (A := A) (B := B)
  toSolution := Algebra.Presentation.differentialsSolution
    (algebraPresentation (A := A) (B := B))
  toIsPresentation := Algebra.Presentation.differentialsSolution_isPresentation
    (algebraPresentation (A := A) (B := B))

@[simp]
theorem differentialPresentation_var (b : B) :
    (differentialPresentation (A := A) (B := B)).var b =
      KaehlerDifferential.D A B b := by
  rfl

/-- `differentialPresentation` is a presentation of `Ω[B⁄A]`. -/
theorem differentialPresentation_isPresentation :
    (differentialPresentation (A := A) (B := B)).toSolution.IsPresentation :=
  (differentialPresentation (A := A) (B := B)).toIsPresentation

end AffineCrystalline.DeRham.Presentation.Tautological
