/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.DeRham.RiouComplex
import AffineCrystalline.DeRham.RiouPresentation
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The de Rham differential in degree one

Let `I ⊆ B ⊗[A] B` be the kernel of the multiplication map, so that
`Ω[B⁄A] = I / I²` with `db` the class of `1 ⊗ b - b ⊗ 1`. We construct the
differential `d : Ω[B⁄A] → ⋀[B]^2 Ω[B⁄A]` directly: the `A`-bilinear map
`(a, b) ↦ da ∧ db` induces an `A`-linear map `B ⊗[A] B → ⋀[B]^2 Ω[B⁄A]`, which
vanishes on `I²` and therefore descends to `I / I²`. We then check Riou's
formula `d(b₀ db₁) = db₀ ∧ db₁` and the identity `d ∘ d = 0` on `B`.

## Main definitions

* `wedge x y`: the element `x ∧ y` of `⋀[B]^2 Ω[B⁄A]`.
* `differentialPairing`, `tensorDifferentialPairing`: the `A`-bilinear map
  `(a, b) ↦ da ∧ db` and the induced `A`-linear map on `B ⊗[A] B`.
* `cotangentDifferential`: the induced map `Ω[B⁄A] = I / I² → ⋀[B]^2 Ω[B⁄A]`.
* `degreeOneDifferential`: the same map on `⋀[B]^1 Ω[B⁄A]`.

## Main results

* `tensorDifferentialPairing_sq_mem`: `tensorDifferentialPairing` vanishes on
  `I²`.
* `cotangentDifferential_apply`: `d(b₀ db₁) = db₀ ∧ db₁`.
* `degreeOneDifferential_sourceGenerator`: Riou's generator formula in degree one.
* `degreeOneDifferential_comp_degreeZeroMap`: the composite
  `B → ⋀[B]^1 Ω[B⁄A] → ⋀[B]^2 Ω[B⁄A]` vanishes.

## References

* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
-/

open scoped CategoryTheory TensorProduct

universe u

noncomputable section

namespace AffineCrystalline.DeRham.RiouDegreeOne

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The module of Kähler differentials `Ω[B⁄A]`. -/
abbrev Ω := Ω[B⁄A]
/-- The second exterior power `⋀[B]^2 Ω[B⁄A]`. -/
abbrev Λ2 := ⋀[B]^2 Ω[B⁄A]

/-- The binary exterior product, viewed in the second exterior power. -/
def wedge (x y : Ω (A := A) (B := B)) : Λ2 (A := A) (B := B) :=
  exteriorPower.ιMulti B 2 ![x, y]

omit [CommRing B] in
private theorem update_vecCons_two_zero {M : Type*} (x y v : M) :
    Function.update ![x, y] 0 v = ![v, y] := by
  funext i
  fin_cases i <;> rfl

omit [CommRing B] in
private theorem update_vecCons_two_one {M : Type*} (x y v : M) :
    Function.update ![x, y] 1 v = ![x, v] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem wedge_add_left (x y z : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) (x + y) z =
      wedge (A := A) (B := B) x z + wedge (A := A) (B := B) y z := by
  simpa only [wedge, update_vecCons_two_zero] using
    (exteriorPower.ιMulti B 2).map_update_add ![x, z] 0 x y

@[simp]
theorem wedge_add_right (x y z : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) x (y + z) =
      wedge (A := A) (B := B) x y + wedge (A := A) (B := B) x z := by
  simpa only [wedge, update_vecCons_two_one] using
    (exteriorPower.ιMulti B 2).map_update_add ![x, y] 1 y z

@[simp]
theorem wedge_smul_left (c : A) (x y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) (c • x) y =
      c • wedge (A := A) (B := B) x y := by
  simpa only [wedge, update_vecCons_two_zero, algebraMap_smul] using
    (exteriorPower.ιMulti B 2).map_update_smul ![x, y] 0 (algebraMap A B c) x

@[simp]
theorem wedge_smul_right (c : A) (x y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) x (c • y) =
      c • wedge (A := A) (B := B) x y := by
  simpa only [wedge, update_vecCons_two_one, algebraMap_smul] using
    (exteriorPower.ιMulti B 2).map_update_smul ![x, y] 1 (algebraMap A B c) y

@[simp]
theorem wedge_smul_left' (c : B) (x y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) (c • x) y =
      c • wedge (A := A) (B := B) x y := by
  simpa only [wedge, update_vecCons_two_zero] using
    (exteriorPower.ιMulti B 2).map_update_smul ![x, y] 0 c x

@[simp]
theorem wedge_smul_right' (c : B) (x y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) x (c • y) =
      c • wedge (A := A) (B := B) x y := by
  simpa only [wedge, update_vecCons_two_one] using
    (exteriorPower.ιMulti B 2).map_update_smul ![x, y] 1 c y

@[simp]
theorem wedge_zero_left (y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) 0 y = 0 := by
  simpa using wedge_smul_left' (A := A) (B := B) (0 : B) y y

@[simp]
theorem wedge_zero_right (x : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) x 0 = 0 := by
  simpa using wedge_smul_right' (A := A) (B := B) (0 : B) x x

@[simp]
theorem wedge_self (x : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) x x = 0 := by
  simpa [wedge] using
    (exteriorPower.ιMulti B 2).map_eq_zero_of_eq ![x, x]
      (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by rfl) (by decide)

theorem wedge_add_swap (x y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) x y + wedge (A := A) (B := B) y x = 0 := by
  have hswap : (![(x : Ω (A := A) (B := B)), y] : Fin 2 → Ω (A := A) (B := B)) ∘
      Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  change exteriorPower.ιMulti B 2 ![x, y] +
    exteriorPower.ιMulti B 2 ![y, x] = 0
  rw [← hswap]
  exact (exteriorPower.ιMulti B 2).map_add_swap ![x, y]
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)

theorem wedge_swap (x y : Ω (A := A) (B := B)) :
    wedge (A := A) (B := B) y x = -wedge (A := A) (B := B) x y := by
  have hswap : (![(x : Ω (A := A) (B := B)), y] : Fin 2 → Ω (A := A) (B := B)) ∘
      Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  change exteriorPower.ιMulti B 2 ![y, x] =
    -exteriorPower.ιMulti B 2 ![x, y]
  rw [← hswap]
  exact (exteriorPower.ιMulti B 2).map_swap ![x, y]
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)

/-! ## The pairing `(a, b) ↦ da ∧ db` -/

/-- The `A`-bilinear pairing `(a, b) ↦ da ∧ db`. -/
noncomputable def differentialPairing :
    B →ₗ[A] B →ₗ[A] Λ2 (A := A) (B := B) :=
  LinearMap.mk₂ A
    (fun a b ↦ wedge (A := A) (B := B)
      (KaehlerDifferential.D A B a) (KaehlerDifferential.D A B b))
    (by
      intro a a' b
      rw [map_add, wedge_add_left])
    (by
      intro c a b
      change wedge (KaehlerDifferential.D A B (c • a))
          (KaehlerDifferential.D A B b) = _
      have hD : KaehlerDifferential.D A B (c • a) =
          c • KaehlerDifferential.D A B a := by
        change (KaehlerDifferential.D A B).toLinearMap (c • a) = _
        exact (KaehlerDifferential.D A B).toLinearMap.map_smul c a
      rw [hD, wedge_smul_left])
    (by
      intro a b b'
      rw [map_add, wedge_add_right])
    (by
      intro c a b
      change wedge (KaehlerDifferential.D A B a)
          (KaehlerDifferential.D A B (c • b)) = _
      have hD : KaehlerDifferential.D A B (c • b) =
          c • KaehlerDifferential.D A B b := by
        change (KaehlerDifferential.D A B).toLinearMap (c • b) = _
        exact (KaehlerDifferential.D A B).toLinearMap.map_smul c b
      rw [hD, wedge_smul_right])

@[simp]
theorem differentialPairing_apply (a b : B) :
    differentialPairing (A := A) (B := B) a b =
      wedge (A := A) (B := B)
        (KaehlerDifferential.D A B a) (KaehlerDifferential.D A B b) := rfl

/-- The tensor product `B ⊗[A] B`. -/
abbrev Tensor := B ⊗[A] B

/-- The `A`-linear map on `B ⊗[A] B` sending `a ⊗ b` to `da ∧ db`. -/
noncomputable def tensorDifferentialPairing :
    Tensor (A := A) (B := B) →ₗ[A] Λ2 (A := A) (B := B) :=
  TensorProduct.lift (differentialPairing (A := A) (B := B))

@[simp]
theorem tensorDifferentialPairing_tmul (a b : B) :
    tensorDifferentialPairing (A := A) (B := B) (a ⊗ₜ[A] b) =
      wedge (A := A) (B := B)
        (KaehlerDifferential.D A B a) (KaehlerDifferential.D A B b) := by
  rfl

/-! ## The square of the diagonal ideal -/

/-- The kernel `I` of the multiplication map `B ⊗[A] B → B`. -/
abbrev diagonalIdeal : Ideal (Tensor (A := A) (B := B)) :=
  KaehlerDifferential.ideal A B

/-- The element `1 ⊗ b - b ⊗ 1` of `I`, whose class in `I / I²` is `db`. -/
def diagonal (b : B) : Tensor (A := A) (B := B) :=
  (1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)

@[simp]
theorem diagonal_mem (b : B) :
    diagonal (A := A) (B := B) b ∈ diagonalIdeal (A := A) (B := B) :=
  KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b

/-- `tensorDifferentialPairing` vanishes on `q (1 ⊗ b - b ⊗ 1) (1 ⊗ c - c ⊗ 1)`. -/
theorem tensorDifferentialPairing_mul_diagonal_mul_diagonal
    (q : Tensor (A := A) (B := B)) (b c : B) :
    tensorDifferentialPairing (A := A) (B := B)
        (q * diagonal (A := A) (B := B) b * diagonal (A := A) (B := B) c) = 0 := by
  refine TensorProduct.induction_on q ?_ ?_ ?_
  · simp
  · intro a d
    simp only [diagonal, sub_mul, mul_sub,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      tensorDifferentialPairing_tmul, map_sub]
    simp only [Derivation.leibniz, wedge_add_left, wedge_add_right,
      wedge_smul_left', wedge_smul_right', smul_add, sub_eq_add_neg]
    rw [wedge_swap (A := A) (B := B)
      (KaehlerDifferential.D A B b) (KaehlerDifferential.D A B c)]
    module
  · intro q₁ q₂ h₁ h₂
    rw [add_mul, add_mul, map_add, h₁, h₂, add_zero]

/-- `tensorDifferentialPairing` vanishes on `q * u * v` for `u, v ∈ I`. -/
theorem tensorDifferentialPairing_mul_mul_mem
    {u : Tensor (A := A) (B := B)} (hu : u ∈ diagonalIdeal (A := A) (B := B))
    {v : Tensor (A := A) (B := B)} (hv : v ∈ diagonalIdeal (A := A) (B := B))
    (q : Tensor (A := A) (B := B)) :
    tensorDifferentialPairing (A := A) (B := B) (q * u * v) = 0 := by
  change u ∈ KaehlerDifferential.ideal A B at hu
  change v ∈ KaehlerDifferential.ideal A B at hv
  rw [← KaehlerDifferential.span_range_eq_ideal A B] at hu hv
  revert q
  refine Submodule.span_induction₂ (R := Tensor (A := A) (B := B))
    (M := Tensor (A := A) (B := B))
    (N := Tensor (A := A) (B := B))
    (p := fun x y _ _ ↦ ∀ q : Tensor (A := A) (B := B),
      tensorDifferentialPairing (A := A) (B := B) (q * x * y) = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · rintro x y ⟨b, rfl⟩ ⟨c, rfl⟩ q
    exact tensorDifferentialPairing_mul_diagonal_mul_diagonal (A := A) (B := B) q b c
  · intro y hy q
    simp
  · intro x hx q
    simp
  · intro x y z hx hy hz h₁ h₂ q
    rw [mul_add, add_mul, map_add, h₁ q, h₂ q, add_zero]
  · intro x y z hx hy hz h₁ h₂ q
    rw [mul_add, map_add, h₁ q, h₂ q, add_zero]
  · intro r x y hx hy h₁ q
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h₁ (q * r)
  · intro r x y hx hy h₁ q
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h₁ (q * r)

/-- `tensorDifferentialPairing` vanishes on products of two elements of `I`. -/
theorem tensorDifferentialPairing_mul_mem
    (u : Tensor (A := A) (B := B))
    (hu : u ∈ diagonalIdeal (A := A) (B := B))
    (v : Tensor (A := A) (B := B))
    (hv : v ∈ diagonalIdeal (A := A) (B := B)) :
    tensorDifferentialPairing (A := A) (B := B) (u * v) = 0 := by
  simpa only [one_mul] using tensorDifferentialPairing_mul_mul_mem (A := A) (B := B) hu hv 1

/-- `tensorDifferentialPairing` vanishes on `I²`. -/
theorem tensorDifferentialPairing_sq_mem
    {x : Tensor (A := A) (B := B)}
    (hx : x ∈ diagonalIdeal (A := A) (B := B) ^ 2) :
    tensorDifferentialPairing (A := A) (B := B) x = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro u hu v hv
    exact tensorDifferentialPairing_mul_mem (A := A) (B := B) u hu v hv
  · intro u v hu hv
    rw [map_add, hu, hv, add_zero]

/-! ## Descent to `I / I²` -/

/-- The restriction of `tensorDifferentialPairing` to `I`. -/
noncomputable def idealDifferential :
    diagonalIdeal (A := A) (B := B) →ₗ[A] Λ2 (A := A) (B := B) :=
  (tensorDifferentialPairing (A := A) (B := B)).comp
    ((diagonalIdeal (A := A) (B := B)).subtype.restrictScalars A)

/-- The submodule `I • I` of `I`, so that `I / (I • I)` is the cotangent module
`Ω[B⁄A]`. -/
abbrev cotangentRel :
    Submodule (Tensor (A := A) (B := B)) (diagonalIdeal (A := A) (B := B)) :=
  diagonalIdeal (A := A) (B := B) •
    (⊤ : Submodule (Tensor (A := A) (B := B))
      (diagonalIdeal (A := A) (B := B)))

/-- `idealDifferential` vanishes on `I • I`. -/
theorem idealDifferential_relation
    (x : diagonalIdeal (A := A) (B := B))
    (hx : x ∈ diagonalIdeal (A := A) (B := B) •
      (⊤ : Submodule (Tensor (A := A) (B := B))
        (diagonalIdeal (A := A) (B := B)))) :
    idealDifferential (A := A) (B := B) x = 0 := by
  change tensorDifferentialPairing (A := A) (B := B) (x : Tensor (A := A) (B := B)) = 0
  apply tensorDifferentialPairing_sq_mem (A := A) (B := B)
  exact (diagonalIdeal (A := A) (B := B)).toCotangent_eq_zero x |>.mp
    ((Submodule.Quotient.mk_eq_zero _).2 hx)

/-- The differential `d : Ω[B⁄A] → ⋀[B]^2 Ω[B⁄A]`, induced by
`idealDifferential` on `Ω[B⁄A] = I / I²`. -/
noncomputable def cotangentDifferential :
    Ω (A := A) (B := B) →ₗ[A] Λ2 (A := A) (B := B) := by
  refine LinearMap.comp
    ((((cotangentRel (A := A) (B := B)).restrictScalars A).liftQ
      (idealDifferential (A := A) (B := B)) ?_))
    (Submodule.Quotient.restrictScalarsEquiv A
      (cotangentRel (A := A) (B := B))).symm.toLinearMap
  intro x hx
  rw [LinearMap.mem_ker]
  exact idealDifferential_relation (A := A) (B := B) x
    ((Submodule.restrictScalars_mem _ _ _).mp hx)

@[simp]
theorem cotangentDifferential_toCotangent
    (x : diagonalIdeal (A := A) (B := B)) :
    cotangentDifferential (A := A) (B := B)
        ((diagonalIdeal (A := A) (B := B)).toCotangent x) =
      idealDifferential (A := A) (B := B) x := by
  rfl

/-- `tensorDifferentialPairing` sends `b₀ • (1 ⊗ b₁ - b₁ ⊗ 1)` to `db₀ ∧ db₁`. -/
theorem tensorDifferentialPairing_algebraMap_smul_diagonal (b₀ b₁ : B) :
    tensorDifferentialPairing (A := A) (B := B)
        ((algebraMap B (Tensor (A := A) (B := B)) b₀) •
          diagonal (A := A) (B := B) b₁) =
      wedge (A := A) (B := B)
        (KaehlerDifferential.D A B b₀) (KaehlerDifferential.D A B b₁) := by
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  simp only [diagonal, mul_sub, map_sub]
  simp [Derivation.leibniz]

/-- Riou's formula in degree one: `d(b₀ db₁) = db₀ ∧ db₁`. -/
theorem cotangentDifferential_apply (b₀ b₁ : B) :
    cotangentDifferential (A := A) (B := B)
        (b₀ • KaehlerDifferential.D A B b₁) =
      wedge (A := A) (B := B)
        (KaehlerDifferential.D A B b₀) (KaehlerDifferential.D A B b₁) := by
  rw [KaehlerDifferential.D_apply]
  change cotangentDifferential (A := A) (B := B)
      (b₀ • (diagonalIdeal (A := A) (B := B)).toCotangent _) = _
  rw [← LinearMap.map_smul_of_tower (diagonalIdeal (A := A) (B := B)).toCotangent]
  rw [cotangentDifferential_toCotangent]
  rw [← KaehlerDifferential.D_apply A B b₁]
  simpa [idealDifferential, KaehlerDifferential.D_apply, Algebra.smul_def,
    Algebra.TensorProduct.algebraMap_apply, diagonal] using
    tensorDifferentialPairing_algebraMap_smul_diagonal (A := A) (B := B) b₀ b₁

/-- The degree-one differential `⋀[B]^1 Ω[B⁄A] → ⋀[B]^2 Ω[B⁄A]`. -/
noncomputable def degreeOneDifferential :
    ⋀[B]^1 Ω[B⁄A] →ₗ[A] Λ2 (A := A) (B := B) :=
  (cotangentDifferential (A := A) (B := B)).comp
    (AffineCrystalline.DeRham.oneFormsEquiv (A := A) (B := B)
      Ω[B⁄A]).toLinearMap

/-- The degree-one differential satisfies Riou's generator formula. -/
theorem degreeOneDifferential_sourceGenerator (b₀ b₁ : B) :
    degreeOneDifferential (A := A) (B := B)
        (AffineCrystalline.DeRham.RiouPresentation.sourceGenerator
          (A := A) (B := B) 1 b₀ (fun _ : Fin 1 ↦ b₁)) =
      AffineCrystalline.DeRham.RiouPresentation.targetGenerator
        (A := A) (B := B) 1 b₀ (fun _ : Fin 1 ↦ b₁) := by
  change cotangentDifferential (A := A) (B := B)
      ((exteriorPower.oneEquiv B Ω[B⁄A])
        (b₀ • exteriorPower.ιMulti B 1
          (KaehlerDifferential.D A B ∘ fun _ : Fin 1 ↦ b₁))) = _
  rw [(exteriorPower.oneEquiv B Ω[B⁄A]).map_smul,
    exteriorPower.oneEquiv_ιMulti]
  exact cotangentDifferential_apply (A := A) (B := B) b₀ b₁

/-! ## The identity `d ∘ d = 0` in degree zero -/

/-- The degree-one differential vanishes on the image of the degree-zero
differential. -/
theorem degreeOneDifferential_comp_degreeZeroMap :
    degreeOneDifferential (A := A) (B := B) ∘ₗ
        (degreeZeroMap (A := A) (B := B)).hom = 0 := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (degreeZeroMap_spec (A := A) (B := B)) x
  change (oneFormsEquiv (A := A) (B := B) Ω[B⁄A]) ((degreeZeroMap (A := A) (B := B)).hom x) =
    KaehlerDifferential.D A B (zeroFormsEquiv (A := A) (B := B) Ω[B⁄A] x) at h
  change cotangentDifferential (A := A) (B := B)
      ((oneFormsEquiv (A := A) (B := B) Ω[B⁄A]) ((degreeZeroMap (A := A) (B := B)).hom x)) = 0
  rw [h, ← one_smul B (KaehlerDifferential.D A B _), cotangentDifferential_apply,
    Derivation.map_one_eq_zero, wedge_zero_left]

end AffineCrystalline.DeRham.RiouDegreeOne
