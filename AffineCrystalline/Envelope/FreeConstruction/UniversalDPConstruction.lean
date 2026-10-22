/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/

import AffineCrystalline.Envelope.FreeConstruction.UniversalDP
import AffineCrystalline.Envelope.FreeConstruction.PositiveDPStructure
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Divided powers on `Γ⁺`: free modules and quotients

Following Roby and the approach of Chambert-Loir and de Frutos-Fernández,
divided powers on the positive ideal `Γ⁺` of the divided power algebra `Γ_R(M)`
are constructed in two steps.

1. If `M` is free, Roby's explicit formula `robyDpow`, computed in a basis of
   `Γ_R(M)` by Roby monomials, defines divided powers on `Γ⁺`. Here this step
   takes as input a `RobyBasisData` and a `RobyDpowLawData`.
2. In general, divided powers on `Γ⁺` descend along a quotient `Γ_R(M) ⧸ K`
   provided `K ⊓ Γ⁺` is a sub-divided power ideal.

## Main definitions

* `FreeDpowInput`: the input of step 1.
* `FreeDpowInput.dividedPowers`: the resulting divided powers on `Γ⁺`.
* `freeModuleDpow`, `finiteFreeModuleDpow`: the same, indexed by
  the canonical basis of a free (resp. finite free) module.
* `PresentationDpowInput`: an ideal `K` of `Γ_R(M)` with `K ⊓ Γ⁺` a
  sub-divided power ideal, and `PresentationDpowInput.dividedPowers`: the
  quotient divided powers.
* `FreePresentationDpowInput`: steps 1 and 2 combined.

## Main results

* `FreeDpowInput.dividedPowers_generator_formula`: Roby's formula
  `γ_n([k](m)) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`.
* `PresentationDpowInput.quotient_dpow_generator_formula`,
  `FreePresentationDpowInput.quotient_dpow_generator_formula`: Roby's formula
  in the quotient.

## References

* N. Roby, *Lois polynômes et lois formelles en théorie des modules*,
  Ann. Sci. École Norm. Sup. (3) 80 (1963), 213–348.
* N. Roby, *Les algèbres à puissances divisées*, Bull. Sci. Math. (2) 89 (1965),
  75–91.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *A formalization of divided
  powers in Lean*, ITP 2025, LIPIcs, 4:1–4:17.
* A. Chambert-Loir and M. I. de Frutos-Fernández, *Formalizing polynomial laws
  and the universal divided power algebra*, arXiv:2512.05750.
-/

open DividedPowers

universe u v

noncomputable section

namespace AffineCrystalline
namespace Envelope
namespace FreeConstruction

section FreeModule

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-! ## Free modules -/

/-- The data of a `RobyBasisData` and a `RobyDpowLawData`, from
which Roby's divided powers on `Γ⁺` are defined. -/
structure FreeDpowInput where
  robyBasis : RobyBasisData (R := R) (M := M) (ι := ι)
  laws : RobyDpowLawData robyBasis

namespace FreeDpowInput

variable (C : FreeDpowInput (R := R) (M := M) (ι := ι))

/-- Roby's divided powers on `Γ⁺`. -/
noncomputable def dividedPowers : DividedPowers (positiveIdeal (R := R) (M := M)) :=
  UniversalDPInput.dividedPowers
    { basis := C.robyBasis, laws := C.laws }

/-- Roby's formula `γ_n([k](m)) = (nk)! / (n! (k!)ⁿ) · [nk](m)` for `k > 0`. -/
theorem dividedPowers_generator_formula {n k : ℕ} {m : M} (hk : k ≠ 0) :
    C.dividedPowers.dpow n (DividedPowerAlgebra.dp R k m) =
      generatorDpow (R := R) (M := M) n k m :=
  UniversalDPInput.generator_formula
    { basis := C.robyBasis, laws := C.laws } hk

/-- Given a `FreeDpowInput`, the ideal `Γ⁺` admits divided powers. -/
theorem is_free_positiveDPStructure
    (C : FreeDpowInput (R := R) (M := M) (ι := ι)) :
    Nonempty (DividedPowers (positiveIdeal (R := R) (M := M))) :=
  ⟨dividedPowers C⟩

end FreeDpowInput

/-- Roby's divided powers on `Γ⁺` for a free module `M`, from a
`FreeDpowInput` indexed by the canonical basis of `M`. -/
noncomputable def freeModuleDpow
    [Module.Free R M]
    (C : FreeDpowInput (R := R) (M := M)
      (ι := Module.Free.ChooseBasisIndex R M)) :
    DividedPowers (positiveIdeal (R := R) (M := M)) :=
  C.dividedPowers

/-- The case of a finite free module `M` of `freeModuleDpow`. -/
noncomputable def finiteFreeModuleDpow
    [Module.Free R M]
    [Finite (Module.Free.ChooseBasisIndex R M)]
    (C : FreeDpowInput (R := R) (M := M)
      (ι := Module.Free.ChooseBasisIndex R M)) :
    DividedPowers (positiveIdeal (R := R) (M := M)) :=
  C.dividedPowers

end FreeModule

section Presentation

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

local notation "Γ" => DividedPowerAlgebra R M

/-! ## Quotients -/

/-- An ideal `K` of `Γ_R(M)` such that `K ⊓ Γ⁺` is a sub-divided power ideal of
`Γ⁺`, with its divided powers from a `PositiveDPStructure`. -/
structure PresentationDpowInput
    (P : PositiveDPStructure (R := R) (M := M)) where
  relationIdeal : Ideal Γ
  relation_isSubDPIdeal :
    IsSubDPIdeal P.dividedPowers
      (relationIdeal ⊓ positiveIdeal (R := R) (M := M))

namespace PresentationDpowInput

variable (P : PositiveDPStructure (R := R) (M := M))
variable (Q : PresentationDpowInput (R := R) (M := M) P)

/-- The quotient ring `Γ_R(M) ⧸ K`. -/
abbrev quotient : Type u := Γ ⧸ Q.relationIdeal

/-- The quotient map `Γ_R(M) → Γ_R(M) ⧸ K`. -/
def quotientMap : Γ →+* Q.quotient := Ideal.Quotient.mk Q.relationIdeal

/-- The quotient divided powers on the image of `Γ⁺` in `Γ_R(M) ⧸ K`. -/
noncomputable def dividedPowers :
    DividedPowers
      ((positiveIdeal (R := R) (M := M)).map (Q.quotientMap P)) :=
  DividedPowers.Quotient.dividedPowers P.dividedPowers
    Q.relation_isSubDPIdeal

theorem quotientMap_isDPMorphism :
    IsDPMorphism P.dividedPowers Q.dividedPowers (Q.quotientMap P) :=
  DividedPowers.Quotient.isDPMorphism P.dividedPowers
    Q.relation_isSubDPIdeal

theorem quotient_dpow_generator {n k : ℕ} (hk : k ≠ 0) (m : M) :
    Q.dividedPowers.dpow n
        ((Q.quotientMap P) (DividedPowerAlgebra.dp R k m)) =
      (Q.quotientMap P)
        (P.dividedPowers.dpow n (DividedPowerAlgebra.dp R k m)) :=
  DividedPowers.Quotient.dpow_apply P.dividedPowers
    Q.relation_isSubDPIdeal
    (dp_mem_positiveIdeal (R := R) (M := M) hk m)

theorem quotient_dpow_generator_formula {n k : ℕ} (hk : k ≠ 0) (m : M) :
    Q.dividedPowers.dpow n
        ((Q.quotientMap P) (DividedPowerAlgebra.dp R k m)) =
      (Q.quotientMap P)
        (generatorDpow (R := R) (M := M) n k m) := by
  rw [Q.quotient_dpow_generator P hk m, P.generator_formula hk]

end PresentationDpowInput

end Presentation

section FreePresentation

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type v}

local notation "Γ" => DividedPowerAlgebra R M

/-! ## Free modules and quotients combined -/

/-- A `FreeDpowInput` together with an ideal `K` of `Γ_R(M)` such that
`K ⊓ Γ⁺` is a sub-divided power ideal for the resulting divided powers. -/
structure FreePresentationDpowInput where
  free : FreeDpowInput (R := R) (M := M) (ι := ι)
  relationIdeal : Ideal Γ
  relation_isSubDPIdeal :
    IsSubDPIdeal free.dividedPowers
      (relationIdeal ⊓ positiveIdeal (R := R) (M := M))

namespace FreePresentationDpowInput

variable (C : FreePresentationDpowInput (R := R) (M := M) (ι := ι))

/-- Roby's divided powers on `Γ⁺`, as a `PositiveDPStructure`. -/
noncomputable def sourceDPStructure : PositiveDPStructure (R := R) (M := M) :=
  { dividedPowers := C.free.dividedPowers
    generator_formula := C.free.dividedPowers_generator_formula }

/-- The ideal `K`, as a `PresentationDpowInput`. -/
noncomputable def quotientInput :
    PresentationDpowInput (R := R) (M := M) C.sourceDPStructure :=
  { relationIdeal := C.relationIdeal
    relation_isSubDPIdeal := C.relation_isSubDPIdeal }

/-- The quotient ring `Γ_R(M) ⧸ K`. -/
abbrev quotient : Type u := Γ ⧸ C.relationIdeal

/-- The quotient divided powers on the image of `Γ⁺` in `Γ_R(M) ⧸ K`. -/
noncomputable def dividedPowers :
    DividedPowers
      ((positiveIdeal (R := R) (M := M)).map
        (PresentationDpowInput.quotientMap C.sourceDPStructure C.quotientInput)) :=
  PresentationDpowInput.dividedPowers C.sourceDPStructure C.quotientInput

theorem quotientMap_isDPMorphism :
    IsDPMorphism C.sourceDPStructure.dividedPowers C.dividedPowers
      (PresentationDpowInput.quotientMap C.sourceDPStructure C.quotientInput) :=
  PresentationDpowInput.quotientMap_isDPMorphism
    C.sourceDPStructure C.quotientInput

theorem quotient_dpow_generator_formula {n k : ℕ} (hk : k ≠ 0) (m : M) :
    C.dividedPowers.dpow n
        ((PresentationDpowInput.quotientMap C.sourceDPStructure C.quotientInput)
          (DividedPowerAlgebra.dp R k m)) =
      (PresentationDpowInput.quotientMap C.sourceDPStructure C.quotientInput)
        (generatorDpow (R := R) (M := M) n k m) :=
  PresentationDpowInput.quotient_dpow_generator_formula
    C.sourceDPStructure C.quotientInput hk m

end FreePresentationDpowInput

end FreePresentation

end FreeConstruction
end Envelope
end AffineCrystalline
