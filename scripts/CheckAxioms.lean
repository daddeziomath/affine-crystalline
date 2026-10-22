/-
Copyright (c) 2026 Marco D'Addezio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marco D'Addezio
-/
import AffineCrystalline.AffineCrystalline

/-!
# Axiom check for the main theorems

Run with `lake env lean scripts/CheckAxioms.lean`.  Each command must print
only `propext`, `Classical.choice` and `Quot.sound`.
-/

open AffineCrystalline.InfinitesimalSite

#print axioms EnvelopeFamily.crystallineCohomologyIsoDeRham
#print axioms EnvelopeFamily.affineDeRhamComparison
#print axioms EnvelopeFamily.crystallineCohomologyIsoCechAlexander
#print axioms AffineCrystalline.DPEnvelope.hasDPEnvelope
#print axioms crystallineCohomologyIsoDeRham
#print axioms affineDeRhamComparison
#print axioms crystallineCohomologyIsoCechAlexander
