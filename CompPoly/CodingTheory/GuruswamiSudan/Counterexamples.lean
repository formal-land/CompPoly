/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPoly.CodingTheory.GuruswamiSudan.Correctness
import CompPoly.Fields.KoalaBear

/-!
# Counterexamples for the Heuristic Guruswami-Sudan Root Finder

This file machine-checks a small obstruction to proving full completeness for
the current Lambdaworks-matching root finder: the root finder is heuristic, so it
does not enumerate every polynomial root of a bivariate polynomial.
-/

namespace CompPoly
namespace CodingTheory
namespace GuruswamiSudan
namespace Generic
namespace Counterexamples

abbrev F := KoalaBear.Field

def heuristicRootCounterexampleQ : Bivariate F :=
  Bivariate.fromMonomials
    #[(0, 0), (0, 1), (0, 2)]
    #[(5000 : F) * (5001 : F), -((5000 : F) + (5001 : F)), (1 : F)]

def heuristicRootCounterexampleF : UniPoly F := #[(5000 : F)]

theorem heuristicRootCounterexample_is_root :
    UniPoly.isZero
      (Bivariate.evaluateYPolynomial
        heuristicRootCounterexampleQ heuristicRootCounterexampleF) := by
  native_decide

theorem heuristicRootCounterexample_not_returned :
    heuristicRootCounterexampleF ∉
      findPolynomialRootsWithDomain heuristicRootCounterexampleQ 1 #[] #[] := by
  native_decide

theorem heuristicRootFinder_incomplete :
    ¬ RootFinderCompleteFor heuristicRootCounterexampleQ 1 #[] #[] := by
  intro hcomplete
  exact heuristicRootCounterexample_not_returned
    (hcomplete heuristicRootCounterexampleF (by native_decide)
      heuristicRootCounterexample_is_root)

end Counterexamples
end Generic
end GuruswamiSudan
end CodingTheory
end CompPoly
