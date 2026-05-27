/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPoly.CodingTheory.GuruswamiSudan.Generic
import CompPoly.Univariate.ToPoly.Core

/-!
# Executable Correctness Milestones for Guruswami-Sudan

This file records proof targets that are true for the current executable
Guruswami-Sudan implementation. The root finder in `Generic.lean` intentionally
matches the Lambdaworks heuristic, so full completeness is stated conditionally
on that root finder returning every polynomial root of the interpolation
polynomial.
-/

namespace CompPoly
namespace CodingTheory
namespace GuruswamiSudan
namespace Generic

variable {F : Type} [Field F]

namespace UniPoly

/-- Mathlib polynomial denoted by the executable GS coefficient array. -/
noncomputable def toPolynomial (p : UniPoly F) : Polynomial F :=
  CPolynomial.Raw.toPoly (p : CPolynomial.Raw F)

/-- The executable Horner evaluator agrees with Mathlib polynomial evaluation. -/
theorem evaluate_eq_toPolynomial_eval (p : UniPoly F) (x : F) :
    UniPoly.evaluate p x = (toPolynomial p).eval x := by
  calc
    UniPoly.evaluate p x =
        CPolynomial.Raw.eval₂Horner (RingHom.id F) x (p : CPolynomial.Raw F) := rfl
    _ = CPolynomial.Raw.eval x (p : CPolynomial.Raw F) :=
        CPolynomial.Raw.eval₂Horner_eq_eval₂ (RingHom.id F) x (p : CPolynomial.Raw F)
    _ = (toPolynomial p).eval x :=
        (CPolynomial.Raw.eval_toPoly_eq_eval x (p : CPolynomial.Raw F)).symm

end UniPoly

variable [BEq F] [Inhabited F]

/-- A returned candidate satisfies the executable Reed-Solomon list-decoding
acceptance predicate: degree below `k` and enough agreement with the received
word. -/
def IsAcceptedCandidate
    (code : ReedSolomonCode F) (received : Array F) (f : UniPoly F) : Prop :=
  UniPoly.degree f < code.k ∧
    agreement received code.domain f ≥ code.n - gsDecodingRadius code.n code.k

/-- Dot product used to state the executable interpolation linear system. -/
def dotProduct (row vector : Array F) : F := Id.run do
  let mut acc : F := 0
  for i in [0:min row.size vector.size] do
    acc := acc + row[i]! * vector[i]!
  pure acc

/-- A vector is in the right kernel of every row of an executable matrix. -/
def VectorInKernel (matrix : Array (Array F)) (vector : Array F) : Prop :=
  ∀ row ∈ matrix, dotProduct row vector = 0

/-- The executable interpolation system attached to the multiplicity step. This
predicate intentionally talks about the concrete matrix built by
`interpolationMatrix`; connecting those rows to Hasse derivatives is the next
mathematical layer above this executable milestone. -/
def SatisfiesInterpolationSystem
    (domain received : Array F) (m d k : Nat) (q : Bivariate F) : Prop :=
  let monomials := monomialsBelowWeightedDegree d k
  let matrix := interpolationMatrix domain received m d k
  let solution := findKernelVector matrix monomials.size
  q = Bivariate.fromMonomials monomials solution ∧ VectorInKernel matrix solution

/-- The precise linear-algebra fact needed from `findKernelVector` for
interpolation correctness. -/
def InterpolationKernelCorrect
    (domain received : Array F) (m d k : Nat) : Prop :=
  let monomials := monomialsBelowWeightedDegree d k
  let matrix := interpolationMatrix domain received m d k
  VectorInKernel matrix (findKernelVector matrix monomials.size)

/-- Soundness of the executable decoder's final filter. This theorem does not
claim that the heuristic root finder found every possible root; it says every
candidate that survives the decoder is genuinely accepted by the executable
agreement predicate. -/
theorem gsListDecode_sound
    (code : ReedSolomonCode F) (received : Array F) (f : UniPoly F)
    (hsize : received.size = code.n)
    (hmem : f ∈ (gsListDecode code received).candidates) :
    IsAcceptedCandidate code received f := by
  simp only [gsListDecode] at hmem
  have hneq : (received.size != code.n) = false := by simp [hsize]
  simp [hneq] at hmem
  exact ⟨hmem.2.1, (Nat.sub_le_iff_le_add).2 hmem.2.2⟩

/-- Interpolation correctness reduced to the executable linear-algebra kernel
claim. This theorem has no proof placeholder and states exactly the remaining
obligation: the row-reduction routine must return a vector annihilating the
interpolation matrix. -/
theorem interpolateWithMultiplicity_correct_of_kernel
    (domain received : Array F) (m d k : Nat)
    (hkernel : InterpolationKernelCorrect domain received m d k) :
    SatisfiesInterpolationSystem domain received m d k
      (interpolateWithMultiplicity domain received m d k) := by
  simpa [SatisfiesInterpolationSystem, InterpolationKernelCorrect,
    interpolateWithMultiplicity] using hkernel

/-- Completeness assumption for the current heuristic root finder at one
particular interpolation polynomial. This is false in general, but useful as the
explicit hypothesis under which the rest of GS completeness can be stated. -/
def RootFinderCompleteFor
    (q : Bivariate F) (maxDegree : Nat) (hintValues domain : Array F) : Prop :=
  ∀ f : UniPoly F,
    UniPoly.degree f < maxDegree →
    UniPoly.isZero (Bivariate.evaluateYPolynomial q f) →
    f ∈ findPolynomialRootsWithDomain q maxDegree hintValues domain

/-- Soundness assumption for one concrete call to the heuristic root finder:
every returned candidate is really a `Y`-root of the bivariate polynomial and
has the requested degree bound. -/
def RootFinderSoundFor
    (q : Bivariate F) (maxDegree : Nat) (hintValues domain : Array F) : Prop :=
  ∀ f : UniPoly F,
    f ∈ findPolynomialRootsWithDomain q maxDegree hintValues domain →
    UniPoly.degree f < maxDegree ∧
      UniPoly.isZero (Bivariate.evaluateYPolynomial q f)

/-- Exact per-case adequacy of the heuristic root finder. This is the assumption
that makes the executable decoder exact for the particular interpolation
polynomial used in this decoding run. -/
def RootFinderAdequateFor
    (q : Bivariate F) (maxDegree : Nat) (hintValues domain : Array F) : Prop :=
  RootFinderSoundFor q maxDegree hintValues domain ∧
    RootFinderCompleteFor q maxDegree hintValues domain

/-- Conditional completeness of the executable decoder after the algebraic GS
step has established that the message polynomial is a root of the interpolated
`Q`, and assuming the heuristic root finder is complete for that `Q`. -/
theorem gsListDecode_complete_of_rootFinderComplete
    (code : ReedSolomonCode F) (received : Array F) (f : UniPoly F)
    (hsize : received.size = code.n)
    (m d : Nat)
    (hparams : chooseParameters code.n code.k = (m, d))
    (hrootComplete :
      let q := interpolateWithMultiplicity code.domain received m d code.k
      RootFinderCompleteFor q code.k received code.domain)
    (hroot :
      let q := interpolateWithMultiplicity code.domain received m d code.k
      UniPoly.isZero (Bivariate.evaluateYPolynomial q f))
    (hdeg : UniPoly.degree f < code.k)
    (hagree :
      agreement received code.domain f ≥
        code.n - gsDecodingRadius code.n code.k) :
    f ∈ (gsListDecode code received).candidates := by
  simp only [gsListDecode]
  have hneq : (received.size != code.n) = false := by simp [hsize]
  simp [hneq, hparams]
  refine ⟨?_, hdeg, ?_⟩
  · exact hrootComplete f hdeg hroot
  · exact (Nat.sub_le_iff_le_add).1 hagree

/-- Under exact per-case root-finder adequacy, the executable decoder returns
exactly the low-degree roots of the interpolated polynomial that also pass the
agreement threshold. This is the strongest correctness statement available for
the current decoder without replacing the heuristic root finder or proving the
separate algebraic GS theorem that an actually-close message is a root of `Q`. -/
theorem gsListDecode_exact_of_rootFinderAdequate
    (code : ReedSolomonCode F) (received : Array F) (f : UniPoly F)
    (hsize : received.size = code.n)
    (m d : Nat)
    (hparams : chooseParameters code.n code.k = (m, d))
    (hrootAdequate :
      let q := interpolateWithMultiplicity code.domain received m d code.k
      RootFinderAdequateFor q code.k received code.domain) :
    f ∈ (gsListDecode code received).candidates ↔
      IsAcceptedCandidate code received f ∧
        (let q := interpolateWithMultiplicity code.domain received m d code.k
         UniPoly.isZero (Bivariate.evaluateYPolynomial q f)) := by
  simp only [gsListDecode]
  have hneq : (received.size != code.n) = false := by simp [hsize]
  simp [hneq, hparams, IsAcceptedCandidate]
  constructor
  · intro hmem
    exact ⟨⟨hmem.2.1, hmem.2.2⟩,
      (hrootAdequate.1 f hmem.1).2⟩
  · intro h
    exact ⟨hrootAdequate.2 f h.1.1 h.2, h.1.1,
      h.1.2⟩

end Generic
end GuruswamiSudan
end CodingTheory
end CompPoly
