/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPoly.CodingTheory.GuruswamiSudan.Generic
import CompPoly.Fields.KoalaBear

/-!
# Executable Guruswami-Sudan Decoder (Fast KoalaBear)

Native-word `KoalaBear.Fast.Field` instantiation of the generic executable
Guruswami-Sudan decoder.
-/

namespace CompPoly
namespace CodingTheory
namespace GuruswamiSudanFast

abbrev F := KoalaBear.Fast.Field
abbrev UniPoly := CompPoly.CodingTheory.GuruswamiSudan.Generic.UniPoly F
abbrev Bivariate := CompPoly.CodingTheory.GuruswamiSudan.Generic.Bivariate F
abbrev ReedSolomonCode := CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode F
abbrev DecodeResult := CompPoly.CodingTheory.GuruswamiSudan.Generic.DecodeResult F

instance : Inhabited F := ⟨0⟩

def maxCandidatesPerDepth : Nat := CompPoly.CodingTheory.GuruswamiSudan.Generic.maxCandidatesPerDepth
def maxTotalRoots : Nat := CompPoly.CodingTheory.GuruswamiSudan.Generic.maxTotalRoots

namespace NatUtil

export CompPoly.CodingTheory.GuruswamiSudan.Generic.NatUtil (floorSqrt ceilSqrt ceilSqrtDiv binomial)

end NatUtil

namespace UniPoly

export CompPoly.CodingTheory.GuruswamiSudan.Generic.UniPoly
  (zero one isZero trim coeff degree leadingCoeff ofNatArray neg add sub scale mul
    mulXPow evaluate pow monomial longDivRem? coeffsEq)

end UniPoly

namespace Bivariate

export CompPoly.CodingTheory.GuruswamiSudan.Generic.Bivariate
  (zero trimCoeffs ofCoeffs isZero yDegree maxXDegree coeff evaluate weightedDegree
    evaluateYPolynomial fromMonomials)

end Bivariate

namespace ReedSolomonCode

def withDomain (domain : Array F) (k : Nat) : ReedSolomonCode :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.withDomain domain k

def consecutiveDomain (n : Nat) : Array F :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.consecutiveDomain (F := F) n

def withConsecutiveDomain (n k : Nat) : ReedSolomonCode :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.withConsecutiveDomain (F := F) n k

def pow2Domain (logN : Nat) : Array F :=
  let omega := KoalaBear.Fast.ofField
    (KoalaBear.twoAdicGenerators.toArray.getD logN (1 : KoalaBear.Field))
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.pow2Domain (F := F) logN omega

def withRootsOfUnityDomain (logN k : Nat) : ReedSolomonCode :=
  let omega := KoalaBear.Fast.ofField
    (KoalaBear.twoAdicGenerators.toArray.getD logN (1 : KoalaBear.Field))
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.withRootsOfUnityDomain (F := F) logN k omega

def encodePolynomial (code : ReedSolomonCode) (poly : UniPoly) : Array F :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.encodePolynomial code poly

def encode (code : ReedSolomonCode) (message : Array F) : Array F :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.ReedSolomonCode.encode code message

end ReedSolomonCode

export CompPoly.CodingTheory.GuruswamiSudan.Generic
  (gsDecodingRadius johnsonListBound? countMonomials chooseParameters
    monomialsBelowWeightedDegree findKernelVector interpolateWithMultiplicity
    extractSmallValue? lagrangeInterpolateAtZeroWithPoints?
    lagrangeInterpolatePolynomial? substituteAndDivide findRootsLinearY
    appendUniquePoly appendUniqueField enumerateSmallPolys
    trySmallIntegerPolynomials tryDirectRoots tryInterpolatedCandidates
    findUnivariateRootsWithHints findUnivariateRootsWithHintsAndDomain
    rrSearchWithDomain findPolynomialRootsWithDomain agreement
    gsListDecodeWithMultiplicity gsListDecode introduceErrors
    introduceErrorsAtPositions)

def polyToNats (p : UniPoly) : Array Nat :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.polyToNats (F := F) KoalaBear.Fast.toNat p

def valuesToNats (xs : Array F) : Array Nat :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.valuesToNats (F := F) KoalaBear.Fast.toNat xs

def candidatesToNats (xs : Array UniPoly) : Array (Array Nat) :=
  CompPoly.CodingTheory.GuruswamiSudan.Generic.candidatesToNats (F := F) KoalaBear.Fast.toNat xs

end GuruswamiSudanFast
end CodingTheory
end CompPoly
