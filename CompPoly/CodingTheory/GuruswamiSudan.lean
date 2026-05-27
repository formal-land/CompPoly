/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPoly.CodingTheory.GuruswamiSudan.Generic
import CompPoly.Fields.KoalaBear

/-!
# Executable Guruswami-Sudan Decoder

Canonical `KoalaBear.Field` instantiation of the generic executable
Guruswami-Sudan decoder.
-/

namespace CompPoly
namespace CodingTheory
namespace GuruswamiSudan

abbrev F := KoalaBear.Field
abbrev UniPoly := Generic.UniPoly F
abbrev Bivariate := Generic.Bivariate F
abbrev ReedSolomonCode := Generic.ReedSolomonCode F
abbrev DecodeResult := Generic.DecodeResult F

def maxCandidatesPerDepth : Nat := Generic.maxCandidatesPerDepth
def maxTotalRoots : Nat := Generic.maxTotalRoots

namespace NatUtil

export Generic.NatUtil (floorSqrt ceilSqrt ceilSqrtDiv binomial)

end NatUtil

namespace UniPoly

export Generic.UniPoly
  (zero one isZero trim coeff degree leadingCoeff ofNatArray neg add sub scale mul
    mulXPow evaluate pow monomial longDivRem? coeffsEq)

end UniPoly

namespace Bivariate

export Generic.Bivariate
  (zero trimCoeffs ofCoeffs isZero yDegree maxXDegree coeff evaluate weightedDegree
    evaluateYPolynomial fromMonomials)

end Bivariate

namespace ReedSolomonCode

def withDomain (domain : Array F) (k : Nat) : ReedSolomonCode :=
  Generic.ReedSolomonCode.withDomain domain k

def consecutiveDomain (n : Nat) : Array F :=
  Generic.ReedSolomonCode.consecutiveDomain (F := F) n

def withConsecutiveDomain (n k : Nat) : ReedSolomonCode :=
  Generic.ReedSolomonCode.withConsecutiveDomain (F := F) n k

def pow2Domain (logN : Nat) : Array F :=
  let omega := KoalaBear.twoAdicGenerators.toArray.getD logN (1 : F)
  Generic.ReedSolomonCode.pow2Domain (F := F) logN omega

def withRootsOfUnityDomain (logN k : Nat) : ReedSolomonCode :=
  let omega := KoalaBear.twoAdicGenerators.toArray.getD logN (1 : F)
  Generic.ReedSolomonCode.withRootsOfUnityDomain (F := F) logN k omega

def encodePolynomial (code : ReedSolomonCode) (poly : UniPoly) : Array F :=
  Generic.ReedSolomonCode.encodePolynomial code poly

def encode (code : ReedSolomonCode) (message : Array F) : Array F :=
  Generic.ReedSolomonCode.encode code message

end ReedSolomonCode

export Generic
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
  Generic.polyToNats (F := F) ZMod.val p

def valuesToNats (xs : Array F) : Array Nat :=
  Generic.valuesToNats (F := F) ZMod.val xs

def candidatesToNats (xs : Array UniPoly) : Array (Array Nat) :=
  Generic.candidatesToNats (F := F) ZMod.val xs

end GuruswamiSudan
end CodingTheory
end CompPoly
