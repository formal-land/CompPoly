/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPoly.CodingTheory.GuruswamiSudanFast

/-!
# Fast KoalaBear Guruswami-Sudan Decoder Tests

Executable regression checks for the native-word KoalaBear Guruswami-Sudan port.
-/

namespace CompPoly
namespace CodingTheory
namespace GuruswamiSudanFast

def hasCandidate (result : DecodeResult) (message : Array F) : Bool :=
  result.candidates.any fun candidate => UniPoly.coeffsEq candidate message

#guard countMonomials 10 3 = 22
#guard gsDecodingRadius 8 2 = 3
#guard chooseParameters 8 2 = (2, 9)
#guard gsDecodingRadius 16 4 = 7
#guard chooseParameters 16 4 = (4, 35)

#guard
  valuesToNats (ReedSolomonCode.consecutiveDomain 8) =
    #[0, 1, 2, 3, 4, 5, 6, 7]

#guard
  valuesToNats (ReedSolomonCode.pow2Domain 3) =
    #[1, 1748172362, 2113994754, 391001680, 2130706432, 382534071,
      16711679, 1739704753]

#guard
  let code := ReedSolomonCode.withConsecutiveDomain 8 2
  let message : Array F := #[1, 2]
  let received := ReedSolomonCode.encode code message
  let result := gsListDecode code received
  result.multiplicity = 2 && result.degreeBound = 9 && result.errorBound = 3 &&
    valuesToNats received = #[1, 3, 5, 7, 9, 11, 13, 15] &&
    candidatesToNats result.candidates = #[#[1, 2]] && hasCandidate result message

#guard
  let code := ReedSolomonCode.withConsecutiveDomain 8 2
  let message : Array F := #[1, 2]
  let codeword := ReedSolomonCode.encode code message
  let received := introduceErrorsAtPositions codeword #[1]
  let result := gsListDecode code received
  valuesToNats received = #[1, 4, 5, 7, 9, 11, 13, 15] &&
    candidatesToNats result.candidates = #[#[1, 2]] && hasCandidate result message

#guard
  let code := ReedSolomonCode.withRootsOfUnityDomain 3 2
  let message : Array F := #[1, 2]
  let received := ReedSolomonCode.encode code message
  let result := gsListDecode code received
  valuesToNats received =
    #[3, 1365638292, 2097283076, 782003361, 2130706432, 765068143, 33423359,
      1348703074] &&
    candidatesToNats result.candidates = #[#[1, 2]] && hasCandidate result message

#guard
  let code := ReedSolomonCode.withRootsOfUnityDomain 3 2
  let message : Array F := #[1, 2]
  let codeword := ReedSolomonCode.encode code message
  let received := introduceErrorsAtPositions codeword #[2]
  let result := gsListDecode code received
  valuesToNats received =
    #[3, 1365638292, 2097283077, 782003361, 2130706432, 765068143, 33423359,
      1348703074] &&
    candidatesToNats result.candidates = #[#[1, 2]] && hasCandidate result message

end GuruswamiSudanFast
end CodingTheory
end CompPoly
