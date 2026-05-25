/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPolyBench.Common
import CompPoly.CodingTheory.GuruswamiSudan
import CompPoly.CodingTheory.GuruswamiSudanFast

/-!
# Guruswami-Sudan Decoder Benchmarks

Benchmarks for the executable KoalaBear Guruswami-Sudan decoder.
-/

namespace CompPolyBench

open CompPoly.CodingTheory.GuruswamiSudan

private def gsWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 2 1 0

private def gsMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 20 5 1

private def checksumUniPoly (p : UniPoly) : Nat :=
  checksumArray checksumKoalaBear p

private def checksumDecodeResult (result : DecodeResult) : Nat :=
  let candidateChecksum := checksumArray checksumUniPoly result.candidates
  mixChecksum
    (mixChecksum
      (mixChecksum candidateChecksum result.multiplicity)
      result.degreeBound)
    result.errorBound

private def checksumFastUniPoly
    (p : CompPoly.CodingTheory.GuruswamiSudanFast.UniPoly) : Nat :=
  checksumArray KoalaBear.Fast.toNat p

private def checksumFastDecodeResult
    (result : CompPoly.CodingTheory.GuruswamiSudanFast.DecodeResult) : Nat :=
  let candidateChecksum := checksumArray checksumFastUniPoly result.candidates
  mixChecksum
    (mixChecksum
      (mixChecksum candidateChecksum result.multiplicity)
      result.degreeBound)
    result.errorBound

private structure GsBenchInput where
  code : ReedSolomonCode
  received : Array F
  inputShape : String

private structure FastGsBenchInput where
  code : CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode
  received : Array CompPoly.CodingTheory.GuruswamiSudanFast.F
  inputShape : String

private def consecutiveInput (withError : Bool) : GsBenchInput :=
  let code := ReedSolomonCode.withConsecutiveDomain 8 2
  let message : Array F := #[1, 2]
  let codeword := ReedSolomonCode.encode code message
  let received :=
    if withError then
      introduceErrorsAtPositions codeword #[1]
    else
      codeword
  {
    code := code
    received := received
    inputShape :=
      if withError then "RS(8,2), consecutive domain, 1 error"
      else "RS(8,2), consecutive domain, no errors"
  }

private def fastConsecutiveInput (withError : Bool) : FastGsBenchInput :=
  let code := CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode.withConsecutiveDomain 8 2
  let message : Array CompPoly.CodingTheory.GuruswamiSudanFast.F := #[1, 2]
  let codeword := CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode.encode code message
  let received :=
    if withError then
      CompPoly.CodingTheory.GuruswamiSudanFast.introduceErrorsAtPositions codeword #[1]
    else
      codeword
  {
    code := code
    received := received
    inputShape :=
      if withError then "RS(8,2), consecutive domain, 1 error"
      else "RS(8,2), consecutive domain, no errors"
  }

private def consecutiveRs16Input : GsBenchInput :=
  let code := ReedSolomonCode.withConsecutiveDomain 16 4
  let message : Array F := #[1, 2, 3, 4]
  let codeword := ReedSolomonCode.encode code message
  {
    code := code
    received := codeword
    inputShape := "RS(16,4), consecutive domain, no errors"
  }

private def fastConsecutiveRs16Input : FastGsBenchInput :=
  let code := CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode.withConsecutiveDomain 16 4
  let message : Array CompPoly.CodingTheory.GuruswamiSudanFast.F := #[1, 2, 3, 4]
  let codeword := CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode.encode code message
  {
    code := code
    received := codeword
    inputShape := "RS(16,4), consecutive domain, no errors"
  }

private def rootsOfUnityInput (withError : Bool) : GsBenchInput :=
  let code := ReedSolomonCode.withRootsOfUnityDomain 3 2
  let message : Array F := #[1, 2]
  let codeword := ReedSolomonCode.encode code message
  let received :=
    if withError then
      introduceErrorsAtPositions codeword #[2]
    else
      codeword
  {
    code := code
    received := received
    inputShape :=
      if withError then "RS(8,2), roots-of-unity domain, 1 error"
      else "RS(8,2), roots-of-unity domain, no errors"
  }

private def fastRootsOfUnityInput (withError : Bool) : FastGsBenchInput :=
  let code := CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode.withRootsOfUnityDomain 3 2
  let message : Array CompPoly.CodingTheory.GuruswamiSudanFast.F := #[1, 2]
  let codeword := CompPoly.CodingTheory.GuruswamiSudanFast.ReedSolomonCode.encode code message
  let received :=
    if withError then
      CompPoly.CodingTheory.GuruswamiSudanFast.introduceErrorsAtPositions codeword #[2]
    else
      codeword
  {
    code := code
    received := received
    inputShape :=
      if withError then "RS(8,2), roots-of-unity domain, 1 error"
      else "RS(8,2), roots-of-unity domain, no errors"
  }

private def runGsDecodeGroup (info : BenchGroupInfo) (input : GsBenchInput)
    (fastInput : FastGsBenchInput)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let warmup := gsWarmupIterations preset
  let measured := gsMeasuredIterations preset
  let checksumIterations := measured
  let canonicalRecord ← runTimed
    (info.groupKey ++ "-canonical") "GuruswamiSudan" "gsListDecode" "KoalaBear.Field"
    input.inputShape preset warmup measured
    (fun _ => gsListDecode input.code input.received)
    checksumDecodeResult (checksumIterations := checksumIterations)
  let fastRecord ← runTimed
    (info.groupKey ++ "-fast") "GuruswamiSudanFast" "gsListDecode" "KoalaBear.Fast.Field"
    fastInput.inputShape preset warmup measured
    (fun _ => CompPoly.CodingTheory.GuruswamiSudanFast.gsListDecode
      fastInput.code fastInput.received)
    checksumFastDecodeResult (checksumIterations := checksumIterations)
  pure ({
    groupKey := info.groupKey
    title := info.title
    records := #[canonicalRecord, fastRecord]
  }, gen)

def gsConsecutiveNoErrorInfo : BenchGroupInfo :=
  ⟨"gs-koalabear-consecutive-no-error",
    "Guruswami-Sudan decode, consecutive domain, no errors (KoalaBear)"⟩

def gsConsecutiveOneErrorInfo : BenchGroupInfo :=
  ⟨"gs-koalabear-consecutive-one-error",
    "Guruswami-Sudan decode, consecutive domain, one error (KoalaBear)"⟩

def gsConsecutiveRs16NoErrorInfo : BenchGroupInfo :=
  ⟨"gs-koalabear-consecutive-rs16-no-error",
    "Guruswami-Sudan decode, consecutive domain, RS(16,4), no errors (KoalaBear)"⟩

def gsRootsNoErrorInfo : BenchGroupInfo :=
  ⟨"gs-koalabear-roots-no-error",
    "Guruswami-Sudan decode, roots-of-unity domain, no errors (KoalaBear)"⟩

def gsRootsOneErrorInfo : BenchGroupInfo :=
  ⟨"gs-koalabear-roots-one-error",
    "Guruswami-Sudan decode, roots-of-unity domain, one error (KoalaBear)"⟩

def gsGroupInfos : List BenchGroupInfo := [
  gsConsecutiveNoErrorInfo,
  gsConsecutiveOneErrorInfo,
  gsConsecutiveRs16NoErrorInfo,
  gsRootsNoErrorInfo,
  gsRootsOneErrorInfo
]

def codingTheoryTasks : List BenchTask := [
  BenchTask.fromGroupRunner gsConsecutiveNoErrorInfo
    (runGsDecodeGroup gsConsecutiveNoErrorInfo (consecutiveInput false)
      (fastConsecutiveInput false)),
  BenchTask.fromGroupRunner gsConsecutiveOneErrorInfo
    (runGsDecodeGroup gsConsecutiveOneErrorInfo (consecutiveInput true)
      (fastConsecutiveInput true)),
  BenchTask.fromGroupRunner gsConsecutiveRs16NoErrorInfo
    (runGsDecodeGroup gsConsecutiveRs16NoErrorInfo consecutiveRs16Input
      fastConsecutiveRs16Input),
  BenchTask.fromGroupRunner gsRootsNoErrorInfo
    (runGsDecodeGroup gsRootsNoErrorInfo (rootsOfUnityInput false)
      (fastRootsOfUnityInput false)),
  BenchTask.fromGroupRunner gsRootsOneErrorInfo
    (runGsDecodeGroup gsRootsOneErrorInfo (rootsOfUnityInput true)
      (fastRootsOfUnityInput true))
]

end CompPolyBench
