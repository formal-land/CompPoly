/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import CompPoly.Fields.KoalaBear

/-!
# Executable Guruswami-Sudan Decoder

This module is a proof-light executable port of the Lambdaworks
`examples/reed-solomon-codes` Guruswami-Sudan decoder. It intentionally mirrors
the Lambdaworks educational implementation, including the same parameter search,
kernel-vector interpolation, Roth-Ruckenstein root-search heuristics, and small
brute-force fallbacks.

The first concrete field target is `KoalaBear.Field`.
-/

namespace CompPoly
namespace CodingTheory
namespace GuruswamiSudan

abbrev F := KoalaBear.Field
abbrev UniPoly := Array F

structure Bivariate where
  coeffs : Array UniPoly
deriving Repr, BEq, Inhabited

structure ReedSolomonCode where
  n : Nat
  k : Nat
  domain : Array F
deriving Repr, BEq, Inhabited

structure DecodeResult where
  candidates : Array UniPoly
  multiplicity : Nat
  degreeBound : Nat
  errorBound : Nat
deriving Repr, BEq, Inhabited

def maxCandidatesPerDepth : Nat := 15
def maxTotalRoots : Nat := 10

namespace NatUtil

def floorSqrt (n : Nat) : Nat := Id.run do
  let mut r := 0
  while (r + 1) * (r + 1) <= n do
    r := r + 1
  pure r

def ceilSqrt (n : Nat) : Nat :=
  let r := floorSqrt n
  if r * r = n then r else r + 1

def ceilSqrtDiv (num den : Nat) : Nat := Id.run do
  if den = 0 then
    pure 0
  else
    let mut r := 0
    while r * r * den < num do
      r := r + 1
    pure r

def binomial (n k : Nat) : Nat := Id.run do
  if k > n then
    pure 0
  else if k = 0 || k = n then
    pure 1
  else
    let kk := min k (n - k)
    let mut result := 1
    for i in [0:kk] do
      result := result * (n - i) / (i + 1)
    pure result

end NatUtil

namespace UniPoly

def zero : UniPoly := #[0]

def one : UniPoly := #[1]

def isZero (p : UniPoly) : Bool :=
  p.all (fun c => c == 0)

def trim (p : UniPoly) : UniPoly := Id.run do
  let mut last := p.size
  while 1 < last && p.getD (last - 1) 0 == 0 do
    last := last - 1
  if last = 0 then
    pure zero
  else
    pure (p.extract 0 last)

def coeff (p : UniPoly) (i : Nat) : F :=
  p.getD i 0

def degree (p : UniPoly) : Nat :=
  let q := trim p
  if q.isEmpty || isZero q then 0 else q.size - 1

def leadingCoeff (p : UniPoly) : F :=
  let q := trim p
  q.getD (q.size - 1) 0

def ofNatArray (xs : Array Nat) : UniPoly :=
  let ys : Array F := xs.map (fun x : Nat => (x : F))
  trim ys

def neg (p : UniPoly) : UniPoly :=
  trim (p.map fun c => -c)

def add (p q : UniPoly) : UniPoly := Id.run do
  let n := max p.size q.size
  let mut out := Array.replicate n (0 : F)
  for i in [0:n] do
    out := out.set! i (p.getD i 0 + q.getD i 0)
  pure (trim out)

def sub (p q : UniPoly) : UniPoly :=
  add p (neg q)

def scale (a : F) (p : UniPoly) : UniPoly :=
  trim (p.map fun c => a * c)

def mul (p q : UniPoly) : UniPoly := Id.run do
  if isZero p || isZero q then
    pure zero
  else
    let n := p.size + q.size - 1
    let mut out := Array.replicate n (0 : F)
    for i in [0:p.size] do
      for j in [0:q.size] do
        let value := out.getD (i + j) 0 + p.getD i 0 * q.getD j 0
        out := out.set! (i + j) value
    pure (trim out)

def mulXPow (p : UniPoly) (k : Nat) : UniPoly :=
  if isZero p then
    zero
  else
    trim (Array.replicate k (0 : F) ++ p)

def evaluate (p : UniPoly) (x : F) : F :=
  p.foldr (fun c acc => acc * x + c) 0

def pow (p : UniPoly) (e : Nat) : UniPoly := Id.run do
  let mut result := one
  for _ in [0:e] do
    result := mul result p
  pure result

def monomial (i : Nat) (c : F) : UniPoly :=
  if c == 0 then
    zero
  else
    (Array.replicate i (0 : F)).push c

def longDivRem? (num den : UniPoly) : Option (Prod UniPoly UniPoly) := Id.run do
  let den := trim den
  if isZero den then
    pure none
  else
    let mut rem := trim num
    let denDeg := degree den
    let denLead := leadingCoeff den
    let mut quot := Array.replicate
      (if degree rem < denDeg then 1 else degree rem - denDeg + 1) (0 : F)
    while !isZero rem && denDeg <= degree rem do
      let shift := degree rem - denDeg
      let coeff := leadingCoeff rem / denLead
      if quot.size <= shift then
        quot := quot ++ Array.replicate (shift + 1 - quot.size) (0 : F)
      quot := quot.set! shift (quot.getD shift 0 + coeff)
      rem := sub rem (mulXPow (scale coeff den) shift)
    pure (some (trim quot, trim rem))

def coeffsEq (p q : UniPoly) : Bool :=
  trim p == trim q

end UniPoly

namespace Bivariate

def zero : Bivariate := { coeffs := #[UniPoly.zero] }

def trimCoeffs (coeffs : Array UniPoly) : Array UniPoly := Id.run do
  let mut last := coeffs.size
  while 1 < last && UniPoly.isZero (coeffs.getD (last - 1) UniPoly.zero) do
    last := last - 1
  if last = 0 then
    pure #[UniPoly.zero]
  else
    pure (coeffs.extract 0 last)

def ofCoeffs (coeffs : Array UniPoly) : Bivariate :=
  { coeffs := trimCoeffs coeffs }

def isZero (q : Bivariate) : Bool :=
  q.coeffs.size = 1 && UniPoly.isZero (q.coeffs.getD 0 UniPoly.zero)

def yDegree (q : Bivariate) : Nat :=
  if isZero q then 0 else q.coeffs.size - 1

def maxXDegree (q : Bivariate) : Nat :=
  q.coeffs.foldl (fun acc p => max acc (UniPoly.degree p)) 0

def coeff (q : Bivariate) (i j : Nat) : F :=
  UniPoly.coeff (q.coeffs.getD j UniPoly.zero) i

def evaluate (q : Bivariate) (x y : F) : F := Id.run do
  let mut result : F := 0
  let mut yPow := (1 : F)
  for j in [0:q.coeffs.size] do
    let xEval := UniPoly.evaluate (q.coeffs.getD j UniPoly.zero) x
    result := result + xEval * yPow
    yPow := yPow * y
  pure result

def weightedDegree (q : Bivariate) (w : Nat) : Nat := Id.run do
  let mut maxDeg := 0
  for j in [0:q.coeffs.size] do
    let p := q.coeffs.getD j UniPoly.zero
    for i in [0:p.size] do
      if p.getD i 0 != 0 then
        maxDeg := max maxDeg (i + w * j)
  pure maxDeg

def evaluateYPolynomial (q : Bivariate) (f : UniPoly) : UniPoly := Id.run do
  let mut result := UniPoly.zero
  let mut fPow := UniPoly.one
  for j in [0:q.coeffs.size] do
    let term := UniPoly.mul (q.coeffs.getD j UniPoly.zero) fPow
    result := UniPoly.add result term
    fPow := UniPoly.mul fPow f
  pure (UniPoly.trim result)

def fromMonomials (monomials : Array (Prod Nat Nat)) (coefficients : Array F) : Bivariate := Id.run do
  let maxJ := monomials.foldl (fun acc pair => max acc pair.2) 0
  let mut rows : Array UniPoly := Array.replicate (maxJ + 1) (#[] : UniPoly)
  for idx in [0:monomials.size] do
    let (i, j) := monomials.getD idx (0, 0)
    let c := coefficients.getD idx 0
    let mut row := rows.getD j #[]
    while row.size <= i do
      row := row.push 0
    row := row.set! i c
    rows := rows.set! j row
  let polys := rows.map fun row =>
    if row.isEmpty then UniPoly.zero else UniPoly.trim row
  pure (ofCoeffs polys)

end Bivariate

namespace ReedSolomonCode

def withDomain (domain : Array F) (k : Nat) : ReedSolomonCode :=
  { n := domain.size, k := k, domain := domain }

def consecutiveDomain (n : Nat) : Array F := Id.run do
  let mut out := #[]
  for i in [0:n] do
    out := out.push (i : F)
  pure out

def withConsecutiveDomain (n k : Nat) : ReedSolomonCode :=
  withDomain (consecutiveDomain n) k

def pow2Domain (logN : Nat) : Array F := Id.run do
  let n := 2 ^ logN
  let omega := KoalaBear.twoAdicGenerators.toArray.getD logN (1 : F)
  let mut out := #[]
  let mut cur := (1 : F)
  for _ in [0:n] do
    out := out.push cur
    cur := cur * omega
  pure out

def withRootsOfUnityDomain (logN k : Nat) : ReedSolomonCode :=
  withDomain (pow2Domain logN) k

def encodePolynomial (code : ReedSolomonCode) (poly : UniPoly) : Array F :=
  code.domain.map fun x => UniPoly.evaluate poly x

def encode (code : ReedSolomonCode) (message : Array F) : Array F :=
  encodePolynomial code (UniPoly.trim message)

end ReedSolomonCode

def gsDecodingRadius (n k : Nat) : Nat :=
  let s := NatUtil.floorSqrt (n * k)
  if n <= s then 0 else n - s - 1

def johnsonListBound? (n k t : Nat) : Option Float :=
  let s := NatUtil.floorSqrt (n * k)
  let denominatorInt := n - t
  if denominatorInt <= s then
    none
  else
    some ((Float.ofNat n) / (Float.ofNat (denominatorInt - s)))

def countMonomials (d w : Nat) : Nat := Id.run do
  if w = 0 then
    pure d
  else
    let maxJ := d / w + 1
    let mut count := 0
    for j in [0:maxJ + 1] do
      let maxI := d - w * j
      count := count + maxI
    pure count

def chooseParameters (n k : Nat) : Prod Nat Nat := Id.run do
  let targetRadius := gsDecodingRadius n k
  for m in [1:21] do
    let radiusWithM := n - NatUtil.ceilSqrtDiv (n * k * (m + 1)) m
    if radiusWithM >= targetRadius then
      let constraintsPerPoint := m * (m + 1) / 2
      let totalConstraints := n * constraintsPerPoint
      let d := NatUtil.ceilSqrt (2 * totalConstraints * (k - 1)) + k
      let numMonomials := countMonomials d (k - 1)
      if numMonomials > totalConstraints then
        return (m, d)
  for m in [2:21] do
    let constraintsPerPoint := m * (m + 1) / 2
    let totalConstraints := n * constraintsPerPoint
    let d := NatUtil.ceilSqrt (2 * totalConstraints * (k - 1)) + k
    let numMonomials := countMonomials d (k - 1)
    if numMonomials > totalConstraints then
      return (m, d)
  pure (4, n + k)

def monomialsBelowWeightedDegree (d k : Nat) : Array (Prod Nat Nat) := Id.run do
  let w := k - 1
  let maxJ := if w = 0 then 0 else d / w + 1
  let mut monomials := #[]
  for j in [0:maxJ + 1] do
    let maxI := d - w * j
    for i in [0:maxI] do
      monomials := monomials.push (i, j)
  pure monomials

def findKernelVector (matrix : Array (Array F)) (numCols : Nat) : Array F := Id.run do
  let m := matrix.size
  let n := numCols
  if m = 0 then
    let mut result := Array.replicate n (0 : F)
    if 0 < n then
      result := result.set! 0 1
    pure result
  else
    let mut mat := matrix.map fun row =>
      if row.size < n then row ++ Array.replicate (n - row.size) (0 : F) else row
    let mut pivotCols : Array Nat := #[]
    let mut pivotRow := 0
    for col in [0:n] do
      if pivotRow < m then
        let mut found : Option Nat := none
        for row in [pivotRow:m] do
          if found.isNone && mat[row]!.getD col 0 != 0 then
            found := some row
        match found with
        | none => pure ()
        | some row =>
            let pivotData := mat[pivotRow]!
            let rowData := mat[row]!
            mat := (mat.set! pivotRow rowData).set! row pivotData
            pivotCols := pivotCols.push col
            let pivot := mat[pivotRow]!.getD col 0
            let pivotInv := pivot⁻¹
            let mut pivotRowData := mat[pivotRow]!
            for j in [col:n] do
              pivotRowData := pivotRowData.set! j (pivotRowData.getD j 0 * pivotInv)
            mat := mat.set! pivotRow pivotRowData
            let pivotSlice := mat[pivotRow]!.extract col n
            for row2 in [0:m] do
              if row2 != pivotRow && mat[row2]!.getD col 0 != 0 then
                let factor := mat[row2]!.getD col 0
                let mut rowData := mat[row2]!
                for offset in [0:pivotSlice.size] do
                  let j := col + offset
                  let sub := factor * pivotSlice.getD offset 0
                  rowData := rowData.set! j (rowData.getD j 0 - sub)
                mat := mat.set! row2 rowData
            pivotRow := pivotRow + 1
    let mut freeCol : Option Nat := none
    for col in [0:n] do
      if freeCol.isNone && !(pivotCols.contains col) then
        freeCol := some col
    let mut kernel := Array.replicate n (0 : F)
    match freeCol with
    | some fc =>
        kernel := kernel.set! fc 1
        for row in [0:pivotCols.size] do
          let pc := pivotCols[row]!
          if row < m then
            kernel := kernel.set! pc (-(mat[row]!.getD fc 0))
    | none =>
        if 0 < n then
          kernel := kernel.set! (n - 1) 1
    pure kernel

def interpolateWithMultiplicity
    (domain received : Array F) (m d k : Nat) : Bivariate := Id.run do
  let monomials := monomialsBelowWeightedDegree d k
  let numMonomials := monomials.size
  let constraintsPerPoint := m * (m + 1) / 2
  let totalConstraints := domain.size * constraintsPerPoint
  let mut matrix : Array (Array F) := Array.mkEmpty totalConstraints
  for idx in [0:domain.size] do
    let alpha := domain.getD idx 0
    let y := received.getD idx 0
    for totalOrder in [0:m] do
      for b in [0:totalOrder + 1] do
        let a := totalOrder - b
        let mut row := Array.replicate numMonomials (0 : F)
        for monIdx in [0:monomials.size] do
          let (i, j) := monomials[monIdx]!
          if !(i < a || j < b) then
            let coeffScalar := NatUtil.binomial i a * NatUtil.binomial j b
            let coeff : F := (coeffScalar : F) * (alpha ^ (i - a)) * (y ^ (j - b))
            row := row.set! monIdx coeff
        matrix := matrix.push row
  let solution := findKernelVector matrix numMonomials
  pure (Bivariate.fromMonomials monomials solution)

def extractSmallValue? (fe : F) : Option Nat := Id.run do
  for i in [0:101] do
    if fe == (i : F) then
      return some i
  pure none

def lagrangeInterpolateAtZeroWithPoints? (points : Array (Prod Nat F)) : Option F := Id.run do
  if points.isEmpty then
    pure none
  else
    let n := points.size
    let mut result : F := 0
    for i in [0:n] do
      let (xi, yi) := points[i]!
      let xiFe : F := xi
      let mut numerator := (1 : F)
      let mut denominator := (1 : F)
      for j in [0:n] do
        if j != i then
          let (xj, _) := points[j]!
          let xjFe : F := xj
          numerator := numerator * (-xjFe)
          denominator := denominator * (xiFe - xjFe)
      if denominator == 0 then
        return none
      result := result + yi * (numerator / denominator)
    pure (some result)

def lagrangeInterpolatePolynomial? (points : Array (Prod Nat F)) (maxDegree : Nat) :
    Option UniPoly := Id.run do
  if points.isEmpty || points.size > maxDegree then
    pure none
  else
    let n := points.size
    let mut coeffs := Array.replicate n (0 : F)
    for i in [0:n] do
      let (xi, yi) := points[i]!
      let xiFe : F := xi
      let mut basis : UniPoly := #[1]
      let mut denominator := (1 : F)
      for j in [0:n] do
        if j != i then
          let (xj, _) := points[j]!
          let xjFe : F := xj
          let mut next := Array.replicate (basis.size + 1) (0 : F)
          for bIdx in [0:basis.size] do
            let c := basis[bIdx]!
            next := next.set! (bIdx + 1) (next.getD (bIdx + 1) 0 + c)
            next := next.set! bIdx (next.getD bIdx 0 - c * xjFe)
          basis := next
          denominator := denominator * (xiFe - xjFe)
      if denominator == 0 then
        return none
      let denomInv := 1 / denominator
      for bIdx in [0:basis.size] do
        if bIdx < coeffs.size then
          coeffs := coeffs.set! bIdx (coeffs.getD bIdx 0 + yi * (basis[bIdx]! * denomInv))
    pure (some (UniPoly.trim coeffs))

def substituteAndDivide (q : Bivariate) (c : F) : Bivariate := Id.run do
  let yDeg := Bivariate.yDegree q
  let maxXDeg := Bivariate.maxXDegree q + yDeg
  let maxYDeg := yDeg
  let mut result : Array UniPoly :=
    Array.replicate (maxYDeg + 1) (Array.replicate (maxXDeg + 2) (0 : F))
  for j in [0:q.coeffs.size] do
    let qj := q.coeffs[j]!
    for kk in [0:j + 1] do
      let binom := NatUtil.binomial j kk
      let scale : F := (binom : F) * (c ^ (j - kk))
      let mut row := result[kk]!
      for i in [0:qj.size] do
        let xPower := i + kk
        if xPower <= maxXDeg + 1 && kk <= maxYDeg then
          row := row.set! xPower (row.getD xPower 0 + qj.getD i 0 * scale)
      result := result.set! kk row
  let divided := result.map fun row =>
    if row.size <= 1 then UniPoly.zero else UniPoly.trim (row.extract 1 row.size)
  pure (Bivariate.ofCoeffs divided)

def findRootsLinearY (q : Bivariate) (maxDegree : Nat) : Array UniPoly :=
  if q.coeffs.size < 2 then
    #[]
  else
    let a := q.coeffs.getD 0 UniPoly.zero
    let b := q.coeffs.getD 1 UniPoly.zero
    let negA := UniPoly.neg a
    match UniPoly.longDivRem? negA b with
    | none => #[]
    | some (quot, rem) =>
        if !UniPoly.isZero rem then
          #[]
        else if UniPoly.degree quot >= maxDegree then
          #[]
        else
          #[quot]

def appendUniquePoly (roots : Array UniPoly) (candidate : UniPoly) : Array UniPoly :=
  if roots.any (fun p => UniPoly.coeffsEq p candidate) then roots else roots.push candidate

def appendUniqueField (roots : Array F) (candidate : F) : Array F :=
  if roots.contains candidate then roots else roots.push candidate

partial def enumerateSmallPolys
    (q : Bivariate) (maxDegree adjustedMaxCoeff totalCandidates idx : Nat)
    (roots : Array UniPoly) : Array UniPoly :=
  if idx >= totalCandidates then
    roots
  else
    Id.run do
      let mut coeffs : Array F := #[]
      let mut value := idx
      for _ in [0:maxDegree] do
        coeffs := coeffs.push ((value % (adjustedMaxCoeff + 1) : Nat) : F)
        value := value / (adjustedMaxCoeff + 1)
      let candidate := UniPoly.trim coeffs
      let roots :=
        if UniPoly.isZero candidate then
          roots
        else if UniPoly.isZero (Bivariate.evaluateYPolynomial q candidate) then
          appendUniquePoly roots candidate
        else
          roots
      pure (enumerateSmallPolys q maxDegree adjustedMaxCoeff totalCandidates (idx + 1) roots)

def trySmallIntegerPolynomials
    (q : Bivariate) (maxDegree maxCoeff : Nat) (roots : Array UniPoly) : Array UniPoly :=
  let adjustedMaxCoeff :=
    if maxDegree <= 2 then maxCoeff
    else if maxDegree <= 3 then min maxCoeff 30
    else if maxDegree <= 4 then min maxCoeff 15
    else min maxCoeff 8
  let totalCandidates := (adjustedMaxCoeff + 1) ^ maxDegree
  if totalCandidates > 200000 then
    roots
  else
    enumerateSmallPolys q maxDegree adjustedMaxCoeff totalCandidates 0 roots

def tryDirectRoots
    (q : Bivariate) (maxDegree : Nat) (hintValues : Array F)
    (roots : Array UniPoly) : Array UniPoly := Id.run do
  let mut roots := roots
  if maxDegree <= 4 then
    roots := trySmallIntegerPolynomials q maxDegree 20 roots
  for hint in hintValues do
    let candidate := #[hint]
    if UniPoly.isZero (Bivariate.evaluateYPolynomial q candidate) then
      roots := appendUniquePoly roots candidate
  pure roots

def tryInterpolatedCandidates
    (q : Bivariate) (maxDegree : Nat) (hintValues domain : Array F)
    (roots : Array UniPoly) : Array UniPoly := Id.run do
  let mut roots := roots
  if hintValues.size < maxDegree || domain.size < maxDegree then
    pure roots
  else
    let n := min hintValues.size domain.size
    let limit := min (n - maxDegree + 1) 20
    for start in [0:limit] do
      if start + maxDegree <= n then
        let mut points : Array (Prod Nat F) := #[]
        for idx in [start:start + maxDegree] do
          match extractSmallValue? (domain[idx]!) with
          | some alpha => points := points.push (alpha, hintValues[idx]!)
          | none => pure ()
        if points.size = maxDegree then
          match lagrangeInterpolatePolynomial? points maxDegree with
          | some candidate =>
              if UniPoly.isZero (Bivariate.evaluateYPolynomial q candidate) then
                roots := appendUniquePoly roots candidate
                if roots.size >= maxTotalRoots then
                  return roots
          | none => pure ()
    pure roots

partial def findUnivariateRootsWithHints (coeffs hintValues : Array F) : Array F :=
  if coeffs.isEmpty || coeffs.all (fun c => c == 0) then
    Id.run do
      let mut roots : Array F := #[]
      for i in [0:20] do
        roots := appendUniqueField roots (i : F)
      for hint in hintValues do
        roots := appendUniqueField roots hint
      pure roots
  else
    let poly := UniPoly.trim coeffs
    let deg := UniPoly.degree poly
    if deg = 0 then
      #[]
    else if deg = 1 then
      let a := poly.getD 1 0
      let b := poly.getD 0 0
      if a == 0 then #[] else #[(-b) / a]
    else
      Id.run do
        let maxRoots := deg
        let mut roots : Array F := #[]
        for hint in hintValues do
          if UniPoly.evaluate poly hint == 0 then
            roots := appendUniqueField roots hint
            if roots.size >= maxRoots then
              return roots
        for i in [0:2000] do
          let elem : F := i
          if UniPoly.evaluate poly elem == 0 then
            roots := appendUniqueField roots elem
            if roots.size >= maxRoots then
              return roots
        for i in [1:2000] do
          let elem : F := -(i : F)
          if UniPoly.evaluate poly elem == 0 then
            roots := appendUniqueField roots elem
            if roots.size >= maxRoots then
              return roots
        pure roots

partial def findUnivariateRootsWithHintsAndDomain
    (coeffs hintValues domain : Array F) : Array F :=
  if coeffs.isEmpty || coeffs.all (fun c => c == 0) then
    Id.run do
      let mut roots : Array F := #[]
      if hintValues.size >= 3 && domain.size >= 3 then
        let minLen := min hintValues.size domain.size
        for start in [0:min minLen 10] do
          for size in [3:min minLen 6 + 1] do
            if start + size <= minLen then
              let mut subset : Array (Prod Nat F) := #[]
              for idx in [start:start + size] do
                match extractSmallValue? (domain[idx]!) with
                | some alpha => subset := subset.push (alpha, hintValues[idx]!)
                | none => pure ()
              if subset.size = size then
                match lagrangeInterpolateAtZeroWithPoints? subset with
                | some root => roots := appendUniqueField roots root
                | none => pure ()
      for i in [0:20] do
        roots := appendUniqueField roots (i : F)
      pure roots
  else
    findUnivariateRootsWithHints coeffs hintValues
partial def rrSearchWithDomain
    (q : Bivariate) (maxDegree : Nat) (currentCoeffs : Array F)
    (roots : Array UniPoly) (hintValues domain : Array F) (depth : Nat) : Array UniPoly :=
  if roots.size >= maxTotalRoots then
    roots
  else
    Id.run do
      let qAtZero := q.coeffs.map fun p => UniPoly.evaluate p 0
      let yRootsAll := findUnivariateRootsWithHintsAndDomain qAtZero hintValues domain
      let yRoots := yRootsAll.extract 0 (min yRootsAll.size maxCandidatesPerDepth)
      let mut roots := roots
      for yRoot in yRoots do
        if roots.size >= maxTotalRoots then
          return roots
        let newCoeffs := currentCoeffs.push yRoot
        if newCoeffs.size <= maxDegree then
          let qTransformed := substituteAndDivide q yRoot
          if Bivariate.isZero qTransformed then
            roots := appendUniquePoly roots (UniPoly.trim newCoeffs)
          else if newCoeffs.size < maxDegree then
            let mut transformedHints : Array F := #[]
            let mut filteredDomain : Array F := #[]
            for idx in [0:min hintValues.size domain.size] do
              let alpha := domain[idx]!
              if alpha != 0 then
                transformedHints := transformedHints.push ((hintValues[idx]! - yRoot) / alpha)
                filteredDomain := filteredDomain.push alpha
            roots := rrSearchWithDomain qTransformed maxDegree newCoeffs roots
              transformedHints filteredDomain (depth + 1)
          let candidate := UniPoly.trim newCoeffs
          if !candidate.isEmpty &&
              UniPoly.isZero (Bivariate.evaluateYPolynomial q candidate) then
            roots := appendUniquePoly roots candidate
      pure roots

def findPolynomialRootsWithDomain
    (q : Bivariate) (maxDegree : Nat) (hintValues domain : Array F) : Array UniPoly :=
  if Bivariate.yDegree q <= 1 then
    findRootsLinearY q maxDegree
  else
    let roots := tryInterpolatedCandidates q maxDegree hintValues domain #[]
    let roots :=
      if maxDegree <= 10 && roots.size < maxTotalRoots then
        tryDirectRoots q maxDegree hintValues roots
      else
        roots
    if roots.size < maxTotalRoots then
      rrSearchWithDomain q maxDegree #[] roots hintValues domain 0
    else
      roots

def agreement (received domain : Array F) (poly : UniPoly) : Nat := Id.run do
  let mut count := 0
  for i in [0:min received.size domain.size] do
    if UniPoly.evaluate poly domain[i]! == received[i]! then
      count := count + 1
  pure count

def gsListDecodeWithMultiplicity
    (code : ReedSolomonCode) (received : Array F) (multiplicity : Nat) : DecodeResult :=
  let n := code.n
  let k := code.k
  let m := multiplicity
  let constraintsPerPoint := m * (m + 1) / 2
  let totalConstraints := n * constraintsPerPoint
  let d := NatUtil.ceilSqrt (2 * totalConstraints * (k - 1)) + k
  let q := interpolateWithMultiplicity code.domain received m d k
  let allRoots := findPolynomialRootsWithDomain q k received code.domain
  let errorBound := gsDecodingRadius n k
  let agreementThreshold := n - errorBound
  let candidates :=
    allRoots.filter fun f =>
      UniPoly.degree f < k && agreement received code.domain f >= agreementThreshold
  {
    candidates := candidates
    multiplicity := m
    degreeBound := d
    errorBound := errorBound
  }

def gsListDecode (code : ReedSolomonCode) (received : Array F) : DecodeResult :=
  if received.size != code.n then
    panic! "received word length must equal code length"
  else
    let params := chooseParameters code.n code.k
    let m := params.1
    let d := params.2
    let q := interpolateWithMultiplicity code.domain received m d code.k
    let allRoots := findPolynomialRootsWithDomain q code.k received code.domain
    let errorBound := gsDecodingRadius code.n code.k
    let agreementThreshold := code.n - errorBound
    let candidates :=
      allRoots.filter fun f =>
        UniPoly.degree f < code.k && agreement received code.domain f >= agreementThreshold
    {
      candidates := candidates
      multiplicity := m
      degreeBound := d
      errorBound := errorBound
    }

def introduceErrors (codeword : Array F) (positions values : Array Nat) : Array F := Id.run do
  let mut out := codeword
  for i in [0:min positions.size values.size] do
    let pos := positions[i]!
    if pos < out.size then
      out := out.set! pos (out[pos]! + (values[i]! : F))
  pure out

def introduceErrorsAtPositions (codeword : Array F) (positions : Array Nat) : Array F :=
  introduceErrors codeword positions (positions.mapIdx fun i _ => i + 1)

def polyToNats (p : UniPoly) : Array Nat :=
  (UniPoly.trim p).map ZMod.val

def valuesToNats (xs : Array F) : Array Nat :=
  xs.map ZMod.val

def candidatesToNats (xs : Array UniPoly) : Array (Array Nat) :=
  xs.map polyToNats

end GuruswamiSudan
end CodingTheory
end CompPoly
