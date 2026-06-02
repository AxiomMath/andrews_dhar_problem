import Mathlib

/-!
# Problem statement: the Φ₃ bijection (Andrews–Dhar, m = 3)

A partition is a weakly decreasing finite list of nonnegative integers.
This file states **only** the theorem (`phi3_bijOn`) together with the
declarations needed to express it; the proof lives in `solution.lean`.
-/

/-- A positive partition is a weakly decreasing list where all parts are positive. -/
def IsPositivePartition (l : List ℕ) : Prop :=
  l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, 0 < x

/-- A positive partition $(\alpha_1, \ldots, \alpha_r)$ is 3-flat if:
  - $\alpha_i - \alpha_{i+1} < 3$ for all $1 \le i < r$, and
  - $\alpha_r < 3$.
  The empty partition is also 3-flat. -/
def IsThreeFlat (l : List ℕ) : Prop :=
  IsPositivePartition l ∧
  (∀ (i : ℕ) (hi : i + 1 < l.length),
    l[i]'(by omega) - l[i + 1]'hi < 3) ∧
  (∀ h : l ≠ [], l.getLast h < 3)

/-- A positive partition is 3-regular if none of its parts is divisible by 3. -/
def IsThreeRegular (l : List ℕ) : Prop :=
  IsPositivePartition l ∧ ∀ x ∈ l, ¬(3 ∣ x)

/-- Decidable check: a list represents a positive partition. -/
def isPositivePartitionBool (l : List ℕ) : Bool :=
  decide (l.Pairwise (· ≥ ·)) && l.all (· > 0)

/-- Decidable check: a list is 3-flat. -/
def isThreeFlatBool (l : List ℕ) : Bool :=
  isPositivePartitionBool l &&
  (List.range (l.length - 1)).all (fun i =>
    decide (l[i]! - l[i+1]! < 3)) &&
  (match l.getLast? with | none => true | some x => decide (x < 3))

/-- Decidable check: whether the part at index i is flat-removable. -/
def isFlatRemovableBool (l : List ℕ) (i : ℕ) : Bool :=
  i < l.length && (l[i]! % 3 == 0) && isThreeFlatBool (l.eraseIdx i)

/-- The nonzero residue sequence of a partition: delete all parts divisible by 3,
    then record the residues mod 3 of the remaining parts (in order).
    The result is a list with entries in $\{1, 2\}$. -/
def nonzeroResSeq (l : List ℕ) : List ℕ :=
  (l.filter (fun x => ¬(x % 3 == 0))).map (fun x => x % 3)

/-- Given a sequence $v = (v_1, \ldots, v_k)$ with entries in $\{1, 2\}$, construct the
    residue core $\Lambda(v)$: the unique 3-flat, 3-regular partition whose $i$-th part
    is congruent to $v_i$ mod 3.

    Construction (right to left):
    - $c_k = v_k$
    - $c_i$ is the unique element of $\{c_{i+1}, c_{i+1}+1, c_{i+1}+2\}$ with
      $c_i \equiv v_i \pmod{3}$. -/
def residueCore : List ℕ → List ℕ
  | [] => []
  | [v] => [v]
  | v :: rest =>
    let tail := residueCore rest
    match tail with
    | [] => [v]  -- unreachable for nonempty rest
    | c_next :: _ =>
      let c_i := if c_next % 3 == v % 3 then c_next
                 else if (c_next + 1) % 3 == v % 3 then c_next + 1
                 else c_next + 2
      c_i :: tail

/-- The conjugate (transpose) of a partition. The $j$-th part of the conjugate equals
    $|\{i : \nu_i \ge j\}|$. Assumes input is a weakly decreasing list of positive naturals. -/
def conjugate (l : List ℕ) : List ℕ :=
  match l with
  | [] => []
  | a :: _ =>
    (List.range a).map (fun j => (l.filter (fun x => x ≥ j + 1)).length)

/-- Componentwise addition of two lists, padding the shorter one with zeros. -/
def zipAddPad (l₁ l₂ : List ℕ) : List ℕ :=
  let n := max l₁.length l₂.length
  (List.range n).map (fun i =>
    (l₁[i]?.getD 0) + (l₂[i]?.getD 0))

/-- S2 of the forward algorithm: scan from the end (smallest part) toward the front.
    When a flat-removable part is found, delete it and record value/3.
    The scan is dynamic: after deletion, continue from the next part above.
    Uses fuel for termination. -/
def scanFromSmallest (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (A, rec)
  | fuel' + 1 =>
    if idx >= A.length then (A, rec)
    else
      let actualIdx := A.length - 1 - idx
      if isFlatRemovableBool A actualIdx then
        let val := A[actualIdx]!
        let A' := A.eraseIdx actualIdx
        scanFromSmallest fuel' A' idx (rec ++ [val / 3])
      else
        scanFromSmallest fuel' A (idx + 1) rec

/-- S3 of the forward algorithm: scan from the front (largest part) toward the end.
    If the current part $A_i = 3a$ is a multiple of 3, delete it, subtract 3 from
    each of the $i$ parts before it (indices $0, \ldots, i-1$), and record $a + i$.
    Uses fuel for termination. -/
def scanFromLargest (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (A, rec)
  | fuel' + 1 =>
    if idx >= A.length then (A, rec)
    else
      let val := A[idx]!
      if val % 3 == 0 && val > 0 then
        let a := val / 3
        let A' := A.eraseIdx idx
        let A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
        scanFromLargest fuel' A'' idx (rec ++ [a + idx])
      else
        scanFromLargest fuel' A (idx + 1) rec

/-- The forward map $\Phi_3$: given a 3-flat partition $\alpha$, produce a 3-regular partition
    via the deletion algorithm.

    S1. Start with $A = \alpha$ and empty record list.
    S2. Scan from smallest to largest, deleting flat-removable multiples of 3.
    S3. Scan from largest to smallest, deleting remaining multiples of 3
        (with subtraction of 3 from parts above).
    S4. Sort record into partition $\nu$, output $\Lambda(\mathrm{res}(\alpha)) + 3\nu'$
        (componentwise sum, padding with zeros). -/
def phi3Forward (l : List ℕ) : List ℕ :=
  -- S2: scan from smallest to largest, deleting flat-removable multiples of 3
  let (A₂, rec₂) := scanFromSmallest (l.length + 1) l 0 []
  -- S3: scan from largest to smallest, removing remaining multiples of 3
  let (_, rec₃) := scanFromLargest (A₂.length + 1) A₂ 0 rec₂
  -- S4: sort record list into weakly decreasing partition ν
  let ν := rec₃.mergeSort (· ≥ ·)
  -- Compute conjugate ν'
  let ν' := conjugate ν
  -- Compute Λ(res(α))
  let core := residueCore (nonzeroResSeq l)
  -- Output: Λ(res α) + 3ν' (componentwise)
  zipAddPad core (ν'.map (· * 3))

/-- Glaisher's theorem for $m = 3$ (Andrews–Dhar form): the number of 3-flat
    partitions of $N$ equals the number of 3-regular partitions of $N$, for
    every non-negative integer $N$.

    Classically, Glaisher's identity gives equicardinality between
    `count < 3` partitions and 3-regular partitions; a separate elementary
    bijection between `count < 3` partitions and 3-flat partitions
    (Andrews–Dhar §2 background) yields the form below, which is the
    cardinality we actually use to derive Direction L of the $\Phi_3$
    bijection from Direction R. -/
def Glaisher3 : Prop :=
  ∀ N : ℕ,
    Set.ncard {l : List ℕ | IsThreeFlat l ∧ l.sum = N} =
    Set.ncard {l : List ℕ | IsThreeRegular l ∧ l.sum = N}

/-- **The Φ₃ bijection.** At each fixed weight `N`, the forward map `phi3Forward`
is a bijection (`Set.BijOn`) from the 3-flat partitions of `N` onto the 3-regular
partitions of `N`, assuming Glaisher's theorem for `m = 3` (`Glaisher3`). -/
theorem phi3_bijOn (hGlaisher : Glaisher3) (N : ℕ) :
    Set.BijOn phi3Forward
      {α | IsThreeFlat α ∧ α.sum = N}
      {β | IsThreeRegular β ∧ β.sum = N} := by sorry
