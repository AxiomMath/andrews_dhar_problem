import Mathlib

/-
# Problem Description

We formalize a weight-preserving bijection $\Phi_3$ from the set of 3-flat partitions
to the set of 3-regular partitions, following the Andrews-Dhar deletion/insertion algorithm.

A partition is a weakly decreasing finite list of nonnegative integers.
A positive partition has all parts positive.
A partition is 3-flat if it is positive, consecutive gaps are $< 3$, and the last part is $< 3$.
A partition is 3-regular if it is positive and no part is divisible by 3.

The map $\Phi_3$ (forward/deletion algorithm) and its inverse $\Phi_3^{-1}$
(insertion algorithm) are constructed, and the main theorem states that $\Phi_3$
is a weight-preserving bijection that also preserves the nonzero residue sequence.
-/

/-! ## Partition predicates -/

/-- A list represents a partition if it is weakly decreasing (allowing zeros). -/
def IsPartition (l : List ℕ) : Prop :=
  l.Pairwise (· ≥ ·)

/-- A positive partition is a weakly decreasing list where all parts are positive. -/
def IsPositivePartition (l : List ℕ) : Prop :=
  l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, 0 < x

/-- The weight of a partition is the sum of its parts. -/
def partWeight (l : List ℕ) : ℕ := l.sum

/-! ## 3-flat partitions -/

/-- A positive partition $(\alpha_1, \ldots, \alpha_r)$ is 3-flat if:
  - $\alpha_i - \alpha_{i+1} < 3$ for all $1 \le i < r$, and
  - $\alpha_r < 3$.
  The empty partition is also 3-flat. -/
def IsThreeFlat (l : List ℕ) : Prop :=
  IsPositivePartition l ∧
  (∀ (i : ℕ) (hi : i + 1 < l.length),
    l[i]'(by omega) - l[i + 1]'hi < 3) ∧
  (∀ h : l ≠ [], l.getLast h < 3)

/-! ## 3-regular partitions -/

/-- A positive partition is 3-regular if none of its parts is divisible by 3. -/
def IsThreeRegular (l : List ℕ) : Prop :=
  IsPositivePartition l ∧ ∀ x ∈ l, ¬(3 ∣ x)

/-! ## Decidable helpers for the algorithms -/

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

/-! ## Nonzero residue sequence -/

/-- The nonzero residue sequence of a partition: delete all parts divisible by 3,
    then record the residues mod 3 of the remaining parts (in order).
    The result is a list with entries in $\{1, 2\}$. -/
def nonzeroResSeq (l : List ℕ) : List ℕ :=
  (l.filter (fun x => ¬(x % 3 == 0))).map (fun x => x % 3)

theorem nonzeroResSeq_in_one_two (l : List ℕ) :
    ∀ x ∈ nonzeroResSeq l, x = 1 ∨ x = 2 := by
  intro x hx
  unfold nonzeroResSeq at hx
  rcases List.mem_map.mp hx with ⟨y, hy_mem, rfl⟩
  have h3 : 0 < (3 : ℕ) := by norm_num
  have hlt := Nat.mod_lt y h3
  simp only [List.mem_filter, beq_iff_eq, decide_not, Bool.not_eq_true',
             decide_eq_false_iff_not] at hy_mem
  omega

/-! ## Residue core $\Lambda(v)$ -/

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

/-! ## Conjugate partition -/

/-- The conjugate (transpose) of a partition. The $j$-th part of the conjugate equals
    $|\{i : \nu_i \ge j\}|$. Assumes input is a weakly decreasing list of positive naturals. -/
def conjugate (l : List ℕ) : List ℕ :=
  match l with
  | [] => []
  | a :: _ =>
    (List.range a).map (fun j => (l.filter (fun x => x ≥ j + 1)).length)

/-! ## Componentwise addition with zero-padding -/

/-- Componentwise addition of two lists, padding the shorter one with zeros. -/
def zipAddPad (l₁ l₂ : List ℕ) : List ℕ :=
  let n := max l₁.length l₂.length
  (List.range n).map (fun i =>
    (l₁[i]?.getD 0) + (l₂[i]?.getD 0))

/-! ## Forward algorithm S2: Scan from smallest to largest -/

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

/-! ## Forward algorithm S3: Scan from largest to smallest -/

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

/-! ## The forward map $\Phi_3$ (deletion algorithm) -/

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

/-! ## Inverse algorithm: Hard and Easy insertions -/

/-- Attempt a hard insertion of size $p$ at position $h$: add 3 to the first $h$ parts
    and insert $3(p-h)$ after them. Returns the resulting list if admissible
    (result is 3-flat and the inserted multiple of 3 is NOT flat-removable).
    Requires $0 \le h \le p - 1$ and $h \le A.\mathrm{length}$. -/
def tryHardInsertion (A : List ℕ) (p : ℕ) (h : ℕ) : Option (List ℕ) :=
  if h >= p ∨ h > A.length then none
  else
    let newPart := 3 * (p - h)
    let raised := A.zipIdx |>.map (fun (x, j) => if j < h then x + 3 else x)
    let result := List.insertIdx raised h newPart
    if isThreeFlatBool result && !(isFlatRemovableBool result h) then
      some result
    else
      none

/-- Find the first admissible hard insertion of size $p$
    (trying $h = 0, 1, \ldots, \min(p-1, A.\mathrm{length})$). -/
def findHardInsertion (A : List ℕ) (p : ℕ) (h : ℕ := 0) : Option (List ℕ) :=
  if h >= p ∨ h > A.length then none
  else
    match tryHardInsertion A p h with
    | some result => some result
    | none => findHardInsertion A p (h + 1)
termination_by p + A.length + 1 - h

/-- Attempt an easy insertion of size $p$: insert $3p$ in weakly decreasing order.
    Returns the result if admissible (result is 3-flat and inserted part IS flat-removable). -/
def tryEasyInsertion (A : List ℕ) (p : ℕ) : Option (List ℕ) :=
  let newPart := 3 * p
  -- Find position to insert in weakly decreasing order
  let pos := (A.takeWhile (· ≥ newPart)).length
  let result := List.insertIdx A pos newPart
  if isThreeFlatBool result && isFlatRemovableBool result pos then
    some result
  else
    none

/-- Perform one insertion step of the inverse algorithm:
    use an admissible hard insertion if one exists; otherwise use the easy insertion.
    The fallback (returning A unchanged) should be unreachable for valid 3-regular inputs;
    see theorem `performInsertion_always_succeeds` below. -/
def performInsertion (A : List ℕ) (p : ℕ) : List ℕ :=
  match findHardInsertion A p with
  | some result => result
  | none =>
    match tryEasyInsertion A p with
    | some result => result
    | none => A  -- unreachable for valid inputs; see theorem below

/-- Process all parts of $\nu$ from largest to smallest, performing insertions. -/
def processInsertions : List ℕ → List ℕ → List ℕ
  | [], A => A
  | p :: rest, A => processInsertions rest (performInsertion A p)

/-! ## The inverse map $\Phi_3^{-1}$ (insertion algorithm) -/

/-- The inverse map $\Phi_3^{-1}$: given a 3-regular partition $\beta$, produce a
    3-flat partition via the insertion algorithm.

    1. Compute $v = \mathrm{res}(\beta)$ and $A = \Lambda(v)$.
    2. Since $\beta$ is 3-regular, $\beta$ and $A$ have the same length and
       $A_i \equiv \beta_i \pmod{3}$. Set $q_i := (\beta_i - A_i)/3$.
    3. Compute $\nu := q'$ (the conjugate of the partition $q$).
    4. Process parts of $\nu$ from largest to smallest using admissible insertions
       (hard if possible, otherwise easy).
    5. Return the resulting 3-flat partition. -/
def phi3Inverse (l : List ℕ) : List ℕ :=
  let v := nonzeroResSeq l
  let A := residueCore v
  let q := (List.range A.length).map (fun i =>
    ((l[i]?.getD 0) - (A[i]?.getD 0)) / 3)
  let ν := conjugate q
  processInsertions ν A

/-! ## Theorem 1 (Glaisher's theorem for m=3, assumed without proof) -/

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

/-- Abbreviation: the sorted record list produced by S2 followed by S3 on `l`. -/
private def sortedRec (l : List ℕ) : List ℕ :=
  let (A₂, rec₂) := scanFromSmallest (l.length + 1) l 0 []
  let (_, rec₃) := scanFromLargest (A₂.length + 1) A₂ 0 rec₂
  rec₃.mergeSort (· ≥ ·)

/-! ## Forward declarations for labeled scaffold -/

private lemma isThreeFlatBool_implies' (l : List ℕ) (h : isThreeFlatBool l = true) :
    IsThreeFlat l := by
  unfold isThreeFlatBool isPositivePartitionBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hpw, hall⟩, hgaps⟩, hlast⟩ := h
  refine ⟨⟨hpw, ?_⟩, ?_, ?_⟩
  · intro x hx; exact hall x hx
  · intro i hi
    have hgi := hgaps i (by omega)
    rw [getElem!_pos l i (by omega), getElem!_pos l (i+1) (by omega)] at hgi
    exact hgi
  · intro hne
    rw [List.getLast?_eq_some_getLast hne] at hlast
    simpa using hlast

private lemma tryHardInsertion_isThreeFlatBool' {A : List ℕ} {p h : ℕ} {result : List ℕ}
    (hsome : tryHardInsertion A p h = some result) :
    isThreeFlatBool result = true := by
  simp only [tryHardInsertion] at hsome
  split at hsome
  · simp at hsome
  · split at hsome
    · next hcond =>
      have heq := Option.some.inj hsome.symm
      rw [heq]
      simp only [Bool.and_eq_true] at hcond
      exact hcond.1
    · simp at hsome

private lemma findHardInsertion_isThreeFlatBool' {A : List ℕ} {p h : ℕ} {result : List ℕ}
    (hsome : findHardInsertion A p h = some result) :
    isThreeFlatBool result = true := by
  unfold findHardInsertion at hsome
  split at hsome
  · simp at hsome
  · split at hsome
    · next r heq =>
      have hrr := Option.some.inj hsome
      rw [← hrr]
      exact tryHardInsertion_isThreeFlatBool' heq
    · exact findHardInsertion_isThreeFlatBool' hsome
termination_by p + A.length + 1 - h

private lemma tryEasyInsertion_isThreeFlatBool' {A : List ℕ} {p : ℕ} {result : List ℕ}
    (hsome : tryEasyInsertion A p = some result) :
    isThreeFlatBool result = true := by
  simp only [tryEasyInsertion] at hsome
  split at hsome
  · next hcond =>
    have heq := Option.some.inj hsome.symm
    rw [heq]
    simp only [Bool.and_eq_true] at hcond
    exact hcond.1
  · simp at hsome

-- Note: performInsertion_always_succeeds is proved later in this file (L3519+).
-- The early declaration was removed because it is unused and its full proof
-- depends on helper lemmas that appear later in the file.
/-- `performInsertion` preserves 3-flatness. Early declaration for use in labeled scaffold. -/
private theorem performInsertion_preserves_flat' (A : List ℕ) (p : ℕ) (hflat : IsThreeFlat A) :
    IsThreeFlat (performInsertion A p) := by
  unfold performInsertion
  split
  · next result heq =>
    exact isThreeFlatBool_implies' result (findHardInsertion_isThreeFlatBool' heq)
  · split
    · next result heq =>
      exact isThreeFlatBool_implies' result (tryEasyInsertion_isThreeFlatBool' heq)
    · exact hflat

private lemma tryHardInsertion_length_eq {A : List ℕ} {p h : ℕ} {r : List ℕ}
    (hr : tryHardInsertion A p h = some r) : r.length = A.length + 1 := by
  simp only [tryHardInsertion] at hr
  split at hr
  · simp at hr
  · split at hr
    · have heq := Option.some.inj hr
      rw [← heq]
      simp [List.length_insertIdx, List.length_map, List.length_zipIdx]
      omega
    · simp at hr

private lemma findHardInsertion_length_eq {A : List ℕ} {p h : ℕ} {r : List ℕ}
    (hr : findHardInsertion A p h = some r) : r.length = A.length + 1 := by
  unfold findHardInsertion at hr
  split at hr
  · simp at hr
  · split at hr
    · next result heq =>
      have := Option.some.inj hr
      rw [← this]
      exact tryHardInsertion_length_eq heq
    · exact findHardInsertion_length_eq hr
termination_by p + A.length + 1 - h

private lemma tryEasyInsertion_length_eq {A : List ℕ} {p : ℕ} {r : List ℕ}
    (hr : tryEasyInsertion A p = some r) : r.length = A.length + 1 := by
  simp only [tryEasyInsertion] at hr
  split at hr
  · have heq := Option.some.inj hr
    rw [← heq]
    simp [List.length_insertIdx]
    exact (List.IsPrefix.sublist (List.takeWhile_prefix _)).length_le
  · simp at hr

private lemma performInsertion_length_ge (A : List ℕ) (p : ℕ) :
    (performInsertion A p).length ≥ A.length := by
  unfold performInsertion
  split
  · next r hr =>
    -- Hard insertion: findHardInsertion returns result of tryHardInsertion via insertIdx
    suffices r.length = A.length + 1 by omega
    exact findHardInsertion_length_eq hr
  · split
    · next r hr =>
      -- Easy insertion: result is List.insertIdx A pos (3*p), length = A.length + 1
      suffices r.length = A.length + 1 by omega
      exact tryEasyInsertion_length_eq hr
    · -- Fallback: same list
      omega

/-! LABELED MULTIPLES SCAFFOLD — substance of Andrews–Dhar Lemma 3.4 -/

inductive InsertionKind : Type
  | easy
  | hard
  deriving DecidableEq, Repr

/-- A natural number annotated with its insertion-provenance.
    `origin = none` ⇔ the part is in the residue core (never inserted).
    `origin = some (p, .easy)` ⇔ inserted by an easy step of size `p`.
    `origin = some (p, .hard)` ⇔ inserted by a hard step of size `p`. -/
structure Labeled : Type where
  value  : ℕ
  origin : Option (ℕ × InsertionKind) := none
  deriving DecidableEq, Repr

namespace Labeled

@[simp] def forget : List Labeled → List ℕ := List.map (·.value)

def embed (A : List ℕ) : List Labeled := A.map (fun n => ⟨n, none⟩)

@[simp] lemma forget_embed (A : List ℕ) : forget (embed A) = A := by
  simp only [forget, embed, List.map_map, Function.comp_def]
  exact List.map_id A

@[simp] lemma length_embed (A : List ℕ) : (embed A).length = A.length := by
  simp [embed]

@[simp] lemma length_forget (A : List Labeled) : (forget A).length = A.length := by
  simp [forget]

lemma embed_no_label (A : List ℕ) (x : Labeled) (hx : x ∈ embed A) :
    x.origin = none := by
  simp [embed, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx; rfl

/-! Scaffolding helper lemmas (namespace `Hints`). -/

namespace Hints

/-! ### `forget` normal forms. -/

@[simp] lemma forget_eraseIdx (A : List Labeled) (i : ℕ) :
    forget (A.eraseIdx i) = (forget A).eraseIdx i := by
  simp [forget, List.eraseIdx_map]

@[simp] lemma forget_insertIdx (A : List Labeled) (i : ℕ) (x : Labeled) :
    forget (A.insertIdx i x) = (forget A).insertIdx i x.value := by
  simp [forget, List.map_insertIdx]

@[simp] lemma forget_takeWhile_value_ge (A : List Labeled) (k : ℕ) :
    forget (A.takeWhile (·.value ≥ k)) = (forget A).takeWhile (· ≥ k) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    simp only [forget, List.takeWhile, List.map_cons]
    split
    · simp [forget] at ih ⊢; exact ih
    · simp

/-! ### Length helpers. -/

lemma length_insertIdx_le {α : Type*} (xs : List α) (i : ℕ) (a : α) (hi : i ≤ xs.length) :
    (xs.insertIdx i a).length = xs.length + 1 := by
  simp [List.length_insertIdx, hi]

/-! ### `origin` transport through `insertIdx`. -/

lemma origin_insertIdx_of_lt (A : List Labeled) (pos i : ℕ) (x : Labeled)

    (hi : i < (A.insertIdx pos x).length)
    (hpre : i < A.length)
    (hlt : i < pos) :
    ((A.insertIdx pos x)[i]'hi).origin = (A[i]'hpre).origin := by
  rw [List.getElem_insertIdx]
  simp [hlt]

lemma origin_insertIdx_at (A : List Labeled) (pos : ℕ) (x : Labeled)

    (hi : pos < (A.insertIdx pos x).length) :
    ((A.insertIdx pos x)[pos]'hi).origin = x.origin := by
  rw [List.getElem_insertIdx]
  simp

lemma origin_insertIdx_of_gt (A : List Labeled) (pos i : ℕ) (x : Labeled)

    (hi : i < (A.insertIdx pos x).length)
    (hpre : i - 1 < A.length)
    (hgt : pos < i) :
    ((A.insertIdx pos x)[i]'hi).origin = (A[i - 1]'hpre).origin := by
  rw [List.getElem_insertIdx]
  simp [show ¬(i < pos) from by omega, show ¬(i = pos) from by omega]

/-! ### One-way FR preservation under the easy-insert guard. -/

lemma easyInsert_preserves_FR_before
    (xs : List ℕ) (p pos i : ℕ)
    (hpos_def : pos = (xs.takeWhile (· ≥ 3 * p)).length)

    (hflat_ins : isThreeFlatBool (xs.insertIdx pos (3 * p)) = true)
    (hFR_pos : isFlatRemovableBool (xs.insertIdx pos (3 * p)) pos = true)
    (hi : i < xs.length)
    (hlt : i < pos)
    (hFR_i : isFlatRemovableBool xs i = true) :
    isFlatRemovableBool (xs.insertIdx pos (3 * p)) i = true := by
  have hpos_le : pos ≤ xs.length := by
    have := (xs.takeWhile_prefix (· ≥ 3 * p)).length_le; omega
  have hlen_ins : (xs.insertIdx pos (3 * p)).length = xs.length + 1 := by
    simp [List.length_insertIdx, hpos_le]
  unfold isFlatRemovableBool at hFR_i ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hFR_i ⊢
  obtain ⟨⟨_, hmod⟩, hflat_erase⟩ := hFR_i
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hlen_ins]; omega
  · rw [getElem!_pos (xs.insertIdx pos (3 * p)) i (by rw [hlen_ins]; omega)]
    rw [List.getElem_insertIdx]
    simp [show i < pos from hlt]
    rw [← getElem!_pos xs i hi]
    exact hmod
  · -- Need: isThreeFlatBool ((xs.insertIdx pos (3*p)).eraseIdx i) = true
    -- Strategy: unfold and prove each component using hflat_ins and gap conditions
    set L := xs.insertIdx pos (3 * p) with hL_def
    have hi_lt_L : i < L.length := by rw [hL_def, hlen_ins]; omega
    have hflat_L := isThreeFlatBool_implies' L hflat_ins
    obtain ⟨⟨hpw_L, hpos_L⟩, hgaps_L, hlast_L⟩ := hflat_L
    -- First establish the gap condition across position i in L
    have hgap_across : ∀ (h1 : 0 < i) (h2 : i + 1 < L.length),
        L[i-1]'(by omega) - L[i+1]'h2 < 3 := by
      intro h1 h2
      have him1_lt_pos : i - 1 < pos := by omega
      have hLim1 : L[i-1]'(by omega) = xs[i-1]'(by omega) := by
        simp only [L, List.getElem_insertIdx, show i - 1 < pos from him1_lt_pos]; simp
      by_cases hip1 : i + 1 < pos
      · have hLip1 : L[i+1]'h2 = xs[i+1]'(by omega) := by
          simp only [L, List.getElem_insertIdx, show i + 1 < pos from hip1]; simp
        rw [hLim1, hLip1]
        have hflat_e := isThreeFlatBool_implies' _ hflat_erase
        obtain ⟨_, hgaps_e, _⟩ := hflat_e
        have hlen_e : (xs.eraseIdx i).length = xs.length - 1 := by
          simp [List.length_eraseIdx, show i < xs.length from hi]
        have hgap_e := hgaps_e (i - 1) (by rw [hlen_e]; omega)
        have he_im1 : (xs.eraseIdx i)[i-1]'(by rw [hlen_e]; omega) = xs[i-1]'(by omega) := by
          rw [List.getElem_eraseIdx]; simp [show i - 1 < i from by omega]
        have he_i : (xs.eraseIdx i)[(i-1)+1]'(by rw [hlen_e]; omega) = xs[i+1]'(by omega) := by
          rw [List.getElem_eraseIdx]
          simp [show ¬((i-1)+1 < i) from by omega]
          congr 1; omega
        rw [he_im1, he_i] at hgap_e
        exact hgap_e
      · -- i + 1 = pos
        have hip1_eq : i + 1 = pos := by omega
        have hLip1 : L[i+1]'h2 = 3 * p := by
          simp only [L, List.getElem_insertIdx, show ¬(i + 1 < pos) from by omega]
          simp [hip1_eq]
        rw [hLim1, hLip1]
        by_cases hpos_end : pos < xs.length
        · -- xs[pos] < 3*p from takeWhile property
          have hxs_pos_lt : xs[pos]'hpos_end < 3 * p := by
            have hsuff : ∀ (A : List ℕ) (q : ℕ)
                (h : (A.takeWhile (· ≥ 3*q)).length < A.length),
                A[(A.takeWhile (· ≥ 3*q)).length]'h < 3 * q := by
              intro A q h
              induction A with
              | nil => simp at h
              | cons a t ih =>
                simp only [List.takeWhile_cons]
                split
                · next hge =>
                  simp only [List.length_cons, List.getElem_cons_succ]
                  exact ih (by simp [hge] at h; omega)
                · next hlt_pred =>
                  simp only [List.length_nil, List.getElem_cons_zero]
                  simp [decide_eq_true_eq] at hlt_pred; omega
            exact hpos_def ▸ hsuff xs p (hpos_def ▸ hpos_end)
          -- Gap from eraseIdx
          have hflat_e := isThreeFlatBool_implies' _ hflat_erase
          obtain ⟨_, hgaps_e, _⟩ := hflat_e
          have hlen_e : (xs.eraseIdx i).length = xs.length - 1 := by
            simp [List.length_eraseIdx, show i < xs.length from hi]
          have hgap_e := hgaps_e (i - 1) (by rw [hlen_e]; omega)
          have he_im1 : (xs.eraseIdx i)[i-1]'(by rw [hlen_e]; omega) = xs[i-1]'(by omega) := by
            rw [List.getElem_eraseIdx]; simp [show i - 1 < i from by omega]
          have he_i : (xs.eraseIdx i)[(i-1)+1]'(by rw [hlen_e]; omega) = xs[i+1]'(by omega) := by
            rw [List.getElem_eraseIdx]
            simp [show ¬((i-1)+1 < i) from by omega]
            congr 1; omega
          rw [he_im1, he_i] at hgap_e
          have helem_eq : xs[i+1]'(by omega) = xs[pos]'hpos_end := by congr 1
          rw [helem_eq] at hgap_e
          omega
        · -- pos = xs.length: last element of xs.eraseIdx i is xs[i-1] < 3
          have hpos_eq : pos = xs.length := by omega
          have hflat_e := isThreeFlatBool_implies' _ hflat_erase
          obtain ⟨_, _, hlast_e⟩ := hflat_e
          have hlen_e : (xs.eraseIdx i).length = xs.length - 1 := by
            simp [List.length_eraseIdx, show i < xs.length from hi]
          have hne : xs.eraseIdx i ≠ [] := by
            intro h; have hlen0 : (xs.eraseIdx i).length = 0 := by rw [h]; rfl
            rw [hlen_e] at hlen0; omega
          have hlast_val := hlast_e hne
          have hlast_elem : (xs.eraseIdx i).getLast hne = xs[i-1]'(by omega) := by
            rw [List.getLast_eq_getElem, List.getElem_eraseIdx]
            simp [show (xs.eraseIdx i).length - 1 < i from by rw [hlen_e]; omega]
            congr 1; rw [hlen_e]; omega
          rw [hlast_elem] at hlast_val; omega
    -- Now prove isThreeFlatBool (L.eraseIdx i) by unfolding
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    have hlen_Le : (L.eraseIdx i).length = L.length - 1 := by
      rw [List.length_eraseIdx]; simp [show i < L.length from hi_lt_L]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact hpw_L.sublist (List.eraseIdx_sublist L i)
    · intro x hx; exact hpos_L x (List.mem_of_mem_eraseIdx hx)
    · intro k hk
      rw [hlen_Le] at hk
      rw [getElem!_pos _ k (by rw [hlen_Le]; omega)]
      rw [getElem!_pos _ (k+1) (by rw [hlen_Le]; omega)]
      rw [List.getElem_eraseIdx (h := by rw [hlen_Le]; omega)]
      rw [List.getElem_eraseIdx (h := by rw [hlen_Le]; omega)]
      by_cases hki : k < i
      · simp [hki]
        by_cases hk1i : k + 1 < i
        · simp [hk1i]; exact hgaps_L k (by omega)
        · simp [show ¬(k + 1 < i) from hk1i]
          have hk_eq : k = i - 1 := by omega
          subst hk_eq
          have hi1 : i + 1 < L.length := by omega
          have h_goal := hgap_across (by omega : 0 < i) hi1
          rw [show L[i - 1 + 1 + 1]'(by omega) = L[i + 1]'hi1 from by congr 1; omega]
          exact h_goal
      · simp [show ¬(k < i) from hki, show ¬(k + 1 < i) from by omega]
        exact hgaps_L (k + 1) (by omega)
    · by_cases hemp : L.eraseIdx i = []
      · simp [hemp]
      · rw [List.getLast?_eq_some_getLast hemp]
        simp only [decide_eq_true_eq]
        -- i + 1 < L.length (since i < xs.length and L.length = xs.length + 1)
        -- so erasing i doesn't remove the last element
        have hi_not_last : ¬(i + 1 = L.length) := by omega
        rw [List.getLast_eq_getElem, List.getElem_eraseIdx]
        have hge : ¬((L.eraseIdx i).length - 1 < i) := by rw [hlen_Le]; omega
        simp [hge]
        have hL_ne : L ≠ [] := by intro h; simp [h] at hi_lt_L
        have hlast_L_val := hlast_L hL_ne
        rw [List.getLast_eq_getElem] at hlast_L_val
        convert hlast_L_val using 2
        rw [hlen_Le]; omega

lemma easyInsert_preserves_FR_after
    (xs : List ℕ) (p pos i : ℕ)
    (hpos_def : pos = (xs.takeWhile (· ≥ 3 * p)).length)
    (hflat_xs : isThreeFlatBool xs = true)
    (hflat_ins : isThreeFlatBool (xs.insertIdx pos (3 * p)) = true)

    (hi : i < xs.length)
    (hgt : pos ≤ i)
    (hFR_i : isFlatRemovableBool xs i = true) :
    isFlatRemovableBool (xs.insertIdx pos (3 * p)) (i + 1) = true := by
  have hpos_le : pos ≤ xs.length := by
    have := (xs.takeWhile_prefix (· ≥ 3 * p)).length_le; omega
  have hlen_ins : (xs.insertIdx pos (3 * p)).length = xs.length + 1 := by
    simp [List.length_insertIdx, hpos_le]
  set L := xs.insertIdx pos (3 * p) with hL_def
  have hi_lt_L : i + 1 < L.length := by rw [hL_def, hlen_ins]; omega
  have hflat_L := isThreeFlatBool_implies' L hflat_ins
  obtain ⟨⟨hpw_L, hpos_L⟩, hgaps_L, hlast_L⟩ := hflat_L
  unfold isFlatRemovableBool at hFR_i ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hFR_i ⊢
  obtain ⟨⟨_, hmod⟩, hflat_erase⟩ := hFR_i
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hlen_ins]; omega
  · rw [getElem!_pos L (i + 1) hi_lt_L]
    rw [show L[i + 1] = xs[i]'hi from by
      simp only [L, List.getElem_insertIdx, show ¬(i + 1 < pos) from by omega,
                 show ¬(i + 1 = pos) from by omega, dite_false, show i + 1 - 1 = i from by omega]]
    rw [← getElem!_pos xs i hi]
    exact hmod
  · have hflat_e := isThreeFlatBool_implies' _ hflat_erase
    obtain ⟨⟨hpw_e, hpos_e⟩, hgaps_e, hlast_e⟩ := hflat_e
    have hAe_len : (xs.eraseIdx i).length = xs.length - 1 := by
      rw [List.length_eraseIdx]; simp [show i < xs.length from hi]
    have hL_gt (j : ℕ) (hj_gt : pos < j) (hj_lt : j < L.length) :
        L[j]'hj_lt = xs[j - 1]'(by omega) := by
      simp only [L, List.getElem_insertIdx, show ¬(j < pos) from by omega,
                 show ¬(j = pos) from by omega, dite_false]
    have hL_at_pos (hpos_lt : pos < L.length) : L[pos]'hpos_lt = 3 * p := by
      simp only [L, List.getElem_insertIdx, show ¬(pos < pos) from Nat.lt_irrefl pos, dite_false]
      simp
    have hgap_across : ∀ (h1 : 0 < i + 1) (h2 : i + 2 < L.length),
        L[i]'(by omega) - L[i+2]'h2 < 3 := by
      intro h1 h2
      by_cases hi_eq_pos : i = pos
      · exfalso
        have hpos_lt_xs : pos < xs.length := by omega
        have hgap_at_pos : L[pos]'(by omega) - L[pos + 1]'(by omega) < 3 :=
          hgaps_L pos (by omega)
        have hL_pos_val : L[pos]'(by omega) = 3 * p := hL_at_pos (by omega)
        have hL_pos1_val : L[pos + 1]'(by omega) = xs[pos]'hpos_lt_xs := by
          have h := hL_gt (pos + 1) (by omega) (by omega)
          simp only [show pos + 1 - 1 = pos from by omega] at h; exact h
        rw [hL_pos_val, hL_pos1_val] at hgap_at_pos
        have hxs_pos_mod : xs[pos]'hpos_lt_xs % 3 = 0 := by
          have heq : xs[i]'hi = xs[pos]'hpos_lt_xs := by congr 1
          rw [← heq, ← getElem!_pos xs i hi]; exact hmod
        have hxs_pos_lt_3p : xs[pos]'hpos_lt_xs < 3 * p := by
          have htw_len : (xs.takeWhile (· ≥ 3 * p)).length = pos := hpos_def.symm
          have hnotge : ∀ (A : List ℕ) (q : ℕ) (k : ℕ) (hk : k < A.length),
              (A.takeWhile (· ≥ q)).length = k → A[k]'hk < q := by
            intro A q k hk hlen
            induction A generalizing k with
            | nil => simp at hk
            | cons a t ih =>
              simp only [List.takeWhile_cons] at hlen
              split at hlen
              · next hge =>
                  cases k with
                  | zero => simp at hlen
                  | succ k' =>
                    simp at hlen hk
                    exact ih k' (by omega) (by omega)
              · next hlt_pred =>
                  simp only [List.length_nil] at hlen
                  subst hlen
                  simp only [List.getElem_cons_zero]
                  simp only [decide_eq_true_eq, not_le] at hlt_pred
                  exact hlt_pred
          exact hnotge xs (3 * p) pos hpos_lt_xs htw_len
        have h3p_ge : 3 * p ≥ xs[pos]'hpos_lt_xs := by
          have hpw := List.pairwise_iff_getElem.mp hpw_L
          have := hpw pos (pos + 1) (by omega) (by omega) (by omega)
          rw [hL_pos_val, hL_pos1_val] at this; exact this
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hxs_pos_mod
        omega
      · have hi_gt : i > pos := by omega
        have hL_i : L[i]'(by omega) = xs[i - 1]'(by omega) := hL_gt i hi_gt (by omega)
        have hL_i2 : L[i + 2]'h2 = xs[i + 1]'(by omega) := by
          have := hL_gt (i + 2) (by omega) h2
          simp only [show i + 2 - 1 = i + 1 from by omega] at this; exact this
        rw [hL_i, hL_i2]
        have hgap_e := hgaps_e (i - 1) (by rw [hAe_len]; omega)
        have he_im1 : (xs.eraseIdx i)[i - 1]'(by rw [hAe_len]; omega) = xs[i - 1]'(by omega) := by
          rw [List.getElem_eraseIdx]; simp [show i - 1 < i from by omega]
        have he_i : (xs.eraseIdx i)[(i - 1) + 1]'(by rw [hAe_len]; omega) = xs[i + 1]'(by omega) := by
          rw [List.getElem_eraseIdx]
          simp [show ¬((i - 1) + 1 < i) from by omega]
          congr 1; omega
        rw [he_im1, he_i] at hgap_e; exact hgap_e
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    have hlen_Le : (L.eraseIdx (i + 1)).length = L.length - 1 := by
      rw [List.length_eraseIdx]; simp [show i + 1 < L.length from hi_lt_L]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact hpw_L.sublist (List.eraseIdx_sublist L (i + 1))
    · intro x hx; exact hpos_L x (List.mem_of_mem_eraseIdx hx)
    · intro k hk
      rw [hlen_Le] at hk
      rw [getElem!_pos _ k (by rw [hlen_Le]; omega)]
      rw [getElem!_pos _ (k + 1) (by rw [hlen_Le]; omega)]
      rw [List.getElem_eraseIdx (h := by rw [hlen_Le]; omega)]
      rw [List.getElem_eraseIdx (h := by rw [hlen_Le]; omega)]
      by_cases hki : k < i + 1
      · simp [hki]
        by_cases hk1i : k + 1 < i + 1
        · simp [show k < i from by omega]
          exact hgaps_L k (by omega)
        · simp [show ¬(k < i) from by omega]
          have hk_eq : k = i := by omega
          subst hk_eq
          exact hgap_across (by omega) (by omega)
      · simp [show ¬(k < i + 1) from hki, show ¬(k < i) from by omega]
        exact hgaps_L (k + 1) (by omega)
    · by_cases hemp : L.eraseIdx (i + 1) = []
      · simp [hemp]
      · rw [List.getLast?_eq_some_getLast hemp]
        simp only [decide_eq_true_eq]
        have hL_ne : L ≠ [] := by intro h; simp [h] at hi_lt_L
        have hlast_L_val := hlast_L hL_ne
        rw [List.getLast_eq_getElem] at hlast_L_val
        rw [List.getLast_eq_getElem, List.getElem_eraseIdx]
        by_cases hi_last : i + 2 = L.length
        · -- i+1 is last index of L; derive contradiction
          exfalso
          have hLi1_val : L[i + 1]'hi_lt_L = xs[i]'hi := by
            have := hL_gt (i + 1) (by omega) hi_lt_L
            simp only [show i + 1 - 1 = i from by omega] at this; exact this
          have hLi1_lt3 : L[i + 1]'hi_lt_L < 3 := by
            convert hlast_L_val using 2; omega
          rw [hLi1_val] at hLi1_lt3
          have hflat_xs_prop := isThreeFlatBool_implies' xs hflat_xs
          obtain ⟨⟨_, hpos_xs⟩, _, _⟩ := hflat_xs_prop
          have hxsi_pos : 0 < xs[i]'hi := hpos_xs (xs[i]'hi) (List.getElem_mem hi)
          have hxsi_mod : xs[i]'hi % 3 = 0 := by
            rw [getElem!_pos xs i hi] at hmod; exact hmod
          omega
        · -- i+1 is not last element of L
          have hcond : ¬((L.eraseIdx (i + 1)).length - 1 < i + 1) := by
            rw [hlen_Le]; omega
          simp [hcond]
          convert hlast_L_val using 2
          rw [hlen_Le]; omega

/-! ### Bridge from the `Prop`-side `IsThreeFlat` to the `Bool`-side -/

lemma isThreeFlatBool_of_IsThreeFlat {xs : List ℕ} (h : IsThreeFlat xs) :
    isThreeFlatBool xs = true := by
  obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := h
  unfold isThreeFlatBool isPositivePartitionBool
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hpw, ?_⟩, ?_⟩, ?_⟩
  · intro x hx; exact hpos x hx
  · intro i hi
    rw [getElem!_pos xs i (by omega), getElem!_pos xs (i+1) (by omega)]
    exact hgaps i (by omega)
  · cases hle : xs.getLast? with
    | none => simp
    | some x =>
      simp only [decide_eq_true_eq]
      have hne : xs ≠ [] := by
        intro h; simp [h] at hle
      rw [List.getLast?_eq_some_getLast hne] at hle
      exact Option.some.inj hle ▸ hlast hne

end Hints

/-! ## Labeled insertion operations -/

def tryHardInsertionLabeled (A : List Labeled) (p h : ℕ) : Option (List Labeled) :=
  if h ≥ p ∨ h > A.length then none
  else
    let newPart : Labeled := ⟨3 * (p - h), some (p, .hard)⟩
    let raised : List Labeled :=
      A.zipIdx.map (fun (x, j) =>
        if j < h then { x with value := x.value + 3 } else x)
    let result := List.insertIdx raised h newPart
    if isThreeFlatBool (forget result) && !(isFlatRemovableBool (forget result) h)
    then some result
    else none

def findHardInsertionLabeled (A : List Labeled) (p : ℕ) (h : ℕ := 0) :
    Option (List Labeled) :=
  if h ≥ p ∨ h > A.length then none
  else
    match tryHardInsertionLabeled A p h with
    | some r => some r
    | none   => findHardInsertionLabeled A p (h + 1)
termination_by p + A.length + 1 - h

def tryEasyInsertionLabeled (A : List Labeled) (p : ℕ) : Option (List Labeled) :=
  let newPart : Labeled := ⟨3 * p, some (p, .easy)⟩
  let pos := (A.takeWhile (·.value ≥ 3 * p)).length
  let result := List.insertIdx A pos newPart
  if isThreeFlatBool (forget result) && isFlatRemovableBool (forget result) pos
  then some result
  else none

def performInsertionLabeled (A : List Labeled) (p : ℕ) : List Labeled :=
  match findHardInsertionLabeled A p with
  | some r => r
  | none =>
    match tryEasyInsertionLabeled A p with
    | some r => r
    | none   => A

def processInsertionsLabeled : List ℕ → List Labeled → List Labeled
  | [],        A => A
  | p :: rest, A => processInsertionsLabeled rest (performInsertionLabeled A p)

/-! ## Forget commutation: insertion side (5 routine sorries) -/

lemma forget_tryHardInsertionLabeled (A : List Labeled) (p h : ℕ) :
    (tryHardInsertionLabeled A p h).map forget = tryHardInsertion (forget A) p h := by
  unfold tryHardInsertionLabeled tryHardInsertion
  simp only [length_forget]
  split
  · simp
  · next hne =>
    have key : forget (List.insertIdx
        (A.zipIdx.map (fun (x, j) => if j < h then { x with value := x.value + 3 } else x))
        h ⟨3 * (p - h), some (p, .hard)⟩) =
      List.insertIdx ((forget A).zipIdx.map (fun (x, j) => if j < h then x + 3 else x)) h (3 * (p - h)) := by
      simp only [forget, List.map_insertIdx, List.map_map, List.zipIdx_map]
      congr 1
      congr 1
      funext ⟨x, j⟩
      simp only [Function.comp, Prod.map, id]
      split <;> rfl
    simp only [show forget = List.map (·.value) from rfl] at key
    rw [show (Labeled.forget) = List.map (·.value) from rfl]
    simp only [key]
    split <;> simp [key]

lemma forget_tryEasyInsertionLabeled (A : List Labeled) (p : ℕ) :
    (tryEasyInsertionLabeled A p).map forget = tryEasyInsertion (forget A) p := by
  unfold tryEasyInsertionLabeled tryEasyInsertion
  simp only [forget, List.map_insertIdx, List.takeWhile_map, Function.comp_def, List.length_map]
  split
  · simp only [Option.map_some, List.map_insertIdx]
  · simp only [Option.map_none]

lemma forget_findHardInsertionLabeled (A : List Labeled) (p h : ℕ) :
    (findHardInsertionLabeled A p h).map forget = findHardInsertion (forget A) p h := by
  unfold findHardInsertionLabeled findHardInsertion
  simp only [length_forget]
  split
  · simp
  · next hguard =>
    have htry := forget_tryHardInsertionLabeled A p h
    cases htryL : tryHardInsertionLabeled A p h with
    | none =>
      simp only [htryL] at htry
      simp only [Option.map] at htry
      simp only [htry.symm]
      exact forget_findHardInsertionLabeled A p (h + 1)
    | some r =>
      simp only [htryL] at htry
      simp only [Option.map] at htry ⊢
      rw [htry.symm]
termination_by p + A.length + 1 - h

@[simp]
lemma forget_performInsertionLabeled (A : List Labeled) (p : ℕ) :
    forget (performInsertionLabeled A p) = performInsertion (forget A) p := by
  unfold performInsertionLabeled performInsertion
  have hfind := forget_findHardInsertionLabeled A p 0
  cases hfL : findHardInsertionLabeled A p with
  | some r =>
    simp only [hfL, Option.map] at hfind
    rw [hfind.symm]
  | none =>
    simp only [hfL, Option.map] at hfind
    rw [hfind.symm]
    have heasy := forget_tryEasyInsertionLabeled A p
    cases heL : tryEasyInsertionLabeled A p with
    | some r =>
      simp only [heL, Option.map] at heasy
      rw [heasy.symm]
    | none =>
      simp only [heL, Option.map] at heasy
      rw [heasy.symm]

@[simp]
lemma forget_processInsertionsLabeled (ν : List ℕ) (A : List Labeled) :
    forget (processInsertionsLabeled ν A) = processInsertions ν (forget A) := by
  induction ν generalizing A with
  | nil => rfl
  | cons p rest ih =>
    simp only [processInsertionsLabeled, processInsertions]
    rw [ih, forget_performInsertionLabeled]

/-! ## Core/easy gap invariant (non-circular boundary-seam support) -/
private def CoreEasyGap (B : List Labeled) : Prop :=
  ∀ (a b : ℕ), a < b → ∀ (ha : a < B.length) (hb : b < B.length),
    (B[a]'ha).origin = none →
    (B[b]'hb).origin = none →
    (∀ (k : ℕ) (hk : k < B.length), a < k → k < b →
      (B[k]'hk).origin.map Prod.snd = some InsertionKind.easy) →
    (B[a]'ha).value < (B[b]'hb).value + 3

private lemma CoreEasyGap.of_clean {B : List Labeled}
    (hclean : ∀ x ∈ B, x.origin = none)
    (hflat : IsThreeFlat (forget B)) :
    CoreEasyGap B := by
  intro a b hab ha hb hca hcb hbet
  rcases Nat.lt_or_ge (a + 1) b with hlt | hge
  · exfalso
    have hk := hbet (a + 1) (by omega) (by omega) hlt
    have hnone : (B[a + 1]'(by omega)).origin = none :=
      hclean _ (List.getElem_mem _)
    rw [hnone] at hk
    simp at hk
  · have hbeq : b = a + 1 := by omega
    subst hbeq
    have hgap := hflat.2.1 a (by rw [length_forget]; exact hb)
    simp only [forget, List.getElem_map] at hgap
    omega

private lemma tryEasyInsertionLabeled_preserves_CoreEasyGap
    {A r : List Labeled} {p : ℕ}
    (htry : tryEasyInsertionLabeled A p = some r)
    (hA : CoreEasyGap A) :
    CoreEasyGap r := by
  unfold tryEasyInsertionLabeled at htry
  simp only at htry
  split at htry
  · have hres := Option.some.inj htry
    set newPart : Labeled := ⟨3 * p, some (p, InsertionKind.easy)⟩ with hnp
    set pos := (A.takeWhile (·.value ≥ 3 * p)).length with hpos
    have hpos_le : pos ≤ A.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    subst hres
    have hlen : (A.insertIdx pos newPart).length = A.length + 1 := by
      rw [List.length_insertIdx]; simp [hpos_le]
    have getlt : ∀ (k : ℕ) (hkA : k < A.length) (hk : k < pos),
        (A.insertIdx pos newPart)[k]'(by rw [hlen]; omega) = A[k]'hkA := by
      intro k hkA hk
      rw [List.getElem_insertIdx]; simp [hk]
    have getgt : ∀ (k : ℕ) (hkA : k - 1 < A.length)
        (hkr : k < (A.insertIdx pos newPart).length) (hk : pos < k),
        (A.insertIdx pos newPart)[k]'hkr = A[k - 1]'hkA := by
      intro k hkA hkr hk
      rw [List.getElem_insertIdx]; simp [show ¬ k < pos by omega, show k ≠ pos by omega]
    intro a b hab ha hb hca hcb hbet
    have hane : a ≠ pos := by
      rintro rfl; rw [List.getElem_insertIdx_self (by omega)] at hca; simp [hnp] at hca
    have hbne : b ≠ pos := by
      rintro rfl; rw [List.getElem_insertIdx_self (by omega)] at hcb; simp [hnp] at hcb
    rcases Nat.lt_or_ge b pos with hbpos | hbpos
    · -- both < pos
      have hapos : a < pos := by omega
      rw [getlt a (by omega) hapos] at hca ⊢
      rw [getlt b (by omega) hbpos] at hcb ⊢
      refine hA a b hab (by omega) (by omega) hca hcb ?_
      intro k hkA hak hkb
      have hkr : k < (A.insertIdx pos newPart).length := by rw [hlen]; omega
      have hh := hbet k hkr hak hkb
      rwa [getlt k hkA (by omega)] at hh
    · rcases Nat.lt_or_ge a pos with hapos | hapos
      · -- straddle: a < pos < b, map to A-window (a, b-1)
        have hbgt : pos < b := by omega
        rw [getlt a (by omega) hapos] at hca ⊢
        rw [getgt b (by omega) hb hbgt] at hcb ⊢
        refine hA a (b - 1) (by omega) (by omega) (by omega) hca hcb ?_
        intro k hkA hak hkb
        rcases Nat.lt_or_ge k pos with hkp | hkp
        · have hkr : k < (A.insertIdx pos newPart).length := by rw [hlen]; omega
          have hh := hbet k hkr hak (by omega)
          rwa [getlt k hkA hkp] at hh
        · have hkr : k + 1 < (A.insertIdx pos newPart).length := by rw [hlen]; omega
          have hh := hbet (k + 1) hkr (by omega) (by omega)
          rw [getgt (k + 1) (by omega) hkr (by omega)] at hh
          simpa using hh
      · -- both > pos
        have hapos' : pos < a := by omega
        have hbgt : pos < b := by omega
        rw [getgt a (by omega) ha hapos'] at hca ⊢
        rw [getgt b (by omega) hb hbgt] at hcb ⊢
        refine hA (a - 1) (b - 1) (by omega) (by omega) (by omega) hca hcb ?_
        intro k hkA hak hkb
        have hkr : k + 1 < (A.insertIdx pos newPart).length := by rw [hlen]; omega
        have hh := hbet (k + 1) hkr (by omega) (by omega)
        rw [getgt (k + 1) (by omega) hkr (by omega)] at hh
        simpa using hh
  · exact absurd htry (by simp)

private lemma tryHardInsertionLabeled_preserves_CoreEasyGap
    {A r : List Labeled} {q h : ℕ}
    (htry : tryHardInsertionLabeled A q h = some r)
    (hA : CoreEasyGap A) :
    CoreEasyGap r := by
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf had
  push_neg at hf
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩ with hnp
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry
  have hlen_raised : raised.length = A.length := by simp [hraised]
  have hh_le : h ≤ A.length := hf.2
  subst hres
  have hlen : (raised.insertIdx h newPart).length = A.length + 1 := by
    rw [List.length_insertIdx]; simp [hlen_raised, hh_le]
  have getlt : ∀ (k : ℕ) (hkA : k < A.length) (hk : k < h),
      ((raised.insertIdx h newPart)[k]'(by rw [hlen]; omega)).value
          = (A[k]'hkA).value + 3 ∧
        ((raised.insertIdx h newPart)[k]'(by rw [hlen]; omega)).origin
          = (A[k]'hkA).origin := by
    intro k hkA hk
    refine ⟨?_, ?_⟩ <;>
      · rw [List.getElem_insertIdx]
        simp [hk, hraised, List.getElem_map, List.getElem_zipIdx]
  have getgt : ∀ (k : ℕ) (hkA : k - 1 < A.length)
      (hkr : k < (raised.insertIdx h newPart).length) (hk : h < k),
      (raised.insertIdx h newPart)[k]'hkr = A[k - 1]'hkA := by
    intro k hkA hkr hk
    rw [List.getElem_insertIdx]
    simp [show ¬ k < h by omega, show k ≠ h by omega, hraised,
      List.getElem_map, List.getElem_zipIdx, show ¬ k - 1 < h by omega]
  intro a b hab ha hb hca hcb hbet
  have hane : a ≠ h := by
    rintro rfl; rw [List.getElem_insertIdx_self (by omega)] at hca; simp [hnp] at hca
  have hbne : b ≠ h := by
    rintro rfl; rw [List.getElem_insertIdx_self (by omega)] at hcb; simp [hnp] at hcb
  rcases Nat.lt_or_ge b h with hbh | hbh
  · -- both < h
    have hah : a < h := by omega
    obtain ⟨hva, hoa⟩ := getlt a (by omega) hah
    obtain ⟨hvb, hob⟩ := getlt b (by omega) hbh
    rw [hoa] at hca
    rw [hob] at hcb
    rw [hva, hvb]
    refine Nat.add_lt_add_iff_right.mpr (hA a b hab (by omega) (by omega) hca hcb ?_)
    intro k hkA hak hkb
    have hkr : k < (raised.insertIdx h newPart).length := by rw [hlen]; omega
    have hb2 := hbet k hkr hak (by omega)
    obtain ⟨_, hok⟩ := getlt k hkA (by omega)
    rwa [hok] at hb2
  · rcases Nat.lt_or_ge a h with hah | hah
    · -- straddle a < h < b: the hard sits between → contradiction
      exfalso
      have hbh' : h < b := by omega
      have hkr : h < (raised.insertIdx h newPart).length := by rw [hlen]; omega
      have hmid := hbet h hkr hah hbh'
      rw [List.getElem_insertIdx_self (by omega)] at hmid
      simp [hnp] at hmid
    · -- both > h
      have hah' : h < a := by omega
      have hbh' : h < b := by omega
      rw [getgt a (by omega) ha hah'] at hca ⊢
      rw [getgt b (by omega) hb hbh'] at hcb ⊢
      refine hA (a - 1) (b - 1) (by omega) (by omega) (by omega) hca hcb ?_
      intro k hkA hak hkb
      have hkr : k + 1 < (raised.insertIdx h newPart).length := by rw [hlen]; omega
      have hb2 := hbet (k + 1) hkr (by omega) (by omega)
      rw [getgt (k + 1) (by omega) hkr (by omega)] at hb2
      simpa using hb2

private lemma findHardInsertionLabeled_preserves_CoreEasyGap
    {A : List Labeled} {p h₀ : ℕ} {result : List Labeled}
    (hfind : findHardInsertionLabeled A p h₀ = some result)
    (hA : CoreEasyGap A) :
    CoreEasyGap result := by
  have hmotive : ∀ h, findHardInsertionLabeled A p h = some result → CoreEasyGap result :=
    findHardInsertionLabeled.induct A p
      (motive := fun h => findHardInsertionLabeled A p h = some result → CoreEasyGap result)
      (fun h hguard hfind => by simp [findHardInsertionLabeled, hguard] at hfind)
      (fun h hguard r htry hfind => by
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry] at hfind
        subst hfind
        exact tryHardInsertionLabeled_preserves_CoreEasyGap htry hA)
      (fun h hguard htry_fail ih hfind => by
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry_fail] at hfind
        exact ih hfind)
  exact hmotive h₀ hfind

private lemma performInsertionLabeled_preserves_CoreEasyGap
    {A : List Labeled} {p : ℕ} (hA : CoreEasyGap A) :
    CoreEasyGap (performInsertionLabeled A p) := by
  unfold performInsertionLabeled
  cases hfind : findHardInsertionLabeled A p with
  | some r =>
    simp only [hfind]
    exact findHardInsertionLabeled_preserves_CoreEasyGap hfind hA
  | none =>
    simp only [hfind]
    cases heasy : tryEasyInsertionLabeled A p with
    | some r =>
      simp only [heasy]
      exact tryEasyInsertionLabeled_preserves_CoreEasyGap heasy hA
    | none => simp only [heasy]; exact hA

private lemma processInsertionsLabeled_CoreEasyGap
    (ν : List ℕ) (A : List Labeled) (hA : CoreEasyGap A) :
    CoreEasyGap (processInsertionsLabeled ν A) := by
  induction ν generalizing A with
  | nil => simpa [processInsertionsLabeled] using hA
  | cons p rest ih =>
    simp only [processInsertionsLabeled]
    exact ih _ (performInsertionLabeled_preserves_CoreEasyGap hA)

/-! ## Labeled forward (deletion) algorithm -/

def scanFromSmallestLabeled (fuel : ℕ) (A : List Labeled) (idx : ℕ) (rec : List ℕ) :
    List Labeled × List ℕ :=
  match fuel with
  | 0 => (A, rec)
  | fuel' + 1 =>
    if idx ≥ A.length then (A, rec)
    else
      let actualIdx := A.length - 1 - idx
      if isFlatRemovableBool (forget A) actualIdx then
        let val := (forget A)[actualIdx]!
        scanFromSmallestLabeled fuel' (A.eraseIdx actualIdx) idx (rec ++ [val / 3])
      else
        scanFromSmallestLabeled fuel' A (idx + 1) rec

def scanFromLargestLabeled (fuel : ℕ) (A : List Labeled) (idx : ℕ) (rec : List ℕ) :
    List Labeled × List ℕ :=
  match fuel with
  | 0 => (A, rec)
  | fuel' + 1 =>
    if idx ≥ A.length then (A, rec)
    else
      let val := (forget A)[idx]!
      if val % 3 == 0 && val > 0 then
        let a := val / 3
        let A' := A.eraseIdx idx
        let A'' := A'.zipIdx.map (fun (x, j) =>
          if j < idx then { x with value := x.value - 3 } else x)
        scanFromLargestLabeled fuel' A'' idx (rec ++ [a + idx])
      else
        scanFromLargestLabeled fuel' A (idx + 1) rec

/-! Commutation of labeled scans with unlabeled scans.  Routine fuel -/

lemma forget_scanFromSmallestLabeled (fuel : ℕ) (A : List Labeled) (idx : ℕ) (rec : List ℕ) :
    let (A', rec') := scanFromSmallestLabeled fuel A idx rec
    forget A' = (scanFromSmallest fuel (forget A) idx rec).1 ∧
    rec' = (scanFromSmallest fuel (forget A) idx rec).2 := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromSmallestLabeled, scanFromSmallest]
  | succ fuel' ih =>
    simp only [scanFromSmallestLabeled, scanFromSmallest, length_forget]
    split
    · simp
    · next h =>
      split
      · next h2 =>
        have herase : forget (A.eraseIdx (A.length - 1 - idx)) =
            (forget A).eraseIdx (A.length - 1 - idx) := by
          simp [forget, List.eraseIdx_map]
        have key := ih (A.eraseIdx (A.length - 1 - idx)) idx
          (rec ++ [(forget A)[A.length - 1 - idx]! / 3])
        rw [herase] at key
        exact key
      · next h2 =>
        exact ih A (idx + 1) rec

lemma forget_scanFromLargestLabeled (fuel : ℕ) (A : List Labeled) (idx : ℕ) (rec : List ℕ) :
    let (A', rec') := scanFromLargestLabeled fuel A idx rec
    forget A' = (scanFromLargest fuel (forget A) idx rec).1 ∧
    rec' = (scanFromLargest fuel (forget A) idx rec).2 := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromLargestLabeled, scanFromLargest]
  | succ fuel' ih =>
    simp only [scanFromLargestLabeled, scanFromLargest, length_forget]
    split
    · simp
    · next h =>
      split
      · next h2 =>
        have herase : forget (A.eraseIdx idx) =
            (forget A).eraseIdx idx := by
          simp [forget, List.eraseIdx_map]
        have hmap : forget
            ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
              if j < idx then { x with value := x.value - 3 } else x)) =
            ((forget A).eraseIdx idx).zipIdx.map (fun (x, j) =>
              if j < idx then x - 3 else x) := by
          simp only [forget, List.map_map, Function.comp_def]
          conv_rhs => rw [show (List.map (·.value) A).eraseIdx idx =
              List.map (·.value) (A.eraseIdx idx) from by rw [List.eraseIdx_map]]
          rw [List.zipIdx_map]
          simp only [List.map_map, Function.comp_def, Prod.map, id]
          congr 1
          funext ⟨x, j⟩
          simp only []
          split <;> rfl
        have key := ih ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
          if j < idx then { x with value := x.value - 3 } else x)) idx
          (rec ++ [(forget A)[idx]! / 3 + idx])
        rw [hmap] at key
        exact key
      · exact ih A (idx + 1) rec

/-! DIRECTION R — right-inverse / compatibility: -/

/-- Sizes of all easy-labeled parts in a labeled list (in list order). -/
def easyLabels (A : List Labeled) : List ℕ :=
  A.filterMap (fun x => match x.origin with
                       | some (p, .easy) => some p
                       | _               => none)

/-- Sizes of all hard-labeled parts in a labeled list (in list order). -/
def hardLabels (A : List Labeled) : List ℕ :=
  A.filterMap (fun x => match x.origin with
                       | some (p, .hard) => some p
                       | _               => none)

/-- Easy labels as an order-forgetting multiset. -/
def easyMS (A : List Labeled) : Multiset ℕ :=
  (easyLabels A : Multiset ℕ)

/-- Hard labels as an order-forgetting multiset. -/
def hardMS (A : List Labeled) : Multiset ℕ :=
  (hardLabels A : Multiset ℕ)

/-- All insertion labels as a multiset. -/
def labelMS (A : List Labeled) : Multiset ℕ :=
  easyMS A + hardMS A

/-- Record list as a multiset. -/
def recMS (rec : List ℕ) : Multiset ℕ :=
  (rec : Multiset ℕ)

/-- Multiset of records added between two record states. -/
def deltaRecMS (recAfter recBefore : List ℕ) : Multiset ℕ :=
  recMS recAfter - recMS recBefore

lemma list_perm_iff_coe_multiset_eq (xs ys : List ℕ) :
    (xs : Multiset ℕ) = (ys : Multiset ℕ) ↔ xs.Perm ys :=
  Multiset.coe_eq_coe

lemma list_perm_of_coe_multiset_eq {xs ys : List ℕ}
    (h : (xs : Multiset ℕ) = (ys : Multiset ℕ)) :
    xs.Perm ys :=
  (list_perm_iff_coe_multiset_eq xs ys).mp h

lemma coe_multiset_eq_of_list_perm {xs ys : List ℕ} (h : xs.Perm ys) :
    (xs : Multiset ℕ) = (ys : Multiset ℕ) :=
  (list_perm_iff_coe_multiset_eq xs ys).mpr h

@[simp] lemma recMS_append (xs ys : List ℕ) :
    recMS (xs ++ ys) = recMS xs + recMS ys := by
  simp [recMS]

@[simp] lemma labelMS_eq (A : List Labeled) :
    labelMS A = easyMS A + hardMS A := rfl

@[simp] lemma deltaRecMS_eq_diff (recAfter recBefore : List ℕ) :
    deltaRecMS recAfter recBefore = ((recAfter.diff recBefore : List ℕ) : Multiset ℕ) := rfl

private lemma deltaRecMS_append_singleton_of_prefix {rec0 rec : List ℕ} (x : ℕ)
    (hprefix : ∃ added, rec = rec0 ++ added) :
    deltaRecMS (rec ++ [x]) rec0 = deltaRecMS rec rec0 + ({x} : Multiset ℕ) := by
  obtain ⟨added, rfl⟩ := hprefix
  unfold deltaRecMS recMS
  rw [show rec0 ++ added ++ [x] = rec0 ++ (added ++ [x]) by simp [List.append_assoc]]
  rw [← Multiset.coe_add rec0 (added ++ [x])]
  rw [add_comm (↑rec0 : Multiset ℕ) (↑(added ++ [x]) : Multiset ℕ)]
  rw [Multiset.add_sub_cancel_right]
  rw [← Multiset.coe_add rec0 added]
  rw [add_comm (↑rec0 : Multiset ℕ) (↑added : Multiset ℕ)]
  rw [Multiset.add_sub_cancel_right]
  rw [← Multiset.coe_add added [x]]
  simp

lemma list_diff_perm_of_deltaRecMS_eq_hardMS {recAfter recBefore : List ℕ}
    {A : List Labeled} (h : deltaRecMS recAfter recBefore = hardMS A) :
    (List.diff recAfter recBefore).Perm (hardLabels A) := by
  apply list_perm_of_coe_multiset_eq
  simpa [hardMS] using h

/- **Invariant R-A** — paper `Thm2WithProof.tex` L539–569.

For every `(p, .easy)` label produced by `processInsertionsLabeled`, when
S2 reaches the corresponding part it is flat-removable and S2 records `p`.
As a multiset statement: the S2-record list equals the easy-label multiset.

PROOF GUIDE (paper): a labeled easy part remains flat-removable through
every later insertion (paper L545–559 case-split on whether later
insertions touch the witness gaps).  Apply `no_raise_labels` (already
closed in the file) for hard-followers, and direct gap arithmetic for
easy-followers of size ≤ p.

DO NOT recurse into S2's internal scan structure.  Induct on `ν` and
apply `performInsertionLabeled` step-by-step, maintaining the invariant
that all easy labels currently in the list are flat-removable. -/

/-- Helper: erasing index i from a 3-flat list preserves 3-flatness when the gap
condition across position i is satisfied (neighbors differ by < 3). -/
private lemma isThreeFlatBool_eraseIdx_of_threeFlat_and_gap
    (L : List ℕ) (i : ℕ) (hi : i < L.length)
    (hflat : isThreeFlatBool L = true)
    (hgap : ∀ (h1 : 0 < i) (h2 : i + 1 < L.length),
      L[i-1]'(by omega) - L[i+1]'h2 < 3)
    (hlast : i + 1 = L.length → 0 < i → L[i-1]'(by omega) < 3) :
    isThreeFlatBool (L.eraseIdx i) = true := by
  unfold isThreeFlatBool isPositivePartitionBool at hflat ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hflat ⊢
  obtain ⟨⟨⟨hpw, hall⟩, hgaps⟩, hlast_orig⟩ := hflat
  have hlen_erase : (L.eraseIdx i).length = L.length - 1 := by
    rw [List.length_eraseIdx]; simp [show i < L.length from hi]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact hpw.sublist (List.eraseIdx_sublist L i)
  · intro x hx; exact hall x (List.mem_of_mem_eraseIdx hx)
  · intro k hk
    rw [hlen_erase] at hk
    rw [getElem!_pos _ k (by rw [hlen_erase]; omega)]
    rw [getElem!_pos _ (k+1) (by rw [hlen_erase]; omega)]
    rw [List.getElem_eraseIdx (h := by rw [hlen_erase]; omega)]
    rw [List.getElem_eraseIdx (h := by rw [hlen_erase]; omega)]
    by_cases hki : k < i
    · simp [hki]
      by_cases hk1i : k + 1 < i
      · simp [hk1i]
        have := hgaps k (by omega)
        rwa [getElem!_pos L k (by omega), getElem!_pos L (k+1) (by omega)] at this
      · simp [show ¬(k + 1 < i) from hk1i]
        have hk_eq : k = i - 1 := by omega
        subst hk_eq
        have hi1 : i + 1 < L.length := by omega
        have h_goal := hgap (by omega : 0 < i) hi1
        rw [show L[i - 1 + 1 + 1]'(by omega) = L[i + 1]'hi1 from by congr 1; omega]
        exact h_goal
    · simp [show ¬(k < i) from hki, show ¬(k + 1 < i) from by omega]
      have := hgaps (k + 1) (by omega)
      rwa [getElem!_pos L (k+1) (by omega), getElem!_pos L (k+2) (by omega)] at this
  · by_cases hemp : L.eraseIdx i = []
    · simp [hemp]
    · rw [List.getLast?_eq_some_getLast hemp]
      simp only [decide_eq_true_eq]
      by_cases hlast_pos : i + 1 = L.length
      · have hi_pos : 0 < i := by
          by_contra h0; push_neg at h0
          have hi0 : i = 0 := by omega
          subst hi0
          have hlen0 : (L.eraseIdx 0).length = 0 := by rw [hlen_erase]; omega
          exact hemp (List.eq_nil_of_length_eq_zero hlen0)
        have hlast_val := hlast hlast_pos hi_pos
        rw [List.getLast_eq_getElem, List.getElem_eraseIdx]
        have hlt : (L.eraseIdx i).length - 1 < i := by rw [hlen_erase]; omega
        simp [hlt]
        convert hlast_val using 2
        rw [hlen_erase]; omega
      · rw [List.getLast_eq_getElem, List.getElem_eraseIdx]
        have hge : ¬((L.eraseIdx i).length - 1 < i) := by rw [hlen_erase]; omega
        simp [hge]
        have hL_ne : L ≠ [] := by intro h; simp [h] at hi
        have hlast_L := hlast_orig
        rw [List.getLast?_eq_some_getLast hL_ne] at hlast_L
        simp [decide_eq_true_eq] at hlast_L
        rw [List.getLast_eq_getElem] at hlast_L
        convert hlast_L using 2
        rw [hlen_erase]; omega

/-- Helper for easy insertion case: if `tryEasyInsertionLabeled A p = some result`,
then all easy-labeled parts in `result` are FR.
The new part is FR by the guard. Existing easy parts remain FR because
inserting into a 3-flat list at position pos preserves FR for elements
whose gap structure is unaffected. -/
private lemma easyInsertion_preserves_easy_FR
    (A : List Labeled) (p : ℕ) (result : List Labeled)
    (hA_flat : IsThreeFlat (forget A))
    (h_inv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget A) i = true)
    (heasy : tryEasyInsertionLabeled A p = some result) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget result) i = true := by
  unfold tryEasyInsertionLabeled at heasy
  set newPart : Labeled := ⟨3 * p, some (p, .easy)⟩ with hnewPart_def
  set pos := (A.takeWhile (·.value ≥ 3 * p)).length with hpos_def
  set raw := List.insertIdx A pos newPart with hraw_def
  have hpos_le : pos ≤ A.length := by
    exact List.IsPrefix.length_le (List.takeWhile_prefix _)
  -- S1 (~12 lines): extract the guard from `heasy` and `result = raw`.
  have hguard_and : isThreeFlatBool (forget raw) = true ∧
                    isFlatRemovableBool (forget raw) pos = true ∧
                    result = raw := by
    simp only [tryEasyInsertionLabeled] at heasy
    split_ifs at heasy with h
    · simp only [Bool.and_eq_true] at h
      exact ⟨h.1, h.2, (Option.some.inj heasy).symm⟩
  obtain ⟨hflat_raw, hFR_raw_pos, hresult⟩ := hguard_and
  subst result
  have hforget_raw : forget raw = (forget A).insertIdx pos (3 * p) := by
    simp [hraw_def, hnewPart_def, forget, List.map_insertIdx]
  have hpos_le_unl : pos ≤ (forget A).length := by
    simpa [forget] using hpos_le
  have hflat_A_bool : isThreeFlatBool (forget A) = true :=
    Hints.isThreeFlatBool_of_IsThreeFlat hA_flat
  intro i hi hkind
  have hraw_len : raw.length = A.length + 1 := by
    simpa [hraw_def] using Hints.length_insertIdx_le A pos newPart hpos_le
  rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
  · -- Branch 1: i < pos. Use easyInsert_preserves_FR_before.
    have hpre : i < A.length := by omega
    have h_origin_eq : (raw[i]'hi).origin = (A[i]'hpre).origin :=
      Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
    have hkind_pre : (A[i]'hpre).origin.map Prod.snd = some InsertionKind.easy := by
      rw [← h_origin_eq]; exact hkind
    have hFR_A_i : isFlatRemovableBool (forget A) i = true :=
      h_inv i hpre hkind_pre
    have hflat_ins_unl : isThreeFlatBool ((forget A).insertIdx pos (3 * p)) = true := by
      rw [← hforget_raw]; exact hflat_raw
    have hFR_ins_pos_unl : isFlatRemovableBool ((forget A).insertIdx pos (3 * p)) pos = true := by
      rw [← hforget_raw]; exact hFR_raw_pos
    have hi_unl : i < (forget A).length := by simpa [forget] using hpre
    have hpos_def_unl : pos = ((forget A).takeWhile (· ≥ 3 * p)).length := by
      rw [hpos_def, ← Hints.forget_takeWhile_value_ge, forget, List.length_map]
    rw [hforget_raw]
    exact Hints.easyInsert_preserves_FR_before
            (forget A) p pos i hpos_def_unl hflat_ins_unl
            hFR_ins_pos_unl hi_unl hlt hFR_A_i
  · -- Branch 2: i = pos. The inserted easy part's own FR comes from the guard.
    subst i
    exact hforget_raw ▸ hFR_raw_pos
  · -- Branch 3: pos < i. Use easyInsert_preserves_FR_after at i - 1.
    have hpre : i - 1 < A.length := by omega
    have h_origin_eq : (raw[i]'hi).origin = (A[i - 1]'hpre).origin :=
      Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
    have hkind_pre : (A[i - 1]'hpre).origin.map Prod.snd = some InsertionKind.easy := by
      rw [← h_origin_eq]; exact hkind
    have hFR_A_im1 : isFlatRemovableBool (forget A) (i - 1) = true :=
      h_inv (i - 1) hpre hkind_pre
    have hflat_ins_unl : isThreeFlatBool ((forget A).insertIdx pos (3 * p)) = true := by
      rw [← hforget_raw]; exact hflat_raw
    have hFR_ins_pos_unl : isFlatRemovableBool ((forget A).insertIdx pos (3 * p)) pos = true := by
      rw [← hforget_raw]; exact hFR_raw_pos
    have him1_unl : i - 1 < (forget A).length := by simpa [forget] using hpre
    have hpos_def_unl : pos = ((forget A).takeWhile (· ≥ 3 * p)).length := by
      rw [hpos_def, ← Hints.forget_takeWhile_value_ge, forget, List.length_map]
    rw [hforget_raw]
    have hi_form : i = (i - 1) + 1 := by omega
    rw [hi_form]
    exact Hints.easyInsert_preserves_FR_after
            (forget A) p pos (i - 1) hpos_def_unl hflat_A_bool hflat_ins_unl
            him1_unl (by omega) hFR_A_im1

private lemma tryHardInsertion_FR_preservation_at_explicit
    (A : List ℕ) (p h : ℕ) (result : List ℕ)
    (hA_flat : IsThreeFlat A)
    (hr : tryHardInsertion A p h = some result)
    (i : ℕ) (hi : i < A.length)
    (h_fr : isFlatRemovableBool A i = true) :
    isFlatRemovableBool result (if i < h then i else i + 1) = true := by
  -- Bridge to the existing existential helper at h₀ := h.
  -- At success of tryHardInsertion at h, the existential helper's witness
  -- equals (if i < h then i else i+1), but the existential loses the formula.
  -- We re-derive it by unfolding findHardInsertion at h₀ := h and observing
  -- that the success branch is taken.
  have hfind : findHardInsertion A p h = some result := by
    unfold findHardInsertion
    have hguard : ¬(h ≥ p ∨ h > A.length) := by
      -- tryHardInsertion succeeded → guard does not block
      unfold tryHardInsertion at hr
      split at hr
      · simp at hr
      · next h_ng => exact h_ng
    simp only [hguard, ↓reduceIte]
    rw [hr]
  -- We replicate the success-branch proof of `findHardInsertion_FR_preservation_at`
  -- inline.  This is essentially copying lines 898-1248 with `h₀ := h`.
  unfold findHardInsertion at hfind
  split at hfind
  · simp at hfind
  · next hguard =>
    push_neg at hguard
    obtain ⟨hlt_p, hle_len⟩ := hguard
    split at hfind
    · next result0 htry_eq =>
      have hr_eq : result0 = result := Option.some.inj hfind
      simp only [tryHardInsertion] at htry_eq
      split at htry_eq
      · simp at htry_eq
      · split at htry_eq
        · next hcond =>
          have heq := Option.some.inj htry_eq
          set newPart := 3 * (p - h) with hnewPart_def
          set raised := List.map (fun x : ℕ × ℕ => if x.2 < h then x.1 + 3 else x.1) A.zipIdx
            with hraised_def
          set result_def := List.insertIdx raised h newPart with hresult_def_def
          have hraised_len : raised.length = A.length := by simp [raised]
          have hresult_def_len : result_def.length = A.length + 1 := by
            simp only [result_def, List.length_insertIdx]; split <;> omega
          have h_r0_eq : result0 = result_def := heq.symm
          have h_r_eq : result = result_def := by rw [← hr_eq, h_r0_eq]
          have hraised_lt_val (j : ℕ) (hj : j < h) :
              raised[j]'(by omega) = A[j]'(by omega) + 3 := by
            simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
            simp only [Nat.zero_add]; exact if_pos hj
          have hraised_ge_val (j : ℕ) (hj : ¬(j < h)) (hjlen : j < A.length) :
              raised[j]'(by omega) = A[j]'hjlen := by
            simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
            simp only [Nat.zero_add]; exact if_neg hj
          have hresult_before (j : ℕ) (hj : j < h) :
              result_def[j]'(by omega) = A[j]'(by omega) + 3 := by
            simp only [result_def, List.getElem_insertIdx, show j < h from hj]
            exact hraised_lt_val j hj
          have hresult_at : result_def[h]'(by omega) = newPart := by
            simp only [result_def, List.getElem_insertIdx, show ¬(h < h) from Nat.lt_irrefl h]
            simp
          have hresult_after (j : ℕ) (hj : j > h) (hjlen : j < result_def.length) :
              result_def[j]'hjlen = A[j - 1]'(by omega) := by
            simp only [result_def, List.getElem_insertIdx, show ¬(j < h) from by omega,
                       show ¬(j = h) from by omega]
            exact hraised_ge_val (j - 1) (by omega) (by omega)
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨hflat_bool, _hnotFR⟩ := hcond
          have hresult_3flat : IsThreeFlat result_def :=
            isThreeFlatBool_implies' _ hflat_bool
          obtain ⟨hpp, hgaps_res, hlast_res⟩ := hresult_3flat
          obtain ⟨hAp, hgaps_A, hlast_A⟩ := hA_flat
          have hA_pw : A.Pairwise (· ≥ ·) := hAp.1
          have hA_pos : ∀ x ∈ A, 0 < x := hAp.2
          unfold isFlatRemovableBool at h_fr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h_fr
          obtain ⟨⟨_hi_lt, hAi_mod⟩, h_eraseA_flat_bool⟩ := h_fr
          have hAi_dvd : 3 ∣ A[i]'hi := by
            rw [getElem!_pos A i hi] at hAi_mod
            exact Nat.dvd_of_mod_eq_zero hAi_mod
          have h_eraseA_flat : IsThreeFlat (A.eraseIdx i) :=
            isThreeFlatBool_implies' _ h_eraseA_flat_bool
          obtain ⟨_hAep, hgaps_Ae, hlast_Ae⟩ := h_eraseA_flat
          have hAe_len : (A.eraseIdx i).length = A.length - 1 := by
            rw [List.length_eraseIdx]; simp [show i < A.length from hi]
          rw [h_r_eq]
          unfold isFlatRemovableBool
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · split <;> rw [hresult_def_len] <;> omega
          · by_cases hilt : i < h
            · simp only [hilt, if_true]
              rw [getElem!_pos result_def i (by rw [hresult_def_len]; omega)]
              rw [hresult_before i hilt]
              omega
            · simp only [hilt, if_false]
              rw [getElem!_pos result_def (i+1) (by rw [hresult_def_len]; omega)]
              have hi_gt : i + 1 > h := by omega
              rw [hresult_after (i+1) hi_gt (by rw [hresult_def_len]; omega)]
              simp only [Nat.add_sub_cancel]
              omega
          · by_cases hilt : i < h
            · simp only [hilt, if_true]
              apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap result_def i
                (by rw [hresult_def_len]; omega) hflat_bool
              · intro h1 h2
                have hi_minus_1_lt : i - 1 < h := by omega
                rw [hresult_before (i-1) hi_minus_1_lt]
                by_cases hi_plus_1_lt : i + 1 < h
                · rw [hresult_before (i+1) hi_plus_1_lt]
                  have hgap : (A.eraseIdx i)[i-1]'(by rw [hAe_len]; omega) -
                              (A.eraseIdx i)[(i-1)+1]'(by rw [hAe_len]; omega) < 3 :=
                    hgaps_Ae (i-1) (by rw [hAe_len]; omega)
                  have he1 : (A.eraseIdx i)[i-1]'(by rw [hAe_len]; omega) = A[i-1]'(by omega) := by
                    rw [List.getElem_eraseIdx]
                    simp [show i - 1 < i from by omega]
                  have he2 : (A.eraseIdx i)[(i-1)+1]'(by rw [hAe_len]; omega) = A[i+1]'(by omega) := by
                    rw [List.getElem_eraseIdx]
                    simp [show ¬((i-1)+1 < i) from by omega]
                    congr 1 <;> omega
                  rw [he1, he2] at hgap
                  have hi1_lt_A : i + 1 < A.length := by
                    rw [hresult_def_len] at h2; omega
                  omega
                · have hi1_eq : i + 1 = h := by omega
                  have hres_i1 : result_def[i+1]'h2 = newPart := by
                    have : result_def[i+1]'h2 = result_def[h]'(by rw [hresult_def_len]; omega) := by
                      congr 1
                    rw [this]; exact hresult_at
                  rw [hres_i1]
                  have hh0_pos : 0 < h := by omega
                  have hgap_res : result_def[h-1]'(by rw [hresult_def_len]; omega) -
                                  result_def[h-1+1]'(by rw [hresult_def_len]; omega) < 3 :=
                    hgaps_res (h-1) (by rw [hresult_def_len]; omega)
                  have hres_h0m1 : result_def[h-1]'(by rw [hresult_def_len]; omega) =
                                   A[h-1]'(by omega) + 3 :=
                    hresult_before (h-1) (by omega)
                  have hres_h0 : result_def[h-1+1]'(by rw [hresult_def_len]; omega) = newPart := by
                    have : result_def[h-1+1]'(by rw [hresult_def_len]; omega) =
                           result_def[h]'(by rw [hresult_def_len]; omega) := by congr 1 <;> omega
                    rw [this]; exact hresult_at
                  rw [hres_h0m1, hres_h0] at hgap_res
                  have hAh0m1_lt : A[h-1]'(by omega) < newPart := by omega
                  have hAi_eq : A[i]'hi = A[h-1]'(by omega) := by congr 1 <;> omega
                  have hAh0m1_dvd : 3 ∣ A[h-1]'(by omega) := hAi_eq ▸ hAi_dvd
                  have hnewPart_dvd : 3 ∣ newPart := ⟨p - h, rfl⟩
                  have hAh0m1_le : A[h-1]'(by omega) + 3 ≤ newPart := by
                    rcases hAh0m1_dvd with ⟨k, hk⟩
                    rcases hnewPart_dvd with ⟨m, hm⟩
                    rw [hk, hm] at hAh0m1_lt ⊢
                    omega
                  have hgap_A_im1 : A[i-1]'(by omega) - A[i]'hi < 3 := by
                    have := hgaps_A (i-1) (by omega)
                    have heq1 : i - 1 + 1 = i := by omega
                    simp only [heq1] at this
                    exact this
                  have hAim1_ge : A[i-1]'(by omega) ≥ A[i]'hi := by
                    have hpw := List.pairwise_iff_getElem.mp hA_pw
                    exact hpw (i-1) i (by omega) hi (by omega)
                  have hAim1_le : A[i-1]'(by omega) ≤ A[i]'hi + 2 := by omega
                  rw [← hAi_eq] at hAh0m1_le
                  omega
              · intro h1 h2
                rw [hresult_def_len] at h1
                exfalso; omega
            · simp only [hilt, if_false]
              push_neg at hilt
              apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap result_def (i+1)
                (by rw [hresult_def_len]; omega) hflat_bool
              · intro h1 h2
                rw [hresult_def_len] at h2
                have h_idx_eq : (i+1) - 1 = i := by omega
                have hres_im1 : result_def[(i+1)-1]'(by rw [hresult_def_len]; omega) =
                                result_def[i]'(by rw [hresult_def_len]; omega) := by
                  congr 1
                rw [hres_im1]
                by_cases hi_eq_h0 : i = h
                · have hres_i_at_h0 : result_def[i]'(by rw [hresult_def_len]; omega) = newPart := by
                    have : result_def[i]'(by rw [hresult_def_len]; omega) =
                           result_def[h]'(by rw [hresult_def_len]; omega) := by congr 1
                    rw [this]; exact hresult_at
                  rw [hres_i_at_h0]
                  have hres_i2 : result_def[(i+1)+1]'(by rw [hresult_def_len]; omega) =
                                 A[i+1]'(by omega) := by
                    have := hresult_after ((i+1)+1) (by omega) (by rw [hresult_def_len]; omega)
                    have hidx : (i+1)+1 - 1 = i+1 := by omega
                    simp only [hidx] at this
                    exact this
                  rw [hres_i2]
                  have hgap_res : result_def[h]'(by rw [hresult_def_len]; omega) -
                                  result_def[h+1]'(by rw [hresult_def_len]; omega) < 3 :=
                    hgaps_res h (by rw [hresult_def_len]; omega)
                  have hres_h0p1 : result_def[h+1]'(by rw [hresult_def_len]; omega) =
                                   A[h]'(by omega) := by
                    have := hresult_after (h+1) (by omega) (by rw [hresult_def_len]; omega)
                    simp only [show h+1-1 = h from by omega] at this
                    exact this
                  rw [hresult_at, hres_h0p1] at hgap_res
                  have hgap_A_h0 : A[h]'(by omega) - A[h+1]'(by omega) < 3 := by
                    have := hgaps_A h (by omega)
                    exact this
                  have hAi_dvd' : 3 ∣ A[h]'(by omega) := by
                    have : A[i]'hi = A[h]'(by omega) := by congr 1 <;> omega
                    rw [← this]; exact hAi_dvd
                  have hnewPart_dvd : 3 ∣ newPart := ⟨p - h, rfl⟩
                  have hnp_le : newPart ≤ A[h]'(by omega) := by
                    rcases hAi_dvd' with ⟨k, hk⟩
                    rcases hnewPart_dvd with ⟨m, hm⟩
                    rw [hk, hm] at hgap_res ⊢
                    omega
                  have hAi1_eq : A[i+1]'(by omega) = A[h+1]'(by omega) := by
                    congr 1 <;> omega
                  rw [hAi1_eq]
                  omega
                · have hi_gt : i > h := by omega
                  have hres_i_after : result_def[i]'(by rw [hresult_def_len]; omega) =
                                      A[i-1]'(by omega) := hresult_after i hi_gt _
                  rw [hres_i_after]
                  have hres_i2 : result_def[(i+1)+1]'(by rw [hresult_def_len]; omega) =
                                 A[i+1]'(by omega) := by
                    have := hresult_after ((i+1)+1) (by omega) (by rw [hresult_def_len]; omega)
                    simp only [show (i+1)+1-1 = i+1 from by omega] at this
                    exact this
                  rw [hres_i2]
                  have hgap : (A.eraseIdx i)[i-1]'(by rw [hAe_len]; omega) -
                              (A.eraseIdx i)[(i-1)+1]'(by rw [hAe_len]; omega) < 3 :=
                    hgaps_Ae (i-1) (by rw [hAe_len]; omega)
                  have he1 : (A.eraseIdx i)[i-1]'(by rw [hAe_len]; omega) = A[i-1]'(by omega) := by
                    rw [List.getElem_eraseIdx]
                    simp [show i - 1 < i from by omega]
                  have he2 : (A.eraseIdx i)[(i-1)+1]'(by rw [hAe_len]; omega) = A[i+1]'(by omega) := by
                    rw [List.getElem_eraseIdx]
                    simp [show ¬((i-1)+1 < i) from by omega]
                    congr 1 <;> omega
                  rw [he1, he2] at hgap
                  omega
              · intro h1 h2
                rw [hresult_def_len] at h1
                have h_i_eq : i = A.length - 1 := by omega
                have hres_im1 : result_def[(i+1)-1]'(by rw [hresult_def_len]; omega) =
                                result_def[i]'(by rw [hresult_def_len]; omega) := by
                  congr 1
                rw [hres_im1]
                by_cases hi_eq_h0 : i = h
                · have hres_i_at_h0 : result_def[i]'(by rw [hresult_def_len]; omega) = newPart := by
                    have : result_def[i]'(by rw [hresult_def_len]; omega) =
                           result_def[h]'(by rw [hresult_def_len]; omega) := by congr 1
                    rw [this]; exact hresult_at
                  rw [hres_i_at_h0]
                  have hAi_dvd' : 3 ∣ A[h]'(by omega) := by
                    have : A[i]'hi = A[h]'(by omega) := by congr 1 <;> omega
                    rw [← this]; exact hAi_dvd
                  have hnp_dvd : 3 ∣ newPart := ⟨p - h, rfl⟩
                  have hgap_res : result_def[h]'(by rw [hresult_def_len]; omega) -
                                  result_def[h+1]'(by rw [hresult_def_len]; omega) < 3 :=
                    hgaps_res h (by rw [hresult_def_len]; omega)
                  have hres_h0p1 : result_def[h+1]'(by rw [hresult_def_len]; omega) =
                                   A[h]'(by omega) := by
                    have := hresult_after (h+1) (by omega) (by rw [hresult_def_len]; omega)
                    simp only [show h+1-1 = h from by omega] at this
                    exact this
                  rw [hresult_at, hres_h0p1] at hgap_res
                  have hAh0_eq : A[h]'(by omega) = A[A.length - 1]'(by omega) := by
                    congr 1 <;> omega
                  rw [hAh0_eq] at hgap_res
                  have hA_last : A[A.length - 1]'(by omega) < 3 := by
                    have hne : A ≠ [] := by
                      intro h'; rw [h'] at hi; simp at hi
                    have := hlast_A hne
                    rw [List.getLast_eq_getElem] at this
                    exact this
                  have hnp_le : newPart ≤ A[A.length - 1]'(by omega) := by
                    rcases hAi_dvd' with ⟨k, hk⟩
                    rw [hAh0_eq] at hk
                    rcases hnp_dvd with ⟨m, hm⟩
                    rw [hk, hm] at hgap_res ⊢
                    omega
                  omega
                · have hi_gt : i > h := by omega
                  have hres_i_after : result_def[i]'(by rw [hresult_def_len]; omega) =
                                      A[i-1]'(by omega) := hresult_after i hi_gt _
                  rw [hres_i_after]
                  have hAe_ne : A.eraseIdx i ≠ [] := by
                    intro hempty
                    have : (A.eraseIdx i).length = 0 := by rw [hempty]; simp
                    rw [hAe_len] at this
                    omega
                  have hlast_Ae_val := hlast_Ae hAe_ne
                  rw [List.getLast_eq_getElem] at hlast_Ae_val
                  have hl2_lt_i : A.length - 2 < i := by omega
                  have hidx_eq : (A.eraseIdx i).length - 1 = A.length - 2 := by
                    rw [hAe_len]; omega
                  have hkey : (A.eraseIdx i)[(A.eraseIdx i).length - 1]'
                                (by rw [hAe_len]; omega) = A[i-1]'(by omega) := by
                    have h1' : (A.eraseIdx i)[(A.eraseIdx i).length - 1]'
                                (by rw [hAe_len]; omega) =
                              (A.eraseIdx i)[A.length - 2]'(by rw [hAe_len]; omega) := by
                      congr 1
                    rw [h1', List.getElem_eraseIdx]
                    simp [show A.length - 2 < i from hl2_lt_i]
                    congr 1 <;> omega
                  rw [hkey] at hlast_Ae_val
                  exact hlast_Ae_val
        · simp at htry_eq
    · -- recursive case: contradicts hr (tryHardInsertion succeeded)
      next htry_none =>
        -- htry_none : tryHardInsertion A p h = none, but hr says it = some result
        rw [hr] at htry_none
        simp at htry_none

/-- At the success of `tryHardInsertionLabeled A p h`, an easy-labeled position
in `result` corresponds to an easy-labeled position in `A` via the index shift
`i = if j < h then j else j + 1`. -/
private lemma tryHardInsertionLabeled_easy_pos_pullback
    (A : List Labeled) (p h : ℕ) (result : List Labeled)
    (hr : tryHardInsertionLabeled A p h = some result)
    (i : ℕ) (hi : i < result.length)
    (h_easy : (result[i]'hi).origin.map Prod.snd = some InsertionKind.easy) :
    ∃ (j : ℕ) (hj : j < A.length),
      i = (if j < h then j else j + 1) ∧
      (A[j]'hj).origin = (result[i]'hi).origin := by
  unfold tryHardInsertionLabeled at hr
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at hr
  split_ifs at hr with hfail hadm
  push_neg at hfail
  obtain ⟨hhp, hhA⟩ := hfail
  have hres : (List.map (fun x : Labeled × ℕ =>
                if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1) A.zipIdx).insertIdx
              h { value := 3 * (p - h), origin := some (p, InsertionKind.hard) } = result :=
    Option.some.inj hr
  set raised : List Labeled :=
    List.map (fun x : Labeled × ℕ => if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1) A.zipIdx
    with hraised_def
  set newPart : Labeled := ⟨3 * (p - h), some (p, InsertionKind.hard)⟩ with hnewPart_def
  have hlen_raised : raised.length = A.length := by simp [hraised_def]
  have hlen_result : result.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx]; simp [hlen_raised, hhA]
  have hi_le : i ≤ A.length := by rw [hlen_result] at hi; omega
  have hraised_get : ∀ k (hk : k < A.length),
      raised[k]'(hlen_raised.symm ▸ hk) =
        if k < h then { value := (A[k]'hk).value + 3, origin := (A[k]'hk).origin }
        else (A[k]'hk) := by
    intro k hk
    simp [hraised_def, List.getElem_map, List.getElem_zipIdx]
  have hi_ins : i < (raised.insertIdx h newPart).length := by
    rw [List.length_insertIdx]; simp [hlen_raised, hhA]; omega
  have keyAll : result[i]'hi = (raised.insertIdx h newPart)[i]'hi_ins := by
    congr 1
    exact hres.symm
  rw [keyAll]
  rw [List.getElem_insertIdx]
  by_cases h1 : i < h
  · rw [dif_pos h1]
    have hi_A : i < A.length := by omega
    refine ⟨i, hi_A, ?_, ?_⟩
    · rw [if_pos h1]
    · rw [hraised_get i hi_A, if_pos h1]
  · rw [dif_neg h1]
    by_cases h2 : i = h
    · rw [dif_pos h2]
      exfalso
      rw [keyAll, List.getElem_insertIdx, dif_neg h1, dif_pos h2] at h_easy
      simp [hnewPart_def] at h_easy
    · rw [dif_neg h2]
      have hi_pos : i ≥ 1 := by omega
      have hi_minus : i - 1 < A.length := by omega
      have hi_minus_ge : ¬ (i - 1 < h) := by omega
      refine ⟨i - 1, hi_minus, ?_, ?_⟩
      · rw [if_neg hi_minus_ge]
        omega
      · rw [hraised_get (i - 1) hi_minus, if_neg hi_minus_ge]

/-- Generalized version of `hardInsertion_preserves_easy_FR` parameterized by
the recursion start height `h₀`.  Proceeds by induction on the termination
measure.  The `h₀ := 0` instance gives `hardInsertion_preserves_easy_FR`. -/
private lemma findHardInsertionLabeled_preserves_easy_FR_aux
    (A : List Labeled) (p h₀ : ℕ) (result : List Labeled)
    (hA_flat : IsThreeFlat (forget A))
    (h_inv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget A) i = true)
    (hhard : findHardInsertionLabeled A p h₀ = some result) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget result) i = true := by
  unfold findHardInsertionLabeled at hhard
  split at hhard
  · simp at hhard
  · split at hhard
    · -- success at h₀: tryHardInsertionLabeled A p h₀ = some r; result = r
      next r htry =>
        intro i hi h_easy
        have hresult_eq : r = result := Option.some.inj hhard
        -- Bridge: tryHardInsertion (forget A) p h₀ = some (forget result)
        have hforget : tryHardInsertion (forget A) p h₀ = some (forget result) := by
          have hcomm := forget_tryHardInsertionLabeled A p h₀
          rw [htry, hresult_eq] at hcomm
          -- hcomm : (some result).map forget = tryHardInsertion (forget A) p h₀
          simp only [Option.map_some] at hcomm
          exact hcomm.symm
        -- Pullback easy origin
        have hi_in_r : i < r.length := by rw [hresult_eq]; exact hi
        have h_easy_r : (r[i]'hi_in_r).origin.map Prod.snd = some InsertionKind.easy := by
          rw [show r[i]'hi_in_r = result[i]'hi from by simp [hresult_eq]]
          exact h_easy
        obtain ⟨j, hj, hi_eq, h_origin⟩ :=
          tryHardInsertionLabeled_easy_pos_pullback A p h₀ r htry i hi_in_r h_easy_r
        -- A[j].origin is easy
        have h_easy_A : (A[j]'hj).origin.map Prod.snd = some InsertionKind.easy := by
          rw [h_origin]; exact h_easy_r
        -- Apply h_inv
        have h_fr_A : isFlatRemovableBool (forget A) j = true :=
          h_inv j hj h_easy_A
        -- Apply explicit helper
        have h_fr_result :
            isFlatRemovableBool (forget result) (if j < h₀ then j else j + 1) = true :=
          tryHardInsertion_FR_preservation_at_explicit (forget A) p h₀ (forget result)
            hA_flat hforget j (by rw [length_forget]; exact hj) h_fr_A
        rw [← hi_eq] at h_fr_result
        exact h_fr_result
    · -- recursive case
      next htry_none =>
        intro i hi h_easy
        exact findHardInsertionLabeled_preserves_easy_FR_aux A p (h₀ + 1) result hA_flat h_inv hhard i hi h_easy
termination_by p + A.length + 1 - h₀

/-- Helper for hard insertion case: if `findHardInsertionLabeled A p = some result`,
then all easy-labeled parts in `result` are FR.
Hard insertion raises positions 0..h-1 by 3 and inserts at h. Existing easy parts
remain FR because: (a) uniform +3 preserves relative gaps, (b) the insertion
doesn't break FR for shifted elements, (c) result is 3-flat by the guard. -/
private lemma hardInsertion_preserves_easy_FR
    (A : List Labeled) (p : ℕ) (result : List Labeled)
    (hA_flat : IsThreeFlat (forget A))
    (h_inv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget A) i = true)
    (hhard : findHardInsertionLabeled A p = some result) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget result) i = true := by
  exact findHardInsertionLabeled_preserves_easy_FR_aux A p 0 result hA_flat h_inv hhard

/-- Helper: `performInsertionLabeled` preserves the flat-removability of all
existing easy-labeled parts. If every easy-labeled part in `A` is FR in
`forget A`, then every easy-labeled part in `performInsertionLabeled A p`
that was already in `A` is FR in `forget (performInsertionLabeled A p)`. -/
private lemma performInsertionLabeled_preserves_easy_FR
    (A : List Labeled) (p : ℕ)
    (hA_flat : IsThreeFlat (forget A))
    (h_inv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget A) i = true) :
    ∀ (i : ℕ) (hi : i < (performInsertionLabeled A p).length),
      ((performInsertionLabeled A p)[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget (performInsertionLabeled A p)) i = true := by
  unfold performInsertionLabeled
  cases hf : findHardInsertionLabeled A p with
  | some r => exact hardInsertion_preserves_easy_FR A p r hA_flat h_inv hf
  | none =>
    cases he : tryEasyInsertionLabeled A p with
    | some r => exact easyInsertion_preserves_easy_FR A p r hA_flat h_inv he
    | none => exact h_inv

/-- All easy-labeled parts in the output of `processInsertionsLabeled` are
flat-removable in `forget` of that output. This is the static (pre-scan) property.

Proof: by induction on ν. At each step, `tryEasyInsertionLabeled` places
a part that is FR by admissibility. Subsequent insertions preserve FR of
existing easy parts because:
- Easy part of size p has value 3p (never modified by subsequent insertions
  of size q ≤ p, since `no_raise_labels` ensures values don't change)
- The gap structure that makes it FR is preserved because subsequent insertions
  happen at positions that don't disrupt the witness gaps. -/
lemma easy_parts_are_flat_removable
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat   : IsThreeFlat (forget A_init))
    (hA_reg    : IsThreeRegular (forget A_init))
    (hA_clean  : ∀ x ∈ A_init, x.origin = none)
    (hν_sort   : ν.Pairwise (· ≥ ·))
    (hν_pos    : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (i : ℕ) (hi : i < labeled.length),
      (labeled[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget labeled) i = true := by
  intro labeled
  -- We prove a stronger inductive statement: for any suffix of ν and any
  -- intermediate state A that is 3-flat and satisfies the invariant,
  -- the result of processInsertionsLabeled satisfies the invariant.
  suffices h_gen : ∀ (ν' : List ℕ) (A : List Labeled),
      IsThreeFlat (forget A) →
      (∀ (i : ℕ) (hi : i < A.length),
        (A[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
          isFlatRemovableBool (forget A) i = true) →
      ∀ (i : ℕ) (hi : i < (processInsertionsLabeled ν' A).length),
        ((processInsertionsLabeled ν' A)[i]'hi).origin.map Prod.snd = some InsertionKind.easy →
          isFlatRemovableBool (forget (processInsertionsLabeled ν' A)) i = true by
    apply h_gen
    · exact hA_flat
    · intro i hi heasy
      have hx := List.getElem_mem hi
      have hclean := hA_clean _ hx
      simp [hclean] at heasy
  intro ν'
  induction ν' with
  | nil =>
    intro A hflat h_inv i hi heasy
    simp only [processInsertionsLabeled] at hi heasy ⊢
    exact h_inv i hi heasy
  | cons p rest ih =>
    intro A hflat h_inv i hi heasy
    simp only [processInsertionsLabeled] at hi heasy ⊢
    have hflat' : IsThreeFlat (forget (performInsertionLabeled A p)) := by
      rw [forget_performInsertionLabeled]
      exact performInsertion_preserves_flat' (forget A) p hflat
    have h_inv' := performInsertionLabeled_preserves_easy_FR A p hflat h_inv
    exact ih (performInsertionLabeled A p) hflat' h_inv' i hi heasy

/- During the dynamic S2 scan of `processInsertionsLabeled ν A_init`,
every part that is flat-removable at the time it is encountered is easy-labeled.

This is the DYNAMIC version of the invariant. It says: at each intermediate
state of the scan, if the part at the current scan position is FR, then
it is easy-labeled. This is stronger than just "easy parts are FR" because
hard parts CAN be FR in the initial list. The dynamic claim holds because:
- The scan goes from bottom (smallest values) upward
- Easy parts are placed at their natural sorted position (small easy parts → low index)
- When an easy part is removed, neighboring hard parts lose their FR status
  (the gap structure changes)
- So at each step, the first FR part from the current scan position is always easy.

Formally: for any intermediate state `(A_mid, rec_mid)` reachable by
`scanFromSmallestLabeled` from the initial labeled list, if
`isFlatRemovableBool (forget A_mid) (A_mid.length - 1 - idx)` is true,
then `A_mid[A_mid.length - 1 - idx]` is easy-labeled. -/

/-- If L is 3-flat, actualIdx < L.length is FR in L, and j < actualIdx is FR in
L.eraseIdx actualIdx, then j is FR in L.
Key: the cross-gap at j is bounded via monotonicity of the weakly decreasing list. -/
private lemma isFlatRemovableBool_transfer_left (L : List ℕ) (j actualIdx : ℕ)
    (hj_lt : j < actualIdx) (hact_lt : actualIdx < L.length)
    (hflat : IsThreeFlat L)
    (h_fr_act : isFlatRemovableBool L actualIdx = true)
    (h_fr_j : isFlatRemovableBool (L.eraseIdx actualIdx) j = true) :
    isFlatRemovableBool L j = true := by
  unfold isFlatRemovableBool at h_fr_act h_fr_j ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h_fr_act h_fr_j ⊢
  obtain ⟨⟨hact_lt', hmod_act⟩, hflat_erase_act⟩ := h_fr_act
  obtain ⟨⟨hj_lt_erase, hmod_j_erase⟩, hflat_double_erase⟩ := h_fr_j
  have hj_lt_L : j < L.length := by omega
  have hlen_erase_act : (L.eraseIdx actualIdx).length = L.length - 1 := by
    simp [List.length_eraseIdx, show actualIdx < L.length from hact_lt]
  have hlen_de : ((L.eraseIdx actualIdx).eraseIdx j).length = L.length - 2 := by
    rw [List.length_eraseIdx, hlen_erase_act]
    simp [show j < L.length - 1 from by omega]; omega
  refine ⟨⟨hj_lt_L, ?_⟩, ?_⟩
  · rw [getElem!_pos (L.eraseIdx actualIdx) j (by omega)] at hmod_j_erase
    have heq_j : (L.eraseIdx actualIdx)[j]'(by omega) = L[j]'hj_lt_L := by
      rw [List.getElem_eraseIdx]; simp [show j < actualIdx from hj_lt]
    rw [heq_j] at hmod_j_erase
    rw [getElem!_pos L j hj_lt_L]; exact hmod_j_erase
  · have hflat_bool : isThreeFlatBool L = true := by
      unfold isThreeFlatBool isPositivePartitionBool
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := hflat
      refine ⟨⟨⟨hpw, ?_⟩, ?_⟩, ?_⟩
      · intro x hx; exact hpos x hx
      · intro i hi
        rw [getElem!_pos L i (by omega), getElem!_pos L (i+1) (by omega)]
        exact hgaps i (by omega)
      · cases hl : L.getLast? with
        | none => simp
        | some x =>
          simp; have hne : L ≠ [] := by intro h; simp [h] at hact_lt
          rw [List.getLast?_eq_some_getLast hne] at hl
          exact Option.some.inj hl ▸ hlast hne
    apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap L j hj_lt_L hflat_bool
    · intro h1 h2
      have hflat_de := isThreeFlatBool_implies' _ hflat_double_erase
      obtain ⟨⟨_, _⟩, hgaps_de, hlast_de⟩ := hflat_de
      have hde_jm1 : ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) =
          L[j-1]'(by omega) := by
        rw [List.getElem_eraseIdx]; simp [show j - 1 < j from by omega]
        rw [List.getElem_eraseIdx]; simp [show j - 1 < actualIdx from by omega]
      by_cases hjp1 : j + 1 < actualIdx
      · have hj_bound : j < ((L.eraseIdx actualIdx).eraseIdx j).length := by rw [hlen_de]; omega
        have hde_j : ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound = L[j+1]'h2 := by
          rw [List.getElem_eraseIdx]; simp
          rw [List.getElem_eraseIdx]; simp [show j + 1 < actualIdx from hjp1]
        have hgap_bound : (j - 1) + 1 < ((L.eraseIdx actualIdx).eraseIdx j).length := by
          rw [hlen_de]; omega
        have hgap_val := hgaps_de (j - 1) hgap_bound
        calc L[j-1]'(by omega) - L[j+1]'h2
            = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
              ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound := by rw [hde_jm1, hde_j]
          _ = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
              ((L.eraseIdx actualIdx).eraseIdx j)[(j-1)+1]'hgap_bound := by
                congr 2; exact (Nat.sub_add_cancel h1).symm
          _ < 3 := hgap_val
      · have hj1_eq : j + 1 = actualIdx := by omega
        by_cases hact_last : actualIdx + 1 < L.length
        · have hj_bound : j < ((L.eraseIdx actualIdx).eraseIdx j).length := by rw [hlen_de]; omega
          have hde_j : ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound = L[actualIdx+1]'(by omega) := by
            rw [List.getElem_eraseIdx]; simp
            rw [List.getElem_eraseIdx]; simp [show ¬(j + 1 < actualIdx) from by omega]
            congr 1; omega
          have hgap_bound : (j - 1) + 1 < ((L.eraseIdx actualIdx).eraseIdx j).length := by
            rw [hlen_de]; omega
          have hgap_val := hgaps_de (j - 1) hgap_bound
          have hineq : L[j-1]'(by omega) - L[actualIdx+1]'(by omega) < 3 := by
            calc L[j-1]'(by omega) - L[actualIdx+1]'(by omega)
                = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
                  ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound := by rw [hde_jm1, hde_j]
              _ = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
                  ((L.eraseIdx actualIdx).eraseIdx j)[(j-1)+1]'hgap_bound := by
                    congr 2; exact (Nat.sub_add_cancel h1).symm
              _ < 3 := hgap_val
          obtain ⟨⟨hpw, _⟩, _, _⟩ := hflat
          have hmono : L[actualIdx]'hact_lt ≥ L[actualIdx+1]'(by omega) :=
            List.pairwise_iff_getElem.mp hpw _ _ hact_lt (by omega) (by omega)
          have hval_eq : L[j+1]'h2 = L[actualIdx]'hact_lt := by congr 1
          have h_ge : L[j+1]'h2 ≥ L[actualIdx+1]'(by omega) := hval_eq ▸ hmono
          exact Nat.lt_of_le_of_lt (Nat.sub_le_sub_left h_ge _) hineq
        · have hne_de : (L.eraseIdx actualIdx).eraseIdx j ≠ [] := by
            intro heq
            have hlen0 : ((L.eraseIdx actualIdx).eraseIdx j).length = 0 := by
              rw [heq]; simp
            rw [hlen_de] at hlen0; omega
          have hlast_val := hlast_de hne_de
          rw [List.getLast_eq_getElem] at hlast_val
          have hlen_de_eq_j : ((L.eraseIdx actualIdx).eraseIdx j).length = j := by
            rw [hlen_de]; omega
          have hget_eq : ((L.eraseIdx actualIdx).eraseIdx j)[((L.eraseIdx actualIdx).eraseIdx j).length - 1] =
              L[j-1]'(by omega) := by
            have hlhs : ((L.eraseIdx actualIdx).eraseIdx j)[((L.eraseIdx actualIdx).eraseIdx j).length - 1] =
                ((L.eraseIdx actualIdx).eraseIdx j)[j - 1]'(by rw [hlen_de]; omega) := by
              congr 1; rw [hlen_de_eq_j]
            rw [hlhs, hde_jm1]
          rw [hget_eq] at hlast_val
          omega
    · intro hlast_eq hipos; omega

/-- If L is 3-flat, actualIdx < L.length is FR in L, and j ≥ actualIdx is FR in
L.eraseIdx actualIdx (corresponding to position j+1 in L), then j+1 is FR in L.
Key: the cross-gap at j+1 is bounded via monotonicity. -/
private lemma isFlatRemovableBool_transfer_right (L : List ℕ) (j actualIdx : ℕ)
    (hj_ge : ¬(j < actualIdx)) (hj_lt : j < L.length - 1) (hact_lt : actualIdx < L.length)
    (hflat : IsThreeFlat L)
    (h_fr_act : isFlatRemovableBool L actualIdx = true)
    (h_fr_j : isFlatRemovableBool (L.eraseIdx actualIdx) j = true) :
    isFlatRemovableBool L (j + 1) = true := by
  unfold isFlatRemovableBool at h_fr_act h_fr_j ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h_fr_act h_fr_j ⊢
  obtain ⟨⟨hact_lt', hmod_act⟩, hflat_erase_act⟩ := h_fr_act
  obtain ⟨⟨hj_lt_erase, hmod_j_erase⟩, hflat_double_erase⟩ := h_fr_j
  have hj1_lt_L : j + 1 < L.length := by omega
  have hlen_erase_act : (L.eraseIdx actualIdx).length = L.length - 1 := by
    simp [List.length_eraseIdx, show actualIdx < L.length from hact_lt]
  have hlen_de : ((L.eraseIdx actualIdx).eraseIdx j).length = L.length - 2 := by
    rw [List.length_eraseIdx, hlen_erase_act]
    simp [show j < L.length - 1 from hj_lt]; omega
  refine ⟨⟨hj1_lt_L, ?_⟩, ?_⟩
  · -- Show L[j+1] % 3 = 0
    rw [getElem!_pos (L.eraseIdx actualIdx) j (by omega)] at hmod_j_erase
    have heq_j : (L.eraseIdx actualIdx)[j]'(by omega) = L[j+1]'hj1_lt_L := by
      rw [List.getElem_eraseIdx]; simp [show ¬(j < actualIdx) from hj_ge]
    rw [heq_j] at hmod_j_erase
    rw [getElem!_pos L (j+1) hj1_lt_L]; exact hmod_j_erase
  · -- Show isThreeFlatBool (L.eraseIdx (j+1)) = true
    have hflat_bool : isThreeFlatBool L = true := by
      unfold isThreeFlatBool isPositivePartitionBool
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := hflat
      refine ⟨⟨⟨hpw, ?_⟩, ?_⟩, ?_⟩
      · intro x hx; exact hpos x hx
      · intro i hi
        rw [getElem!_pos L i (by omega), getElem!_pos L (i+1) (by omega)]
        exact hgaps i (by omega)
      · cases hl : L.getLast? with
        | none => simp
        | some x =>
          simp; have hne : L ≠ [] := by intro h; simp [h] at hact_lt
          rw [List.getLast?_eq_some_getLast hne] at hl
          exact Option.some.inj hl ▸ hlast hne
    apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap L (j+1) hj1_lt_L hflat_bool
    · -- Gap condition: L[j] - L[j+2] < 3
      intro h1 h2
      suffices h : L[j]'(by omega) - L[j+2]'(by omega) < 3 by
        convert h using 2 <;> omega
      have hflat_de := isThreeFlatBool_implies' _ hflat_double_erase
      obtain ⟨⟨_, _⟩, hgaps_de, hlast_de⟩ := hflat_de
      by_cases hj_gt : actualIdx < j
      · -- Case: j > actualIdx
        have hde_jm1 : ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) =
            L[j]'(by omega) := by
          rw [List.getElem_eraseIdx]
          simp [show j - 1 < j from by omega]
          rw [List.getElem_eraseIdx]
          simp [show ¬(j - 1 < actualIdx) from by omega]
          congr 1; omega
        have hj_bound : j < ((L.eraseIdx actualIdx).eraseIdx j).length := by rw [hlen_de]; omega
        have hde_j : ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound = L[j+2]'(by omega) := by
          rw [List.getElem_eraseIdx]
          simp [show ¬(j < j) from by omega]
          rw [List.getElem_eraseIdx]
          simp [show ¬(j + 1 < actualIdx) from by omega]
        have hgap_bound : (j - 1) + 1 < ((L.eraseIdx actualIdx).eraseIdx j).length := by
          rw [hlen_de]; omega
        have hgap_val := hgaps_de (j - 1) hgap_bound
        calc L[j]'(by omega) - L[j+2]'(by omega)
            = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
              ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound := by rw [hde_jm1, hde_j]
          _ = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
              ((L.eraseIdx actualIdx).eraseIdx j)[(j-1)+1]'hgap_bound := by congr 2; omega
          _ < 3 := hgap_val
      · -- Case: j = actualIdx
        have hj_eq : j = actualIdx := by omega
        by_cases hj_pos : j = 0
        · -- j = 0, actualIdx = 0
          subst hj_pos
          have hact0 : actualIdx = 0 := by omega
          subst hact0
          obtain ⟨⟨hpw, hpos⟩, hgaps_L, hlast_L⟩ := hflat
          have hgap12 : L[1]'(by omega) - L[2]'(by omega) < 3 :=
            hgaps_L 1 (by omega)
          have hmod_act' : L[0]'(by omega) % 3 = 0 := by
            rw [getElem!_pos L 0 (by omega)] at hmod_act; exact hmod_act
          have hmod1 : L[1]'(by omega) % 3 = 0 := by
            have hlt_erase : 0 < (L.eraseIdx 0).length := by omega
            rw [getElem!_pos _ 0 hlt_erase] at hmod_j_erase
            have heq : (L.eraseIdx 0)[0]'hlt_erase = L[1]'(by omega) := by
              rw [List.getElem_eraseIdx]; simp
            rw [heq] at hmod_j_erase; exact hmod_j_erase
          have hmono01 : L[0]'(by omega) ≥ L[1]'(by omega) :=
            List.pairwise_iff_getElem.mp hpw _ _ (by omega) (by omega) (by omega)
          have hgap01 : L[0]'(by omega) - L[1]'(by omega) < 3 :=
            hgaps_L 0 (by omega)
          have h01_eq : L[0]'(by omega) = L[1]'(by omega) := by
            have ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero hmod_act'
            have ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero hmod1
            rw [ha, hb] at hmono01 hgap01 ⊢; omega
          -- Goal: L[0]'_ - L[0+2]'_ < 3.
          -- (0:ℕ)+2 is defeq to 2, so L[0+2]'_ = L[2]'_.
          rw [h01_eq]; exact hgap12
        · -- j > 0, j = actualIdx
          have hde_jm1 : ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) =
              L[j-1]'(by omega) := by
            rw [List.getElem_eraseIdx]
            simp [show j - 1 < j from by omega]
            rw [List.getElem_eraseIdx]
            simp [show j - 1 < actualIdx from by omega]
          have hj_bound : j < ((L.eraseIdx actualIdx).eraseIdx j).length := by rw [hlen_de]; omega
          have hde_j : ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound = L[j+2]'(by omega) := by
            rw [List.getElem_eraseIdx]
            simp [show ¬(j < j) from by omega]
            rw [List.getElem_eraseIdx]
            simp [show ¬(j + 1 < actualIdx) from by omega]
          have hgap_bound : (j - 1) + 1 < ((L.eraseIdx actualIdx).eraseIdx j).length := by
            rw [hlen_de]; omega
          have hgap_val := hgaps_de (j - 1) hgap_bound
          have hineq : L[j-1]'(by omega) - L[j+2]'(by omega) < 3 := by
            calc L[j-1]'(by omega) - L[j+2]'(by omega)
                = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
                  ((L.eraseIdx actualIdx).eraseIdx j)[j]'hj_bound := by rw [hde_jm1, hde_j]
              _ = ((L.eraseIdx actualIdx).eraseIdx j)[j-1]'(by rw [hlen_de]; omega) -
                  ((L.eraseIdx actualIdx).eraseIdx j)[(j-1)+1]'hgap_bound := by congr 2; omega
              _ < 3 := hgap_val
          obtain ⟨⟨hpw, _⟩, _, _⟩ := hflat
          have hmono : L[j-1]'(by omega) ≥ L[j]'(by omega) :=
            List.pairwise_iff_getElem.mp hpw _ _ (by omega) (by omega) (by omega)
          exact Nat.lt_of_le_of_lt (Nat.sub_le_sub_right hmono _) hineq
    · -- Last condition: j+2 = L.length → L[j] < 3
      intro hlast_eq hipos
      suffices h : L[j]'(by omega) < 3 by convert h using 2
      have hflat_de := isThreeFlatBool_implies' _ hflat_double_erase
      obtain ⟨⟨_, _⟩, hgaps_de, hlast_de⟩ := hflat_de
      by_cases hj_pos : j = 0
      · -- j = 0: contradiction from L[1] % 3 = 0 ∧ L[1] > 0 ∧ L[1] < 3
        subst hj_pos
        have hact0 : actualIdx = 0 := by omega
        subst hact0
        obtain ⟨⟨hpw, hpos⟩, hgaps_L, hlast_L⟩ := hflat
        have hL_ne : L ≠ [] := by intro h; simp [h] at hact_lt
        have hlast_val := hlast_L hL_ne
        rw [List.getLast_eq_getElem] at hlast_val
        have hL1_lt3 : L[1]'(by omega) < 3 := by convert hlast_val using 2; omega
        have hL1_pos : (0 : ℕ) < L[1]'(by omega) := hpos _ (List.getElem_mem (by omega))
        have hmod1 : L[1]'(by omega) % 3 = 0 := by
          have hlt_erase : 0 < (L.eraseIdx 0).length := by omega
          rw [getElem!_pos _ 0 hlt_erase] at hmod_j_erase
          have heq : (L.eraseIdx 0)[0]'hlt_erase = L[1]'(by omega) := by
            rw [List.getElem_eraseIdx]; simp
          rw [heq] at hmod_j_erase; exact hmod_j_erase
        omega
      · -- j > 0: use last element of double-erased
        have hne_de : (L.eraseIdx actualIdx).eraseIdx j ≠ [] := by
          intro heq; have hlen0 : ((L.eraseIdx actualIdx).eraseIdx j).length = 0 := by rw [heq]; simp
          rw [hlen_de] at hlen0; omega
        have hlast_val := hlast_de hne_de
        rw [List.getLast_eq_getElem] at hlast_val
        by_cases hj_gt : actualIdx < j
        · -- double-erased[j-1] = L[j]
          have hget_eq : ((L.eraseIdx actualIdx).eraseIdx j)[((L.eraseIdx actualIdx).eraseIdx j).length - 1] =
              L[j]'(by omega) := by
            have hlhs : ((L.eraseIdx actualIdx).eraseIdx j)[((L.eraseIdx actualIdx).eraseIdx j).length - 1] =
                ((L.eraseIdx actualIdx).eraseIdx j)[j - 1]'(by rw [hlen_de]; omega) := by
              congr 1; rw [hlen_de]; omega
            rw [hlhs, List.getElem_eraseIdx]
            simp [show j - 1 < j from by omega]
            rw [List.getElem_eraseIdx]
            simp [show ¬(j - 1 < actualIdx) from by omega]
            congr 1; omega
          rw [hget_eq] at hlast_val; exact hlast_val
        · -- j = actualIdx: double-erased[j-1] = L[j-1]
          have hget_eq : ((L.eraseIdx actualIdx).eraseIdx j)[((L.eraseIdx actualIdx).eraseIdx j).length - 1] =
              L[j-1]'(by omega) := by
            have hlhs : ((L.eraseIdx actualIdx).eraseIdx j)[((L.eraseIdx actualIdx).eraseIdx j).length - 1] =
                ((L.eraseIdx actualIdx).eraseIdx j)[j - 1]'(by rw [hlen_de]; omega) := by
              congr 1; rw [hlen_de]; omega
            rw [hlhs, List.getElem_eraseIdx]
            simp [show j - 1 < j from by omega]
            rw [List.getElem_eraseIdx]
            simp [show j - 1 < actualIdx from by omega]
          rw [hget_eq] at hlast_val
          obtain ⟨⟨hpw, _⟩, _, _⟩ := hflat
          have hmono : L[j-1]'(by omega) ≥ L[j]'(by omega) :=
            List.pairwise_iff_getElem.mp hpw _ _ (by omega) (by omega) (by omega)
          omega

private lemma easyLabels_eraseIdx_of_easy (A : List Labeled) (i : ℕ) (hi : i < A.length)
    (p : ℕ) (h_origin : (A[i]'hi).origin = some (p, InsertionKind.easy)) :
    (easyLabels A).Perm (p :: easyLabels (A.eraseIdx i)) := by
  unfold easyLabels
  have herase : A.eraseIdx i = A.take i ++ A.drop (i + 1) :=
    List.eraseIdx_eq_take_drop_succ A i
  have hsplit : A = A.take i ++ [A[i]'hi] ++ A.drop (i + 1) := by
    have h2 := List.getElem_cons_drop hi
    conv_lhs => rw [← List.take_append_drop i A, ← h2]
    simp
  conv_lhs => rw [hsplit]
  rw [herase]
  simp only [List.filterMap_append, List.filterMap_cons, h_origin, List.filterMap_nil]
  simp only [List.singleton_append, List.append_assoc]
  exact List.perm_middle

private lemma easyMS_eraseIdx_of_easy (A : List Labeled) (i : ℕ) (hi : i < A.length)
    (p : ℕ) (h_origin : (A[i]'hi).origin = some (p, InsertionKind.easy)) :
    easyMS A = ({p} : Multiset ℕ) + easyMS (A.eraseIdx i) := by
  unfold easyMS
  have hperm := easyLabels_eraseIdx_of_easy A i hi p h_origin
  have hms := coe_multiset_eq_of_list_perm hperm
  simpa using hms

/-- Removing an easy-labeled element leaves the hard-label multiset unchanged. -/
private lemma hardLabels_eraseIdx_of_easy (A : List Labeled) (i : ℕ) (hi : i < A.length)
    (p : ℕ) (h_origin : (A[i]'hi).origin = some (p, InsertionKind.easy)) :
    hardLabels (A.eraseIdx i) = hardLabels A := by
  unfold hardLabels
  have herase : A.eraseIdx i = A.take i ++ A.drop (i + 1) :=
    List.eraseIdx_eq_take_drop_succ A i
  have hsplit : A = A.take i ++ [A[i]'hi] ++ A.drop (i + 1) := by
    have h2 := List.getElem_cons_drop hi
    conv_lhs => rw [← List.take_append_drop i A, ← h2]
    simp
  rw [herase, hsplit]
  simp only [List.filterMap_append, List.filterMap_cons, h_origin, List.filterMap_nil]
  simp

/-- Removing a hard-labeled element transfers its label out of `hardLabels`. -/
private lemma hardLabels_eraseIdx_of_hard (A : List Labeled) (i : ℕ) (hi : i < A.length)
    (p : ℕ) (h_origin : (A[i]'hi).origin = some (p, InsertionKind.hard)) :
    (hardLabels A).Perm (p :: hardLabels (A.eraseIdx i)) := by
  unfold hardLabels
  have herase : A.eraseIdx i = A.take i ++ A.drop (i + 1) :=
    List.eraseIdx_eq_take_drop_succ A i
  have hsplit : A = A.take i ++ [A[i]'hi] ++ A.drop (i + 1) := by
    have h2 := List.getElem_cons_drop hi
    conv_lhs => rw [← List.take_append_drop i A, ← h2]
    simp
  conv_lhs => rw [hsplit]
  rw [herase]
  simp only [List.filterMap_append, List.filterMap_cons, h_origin, List.filterMap_nil]
  simp only [List.singleton_append, List.append_assoc]
  exact List.perm_middle

/-- One S2 delete step preserves `hardLabels` when the deleted frontier is easy-labeled. -/
private lemma hardLabels_scanFromSmallestLabeled_succ_erase
    (fuel' : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hact : B.length - 1 - idx < B.length)
    (p : ℕ)
    (h_easy : (B[B.length - 1 - idx]'hact).origin = some (p, InsertionKind.easy))
    (h_tail :
      hardLabels
          (scanFromSmallestLabeled fuel' (B.eraseIdx (B.length - 1 - idx)) idx
            (rec ++ [(forget B)[B.length - 1 - idx]! / 3])).1 =
        hardLabels (B.eraseIdx (B.length - 1 - idx))) :
    hardLabels (scanFromSmallestLabeled (fuel' + 1) B idx rec).1 = hardLabels B := by
  simp only [scanFromSmallestLabeled]
  rw [if_neg hidx]
  rw [if_pos hfr]
  exact (by
    simpa [forget] using
      h_tail.trans (hardLabels_eraseIdx_of_easy B (B.length - 1 - idx) hact p h_easy))

/-- One S2 skip step preserves `hardLabels` if the recursive tail does. -/
private lemma hardLabels_scanFromSmallestLabeled_succ_skip
    (fuel' : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false)
    (h_tail : hardLabels (scanFromSmallestLabeled fuel' B (idx + 1) rec).1 = hardLabels B) :
    hardLabels (scanFromSmallestLabeled (fuel' + 1) B idx rec).1 = hardLabels B := by
  simp only [scanFromSmallestLabeled]
  rw [if_neg hidx]
  rw [if_neg (by simpa [hfr])]
  exact h_tail

/-- Generic S2 hard-label preservation from a step invariant.

The invariant argument is deliberately abstract: the real trajectory proof must
show that a fired S2 frontier is easy-labeled and that the invariant recurses
through the delete/skip branch. Once those two facts are available, this lemma
handles the scan recursion and hard-label bookkeeping. -/
private lemma hardLabels_scanFromSmallestLabeled_eq_of_stepInvariant
    (Inv : ℕ → List Labeled → ℕ → List ℕ → Prop)
    (hdelete : ∀ (fuel' : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        Inv (fuel' + 1) B idx rec →
          ∃ (p : ℕ) (hact : B.length - 1 - idx < B.length),
            (B[B.length - 1 - idx]'hact).origin = some (p, InsertionKind.easy) ∧
            Inv fuel' (B.eraseIdx (B.length - 1 - idx)) idx
              (rec ++ [(forget B)[B.length - 1 - idx]! / 3]))
    (hskip : ∀ (fuel' : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
        Inv (fuel' + 1) B idx rec → Inv fuel' B (idx + 1) rec) :
    ∀ (fuel : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      Inv fuel B idx rec →
        hardLabels (scanFromSmallestLabeled fuel B idx rec).1 = hardLabels B := by
  intro fuel
  induction fuel with
  | zero =>
    intro B idx rec _inv
    simp [scanFromSmallestLabeled]
  | succ fuel' ih =>
    intro B idx rec hInv
    by_cases hidx : idx ≥ B.length
    · simp [scanFromSmallestLabeled, hidx]
    · by_cases hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true
      · obtain ⟨p, hact, heasy, hInv_tail⟩ := hdelete fuel' B idx rec hidx hfr hInv
        exact hardLabels_scanFromSmallestLabeled_succ_erase fuel' B idx rec
          hidx hfr hact p heasy (ih (B.eraseIdx (B.length - 1 - idx)) idx
            (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) hInv_tail)
      · have hfr_false : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false := by
          cases hc : isFlatRemovableBool (forget B) (B.length - 1 - idx) with
          | false => rfl
          | true => exact False.elim (hfr hc)
        exact hardLabels_scanFromSmallestLabeled_succ_skip fuel' B idx rec
          hidx hfr_false (ih B (idx + 1) rec (hskip fuel' B idx rec hidx hfr_false hInv))

/-- Elements with origin=none in processInsertionsLabeled have value not divisible by 3.
This is because such elements come from A_init unchanged, and A_init is 3-regular. -/
private lemma tryHardInsertionLabeled_preserves_origin_none_mod3
    (A : List Labeled) (p h : ℕ) (result : List Labeled)
    (htry : tryHardInsertionLabeled A p h = some result)
    (hinv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin = none → (A[i]'hi).value % 3 ≠ 0) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin = none → (result[i]'hi).value % 3 ≠ 0 := by
  simp only [tryHardInsertionLabeled] at htry
  split_ifs at htry with hcond hadm
  push_neg at hcond
  obtain ⟨hh_p, hh_A⟩ := hcond
  have hres := Option.some.inj htry
  subst hres
  set raised : List Labeled :=
    A.zipIdx.map (fun (x, j) =>
      if j < h then { x with value := x.value + 3 } else x)
  set newPart : Labeled := ⟨3 * (p - h), some (p, .hard)⟩
  have hlen_raised : raised.length = A.length := by simp [raised]
  have hh_le : h ≤ raised.length := by omega
  have hlen_ins : (raised.insertIdx h newPart).length = A.length + 1 := by
    simp [List.length_insertIdx, hlen_raised]; omega
  intro i hi horg
  rw [List.getElem_insertIdx] at horg ⊢
  by_cases h1 : i < h
  · simp only [h1, dite_true] at horg ⊢
    have hi_A : i < A.length := by omega
    have hri : raised[i]'(by omega) =
        { value := (A[i]'hi_A).value + 3, origin := (A[i]'hi_A).origin } := by
      simp [raised, List.getElem_map, List.getElem_zipIdx, h1]
    rw [hri] at horg ⊢
    dsimp only at horg ⊢
    have := hinv i hi_A horg
    omega
  · simp only [h1, dite_false] at horg ⊢
    by_cases h2 : i = h
    · simp [h2, newPart] at horg
    · simp only [h2, dite_false] at horg ⊢
      have hi_minus : i - 1 < A.length := by omega
      have hi_minus_raised : i - 1 < raised.length := by omega
      by_cases h3 : i - 1 < h
      · have hri : raised[i - 1]'hi_minus_raised =
            { value := (A[i-1]'hi_minus).value + 3, origin := (A[i-1]'hi_minus).origin } := by
          simp [raised, List.getElem_map, List.getElem_zipIdx, h3]
        rw [hri] at horg ⊢
        dsimp only at horg ⊢
        have := hinv (i - 1) hi_minus horg
        omega
      · have hri : raised[i - 1]'hi_minus_raised = (A[i-1]'hi_minus) := by
          simp [raised, List.getElem_map, List.getElem_zipIdx, h3]
        rw [hri] at horg ⊢
        exact hinv (i - 1) hi_minus horg

private lemma findHardInsertionLabeled_preserves_origin_none_mod3
    (A : List Labeled) (p : ℕ) (h₀ : ℕ) (result : List Labeled)
    (hfind : findHardInsertionLabeled A p h₀ = some result)
    (hinv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin = none → (A[i]'hi).value % 3 ≠ 0) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin = none → (result[i]'hi).value % 3 ≠ 0 := by
  have hmotive : ∀ h, findHardInsertionLabeled A p h = some result →
      ∀ (i : ℕ) (hi : i < result.length),
        (result[i]'hi).origin = none → (result[i]'hi).value % 3 ≠ 0 :=
    findHardInsertionLabeled.induct A p
      (motive := fun h => findHardInsertionLabeled A p h = some result →
        ∀ (i : ℕ) (hi : i < result.length),
          (result[i]'hi).origin = none → (result[i]'hi).value % 3 ≠ 0)
      (fun h hguard hfind => by simp [findHardInsertionLabeled, hguard] at hfind)
      (fun h hguard r htry hfind => by
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry] at hfind
        subst hfind
        exact tryHardInsertionLabeled_preserves_origin_none_mod3 A p h r htry hinv)
      (fun h hguard htry_fail ih hfind => by
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry_fail] at hfind
        exact ih hfind)
  exact hmotive h₀ hfind

private lemma tryEasyInsertionLabeled_preserves_origin_none_mod3
    (A : List Labeled) (p : ℕ) (result : List Labeled)
    (heasy : tryEasyInsertionLabeled A p = some result)
    (hinv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin = none → (A[i]'hi).value % 3 ≠ 0) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin = none → (result[i]'hi).value % 3 ≠ 0 := by
  unfold tryEasyInsertionLabeled at heasy
  simp only at heasy
  split at heasy
  · have hres := Option.some.inj heasy
    subst hres
    set newPart : Labeled := ⟨3 * p, some (p, .easy)⟩
    set pos := (A.takeWhile (·.value ≥ 3 * p)).length
    have hpos_le : pos ≤ A.length := List.IsPrefix.length_le (List.takeWhile_prefix _)
    have hlen_ins : (A.insertIdx pos newPart).length = A.length + 1 := by
      simp [List.length_insertIdx, hpos_le]
    intro i hi horg
    rw [List.getElem_insertIdx] at horg ⊢
    by_cases h1 : i < pos
    · simp only [h1, dite_true] at horg ⊢
      exact hinv i (by omega) horg
    · simp only [h1, dite_false] at horg ⊢
      by_cases h2 : i = pos
      · simp [h2, newPart] at horg
      · simp only [h2, dite_false] at horg ⊢
        have hi_bound : i - 1 < A.length := by rw [hlen_ins] at hi; omega
        exact hinv (i - 1) hi_bound horg
  · simp at heasy

private lemma performInsertionLabeled_preserves_origin_none_mod3
    (A : List Labeled) (p : ℕ)
    (hinv : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin = none → (A[i]'hi).value % 3 ≠ 0) :
    ∀ (i : ℕ) (hi : i < (performInsertionLabeled A p).length),
      ((performInsertionLabeled A p)[i]'hi).origin = none →
      ((performInsertionLabeled A p)[i]'hi).value % 3 ≠ 0 := by
  unfold performInsertionLabeled
  split
  · next r hr => exact findHardInsertionLabeled_preserves_origin_none_mod3 A p 0 r hr hinv
  · split
    · next r hr => exact tryEasyInsertionLabeled_preserves_origin_none_mod3 A p r hr hinv
    · exact hinv

private lemma processInsertionsLabeled_origin_none_not_div3
    (A_init : List Labeled) (ν : List ℕ)
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (j : ℕ) (hj : j < (processInsertionsLabeled ν A_init).length)
    (horigin : ((processInsertionsLabeled ν A_init)[j]'hj).origin = none) :
    ((processInsertionsLabeled ν A_init)[j]'hj).value % 3 ≠ 0 := by
  suffices hsuff : ∀ (A : List Labeled) (ν : List ℕ)
      (hinv : ∀ (i : ℕ) (hi : i < A.length), (A[i]'hi).origin = none → (A[i]'hi).value % 3 ≠ 0)
      (j : ℕ) (hj : j < (processInsertionsLabeled ν A).length)
      (horg : ((processInsertionsLabeled ν A)[j]'hj).origin = none),
      ((processInsertionsLabeled ν A)[j]'hj).value % 3 ≠ 0 by
    apply hsuff
    · intro i hi horg_i
      have hmem : A_init[i]'hi ∈ A_init := List.getElem_mem hi
      have hval_mem : (A_init[i]'hi).value ∈ forget A_init := by
        simp [forget, List.mem_map]
        exact ⟨A_init[i]'hi, hmem, rfl⟩
      have hndvd := hA_reg.2 _ hval_mem
      intro h3
      exact hndvd (Nat.dvd_of_mod_eq_zero h3)
    · exact horigin
  intro A ν
  induction ν generalizing A with
  | nil =>
    intro hinv j hj horg
    simp [processInsertionsLabeled] at hj horg ⊢
    exact hinv j hj horg
  | cons p rest ih =>
    intro hinv j hj horg
    simp only [processInsertionsLabeled] at hj horg ⊢
    exact ih (performInsertionLabeled A p)
      (performInsertionLabeled_preserves_origin_none_mod3 A p hinv) j hj horg

-- Forward-relocated helpers (originally near line 7486 / 7595) — needed
-- earlier to close the geometric argument inside
-- `processInsertionsLabeled_easy_value_eq`. Definitions only depend on
-- `tryHardInsertion`, `isThreeFlatBool`, `isPositivePartitionBool`, `IsThreeFlat`,
-- all defined at the top of the file.
private lemma tryHardInsertion_upper_bound_early {A : List ℕ} {p h : ℕ}
    (hsuc : (tryHardInsertion A p h).isSome) (hh : h ≥ 1) (hlen : h ≤ A.length) :
    A[h-1]'(by omega) < 3 * p - 3 * h := by
  unfold tryHardInsertion at hsuc
  split at hsuc
  · simp at hsuc
  · next hguard =>
    push_neg at hguard
    set raised := List.map (fun x : ℕ × ℕ => if x.2 < h then x.1 + 3 else x.1) A.zipIdx
    set result := List.insertIdx raised h (3 * (p - h))
    have hcond : isThreeFlatBool result = true := by
      simp only [result, raised] at hsuc ⊢
      split at hsuc
      · next hc =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        exact hc.1
      · simp at hsuc
    unfold isThreeFlatBool isPositivePartitionBool at hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcond
    obtain ⟨⟨⟨_, _⟩, hgaps⟩, _⟩ := hcond
    have hraised_len : raised.length = A.length := by
      simp [raised, List.length_map, List.length_zipIdx]
    have hresult_len : result.length = A.length + 1 := by
      simp only [result, List.length_insertIdx]
      split
      · omega
      · omega
    have hh1_lt_result_sub : h - 1 < result.length - 1 := by omega
    have hgap_h1 := hgaps (h - 1) hh1_lt_result_sub
    have hkey : h - 1 + 1 = h := by omega
    rw [hkey] at hgap_h1
    rw [getElem!_pos result (h-1) (by omega), getElem!_pos result h (by omega)] at hgap_h1
    have hresult_h : result[h]'(by omega) = 3 * (p - h) := by
      simp only [result, List.getElem_insertIdx]
      split
      · next hlt => exact absurd hlt (Nat.lt_irrefl h)
      · split
        · rfl
        · next _ hne => exact absurd trivial hne
    have hresult_h1 : result[h-1]'(by omega) = raised[h-1]'(by omega) := by
      simp only [result, List.getElem_insertIdx]
      split
      · next hlt => rfl
      · next hlt => exfalso; omega
    have hraised_h1 : raised[h-1]'(by omega) = A[h-1]'(by omega) + 3 := by
      simp only [raised]
      rw [List.getElem_map]
      simp only [List.getElem_zipIdx]
      simp [show (h - 1 : ℕ) < h from by omega]
    rw [hresult_h1, hraised_h1, hresult_h] at hgap_h1
    omega

private lemma threeFlat_descent_bound_early {A : List ℕ} (hflat : IsThreeFlat A)
    {i j : ℕ} (hij : i ≤ j) (hj : j < A.length) :
    A[i]'(by omega) ≤ A[j]'hj + 2 * (j - i) := by
  obtain ⟨_, hgap, _⟩ := hflat
  suffices h : ∀ k : ℕ, ∀ i j : ℕ, (hi : i < A.length) → (hj : j < A.length) →
      j - i = k → i ≤ j →
      A[i]'hi ≤ A[j]'hj + 2 * k from
    h (j - i) i j (by omega) hj rfl hij
  intro k
  induction k with
  | zero =>
    intro i j hi hj heq hij'
    have : i = j := by omega
    subst this
    simp
  | succ n ih =>
    intro i j hi hj heq hij'
    have hj_pos : j ≥ 1 := by omega
    have hj1_lt : j - 1 < A.length := by omega
    have hj1_succ : j - 1 + 1 < A.length := by omega
    have hgap_raw := hgap (j - 1) hj1_succ
    have heqj : A[j - 1 + 1]'hj1_succ = A[j]'hj := by
      congr 1; omega
    have hgap_j : A[j-1]'hj1_lt - A[j]'hj < 3 := by
      rw [← heqj]; exact hgap_raw
    have hij1 : i ≤ j - 1 := by omega
    have heq1 : j - 1 - i = n := by omega
    have ih_app := ih i (j - 1) hi hj1_lt heq1 hij1
    omega

/-- Elements with origin = some(p, .easy) in processInsertionsLabeled have value = 3*p.
Easy insertions set value = 3*p, and subsequent (hard) insertions never raise easy elements
because the sorted-descending order of ν ensures easy elements are at positions ≥ h. -/
private lemma processInsertionsLabeled_easy_value_eq
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (j : ℕ) (hj : j < (processInsertionsLabeled ν A_init).length)
    (p : ℕ) (horigin : ((processInsertionsLabeled ν A_init)[j]'hj).origin = some (p, InsertionKind.easy)) :
    ((processInsertionsLabeled ν A_init)[j]'hj).value = 3 * p := by
  -- Strategy: induction on ν with two invariants:
  -- (1) hinv: easy elements have value = 3*r
  -- (2) hbound: easy elements have r ≥ q for all q in ν (so r ≥ current insertion size)
  -- The hard case derives contradiction from: 3-flat gap at h-1 gives A[h-1] < 3*q - 3*h,
  -- while iterated gap from j gives A[h-1] ≥ 3*r - 2*(h-1-j), and r ≥ q yields h+2+2*j < 0.
  suffices hsuff : ∀ (A : List Labeled) (ν : List ℕ)
      (hflat : IsThreeFlat (forget A))
      (hν_sort : ν.Pairwise (· ≥ ·))
      (hinv : ∀ (i : ℕ) (hi : i < A.length) (q : ℕ),
        (A[i]'hi).origin = some (q, InsertionKind.easy) → (A[i]'hi).value = 3 * q)
      (hbound : ∀ (i : ℕ) (hi : i < A.length) (q : ℕ),
        (A[i]'hi).origin = some (q, InsertionKind.easy) → ∀ s ∈ ν, q ≥ s)
      (j : ℕ) (hj : j < (processInsertionsLabeled ν A).length)
      (p : ℕ) (horg : ((processInsertionsLabeled ν A)[j]'hj).origin = some (p, InsertionKind.easy)),
      ((processInsertionsLabeled ν A)[j]'hj).value = 3 * p by
    apply hsuff
    · exact hA_flat
    · exact hν_sort
    · intro i hi q horg_i
      have hmem := List.getElem_mem hi
      exact absurd horg_i (by rw [hA_clean _ hmem]; simp)
    · intro i hi q horg_i
      have hmem := List.getElem_mem hi
      exact absurd horg_i (by rw [hA_clean _ hmem]; simp)
    · exact horigin
  intro A ν
  induction ν generalizing A with
  | nil =>
    intro hflat _ hinv _ j hj p horg
    simp [processInsertionsLabeled] at hj horg ⊢
    exact hinv j hj p horg
  | cons q rest ih =>
    intro hflat hν_sort' hinv hbound j hj p horg
    simp only [processInsertionsLabeled] at hj horg ⊢
    have hν_rest : rest.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hν_sort').2
    have hq_ge_rest : ∀ s ∈ rest, q ≥ s := (List.pairwise_cons.mp hν_sort').1
    have hflat' : IsThreeFlat (forget (performInsertionLabeled A q)) := by
      rw [forget_performInsertionLabeled]
      exact performInsertion_preserves_flat' (forget A) q hflat
    have hinv'_hard_aux :
        ∀ (h₀ : ℕ) (result : List Labeled),
          findHardInsertionLabeled A q h₀ = some result →
          ∀ (i : ℕ) (hi : i < result.length) (r : ℕ),
            (result[i]'hi).origin = some (r, InsertionKind.easy) →
            (result[i]'hi).value = 3 * r := by
      -- No easy element gets raised: needs the geometric argument
      -- (sortedness q ≥ rest, hbound r ≥ q, 3-flat gap structure ⇒
      -- easy element value 3r ≥ 3q > 3(q-h)+3*h_offset is at position ≥ h).
      intro h₀
      induction h₀ using findHardInsertionLabeled.induct A q with
      | case1 h hguard =>
        intro result hfind i hi r horg_i
        unfold findHardInsertionLabeled at hfind
        simp [hguard] at hfind
      | case2 h hguard r_h htry =>
        intro result hfind i hi r horg_i
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry] at hfind
        subst hfind
        -- Pullback: easy at position i in r_h came from easy at position j in A.
        have horg_easy : (r_h[i]'hi).origin.map Prod.snd = some InsertionKind.easy := by
          rw [horg_i]; rfl
        obtain ⟨j, hj, hi_eq, h_origin⟩ :=
          tryHardInsertionLabeled_easy_pos_pullback A q h r_h htry i hi horg_easy
        have horg_A : (A[j]'hj).origin = some (r, InsertionKind.easy) := by
          rw [h_origin]; exact horg_i
        have hval_A : (A[j]'hj).value = 3 * r := hinv j hj r horg_A
        have hr_ge_q : r ≥ q :=
          hbound j hj r horg_A q (List.mem_cons_self)
        -- Save original htry before unfolding.
        have htry_orig : tryHardInsertionLabeled A q h = some r_h := htry
        -- Unfold tryHardInsertionLabeled to extract the structure.
        unfold tryHardInsertionLabeled at htry
        simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
        split_ifs at htry with hfail hadm
        push_neg at hfail
        obtain ⟨hh_q, hh_A⟩ := hfail
        set newPart : Labeled := ⟨3 * (q - h), some (q, .hard)⟩ with hnewPart_def
        set raised : List Labeled :=
          List.map (fun x : Labeled × ℕ =>
            if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1) A.zipIdx
          with hraised_def
        have hres : raised.insertIdx h newPart = r_h := Option.some.inj htry
        have hlen_raised : raised.length = A.length := by simp [hraised_def]
        have hraised_get : ∀ k (hk : k < A.length),
            raised[k]'(hlen_raised.symm ▸ hk) =
              if k < h then { value := (A[k]'hk).value + 3, origin := (A[k]'hk).origin }
              else (A[k]'hk) := by
          intro k hk
          simp [hraised_def, List.getElem_map, List.getElem_zipIdx]
        -- Case split on j < h vs j ≥ h.
        by_cases hjh : j < h
        · -- Geometric contradiction.
          exfalso
          -- We have r ≥ q, A[j].value = 3*r, j < h ≤ A.length.
          have hh_pos : h ≥ 1 := by omega
          -- Bridge to unlabeled tryHardInsertion succeeding.
          have hforget := forget_tryHardInsertionLabeled A q h
          rw [htry_orig] at hforget
          have h_unl_some : tryHardInsertion (forget A) q h = some (forget r_h) := by
            simp only [Option.map_some] at hforget
            exact hforget.symm
          have h_unl_isSome : (tryHardInsertion (forget A) q h).isSome := by
            rw [h_unl_some]; rfl
          have hh_le_forget : h ≤ (forget A).length := by
            rw [length_forget]; exact hh_A
          have hub :=
            tryHardInsertion_upper_bound_early h_unl_isSome hh_pos hh_le_forget
          have hh1_lt_A : h - 1 < A.length := by omega
          have hub' : (A[h-1]'hh1_lt_A).value < 3 * q - 3 * h := by
            have hf : (forget A)[h-1]'(by rw [length_forget]; exact hh1_lt_A) =
                (A[h-1]'hh1_lt_A).value := by
              simp [forget, List.getElem_map]
            rw [← hf]
            exact hub
          have hdesc :=
            threeFlat_descent_bound_early hflat (show j ≤ h - 1 by omega)
              (by rw [length_forget]; exact hh1_lt_A)
          have hdesc' : (A[j]'hj).value ≤ (A[h-1]'hh1_lt_A).value + 2 * (h - 1 - j) := by
            have hf1 : (forget A)[j]'(by rw [length_forget]; exact hj) = (A[j]'hj).value := by
              simp [forget, List.getElem_map]
            have hf2 : (forget A)[h-1]'(by rw [length_forget]; exact hh1_lt_A) =
                (A[h-1]'hh1_lt_A).value := by
              simp [forget, List.getElem_map]
            rw [hf1, hf2] at hdesc
            exact hdesc
          omega
        · -- j ≥ h: result[i] corresponds to raised[j] = A[j], no value change.
          push_neg at hjh
          -- i = j + 1 (from pullback when ¬ j < h).
          have hi_val : i = j + 1 := by
            have hjh_not : ¬ j < h := Nat.not_lt.mpr hjh
            simp [hjh_not] at hi_eq
            exact hi_eq
          -- result[i] = (raised.insertIdx h newPart)[i].
          have hi_ins : i < (raised.insertIdx h newPart).length := by
            rw [List.length_insertIdx]; simp [hlen_raised, hh_A]; omega
          have keyAll : r_h[i]'hi = (raised.insertIdx h newPart)[i]'hi_ins := by
            congr 1; exact hres.symm
          rw [keyAll]
          rw [List.getElem_insertIdx]
          have hnotlt : ¬ (i < h) := by omega
          have hnoteq : i ≠ h := by omega
          rw [dif_neg hnotlt, dif_neg hnoteq]
          have hi_minus_lt : i - 1 < A.length := by
            rw [hi_val]; omega
          have hi_minus_eq : i - 1 = j := by omega
          have hi_minus_not_lt : ¬ (i - 1 < h) := by omega
          have hri := hraised_get (i - 1) hi_minus_lt
          rw [if_neg hi_minus_not_lt] at hri
          -- hri : raised[i-1] = A[i-1]
          rw [hri]
          -- Goal: A[i-1].value = 3 * r. Use hi_minus_eq : i - 1 = j and hval_A.
          have hAget : (A[i - 1]'hi_minus_lt) = (A[j]'hj) := by
            congr 1
          rw [hAget]
          exact hval_A
      | case3 h hguard htry_fail ih =>
        intro result hfind i hi r horg_i
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry_fail] at hfind
        exact ih result hfind i hi r horg_i
    -- Helper: tryEasyInsertion case for hinv.
    have hinv'_easy_aux :
        ∀ (result : List Labeled),
          tryEasyInsertionLabeled A q = some result →
          ∀ (i : ℕ) (hi : i < result.length) (r : ℕ),
            (result[i]'hi).origin = some (r, InsertionKind.easy) →
            (result[i]'hi).value = 3 * r := by
      intro result he i hi r horg_i
      unfold tryEasyInsertionLabeled at he
      simp only at he
      split_ifs at he with hcond
      set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
      set pos := (A.takeWhile (·.value ≥ 3 * q)).length
      have hres : A.insertIdx pos newPart = result := Option.some.inj he
      have hpos_le : pos ≤ A.length := List.IsPrefix.length_le (List.takeWhile_prefix _)
      have hlen_r : result.length = A.length + 1 := by
        rw [← hres, List.length_insertIdx]; simp [hpos_le]
      subst hres
      rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
      · have hpre : i < A.length := by omega
        have horig := Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
        rw [horig] at horg_i
        have hval := hinv i hpre r horg_i
        rw [List.getElem_insertIdx]
        simp [hlt]
        exact hval
      · subst heq
        have horig := Hints.origin_insertIdx_at A pos newPart hi
        rw [horig] at horg_i
        simp [newPart] at horg_i
        rw [List.getElem_insertIdx]
        simp [newPart, ← horg_i]
      · have hpre : i - 1 < A.length := by rw [hlen_r] at hi; omega
        have horig := Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
        rw [horig] at horg_i
        have hval := hinv (i - 1) hpre r horg_i
        rw [List.getElem_insertIdx]
        have hnotlt : ¬ (i < pos) := by omega
        have hnoteq : i ≠ pos := by omega
        simp [hnotlt, hnoteq]
        exact hval
    have hinv' : ∀ (i : ℕ) (hi : i < (performInsertionLabeled A q).length) (r : ℕ),
        ((performInsertionLabeled A q)[i]'hi).origin = some (r, InsertionKind.easy) →
        ((performInsertionLabeled A q)[i]'hi).value = 3 * r := by
      unfold performInsertionLabeled
      split
      · next r_hard hf => exact hinv'_hard_aux 0 r_hard hf
      · split
        · next r_easy he => exact hinv'_easy_aux r_easy he
        · exact hinv
    -- hbound preservation
    have hbound'_hard_aux :
        ∀ (h₀ : ℕ) (result : List Labeled),
          findHardInsertionLabeled A q h₀ = some result →
          ∀ (i : ℕ) (hi : i < result.length) (r : ℕ),
            (result[i]'hi).origin = some (r, InsertionKind.easy) →
            ∀ s ∈ rest, r ≥ s := by
      intro h₀
      induction h₀ using findHardInsertionLabeled.induct A q with
      | case1 h hguard =>
        intro result hfind i hi r horg_i s hs_rest
        unfold findHardInsertionLabeled at hfind
        simp [hguard] at hfind
      | case2 h hguard r_h htry =>
        intro result hfind i hi r horg_i s hs_rest
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry] at hfind
        subst hfind
        have hs_full : s ∈ q :: rest := List.mem_cons_of_mem q hs_rest
        have horg_easy : (r_h[i]'hi).origin.map Prod.snd = some InsertionKind.easy := by
          rw [horg_i]; rfl
        obtain ⟨j, hj, _, h_origin⟩ :=
          tryHardInsertionLabeled_easy_pos_pullback A q h r_h htry i hi horg_easy
        have horg_A : (A[j]'hj).origin = some (r, InsertionKind.easy) := by
          rw [h_origin]; exact horg_i
        exact hbound j hj r horg_A s hs_full
      | case3 h hguard htry_fail ih =>
        intro result hfind i hi r horg_i s hs_rest
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry_fail] at hfind
        exact ih result hfind i hi r horg_i s hs_rest
    have hbound'_easy_aux :
        ∀ (result : List Labeled),
          tryEasyInsertionLabeled A q = some result →
          ∀ (i : ℕ) (hi : i < result.length) (r : ℕ),
            (result[i]'hi).origin = some (r, InsertionKind.easy) →
            ∀ s ∈ rest, r ≥ s := by
      intro result he i hi r horg_i s hs_rest
      have hs_full : s ∈ q :: rest := List.mem_cons_of_mem q hs_rest
      unfold tryEasyInsertionLabeled at he
      simp only at he
      split_ifs at he with hcond
      set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
      set pos := (A.takeWhile (·.value ≥ 3 * q)).length
      have hres : A.insertIdx pos newPart = result := Option.some.inj he
      have hpos_le : pos ≤ A.length := List.IsPrefix.length_le (List.takeWhile_prefix _)
      have hlen_r : result.length = A.length + 1 := by
        rw [← hres, List.length_insertIdx]; simp [hpos_le]
      subst hres
      rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
      · have hpre : i < A.length := by omega
        have horig := Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
        rw [horig] at horg_i
        exact hbound i hpre r horg_i s hs_full
      · subst heq
        have horig := Hints.origin_insertIdx_at A pos newPart hi
        rw [horig] at horg_i
        simp [newPart] at horg_i
        rw [← horg_i]
        exact hq_ge_rest s hs_rest
      · have hpre : i - 1 < A.length := by rw [hlen_r] at hi; omega
        have horig := Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
        rw [horig] at horg_i
        exact hbound (i - 1) hpre r horg_i s hs_full
    have hbound' : ∀ (i : ℕ) (hi : i < (performInsertionLabeled A q).length) (r : ℕ),
        ((performInsertionLabeled A q)[i]'hi).origin = some (r, InsertionKind.easy) →
        ∀ s ∈ rest, r ≥ s := by
      unfold performInsertionLabeled
      split
      · next r_hard hf => exact hbound'_hard_aux 0 r_hard hf
      · split
        · next r_easy he => exact hbound'_easy_aux r_easy he
        · intro i hi r horg_i s hs_rest
          have hs_full : s ∈ q :: rest := List.mem_cons_of_mem q hs_rest
          exact hbound i hi r horg_i s hs_full
    exact ih (performInsertionLabeled A q) hflat' hν_rest hinv' hbound' j hj p horg

-- Lemma: processInsertionsLabeled_easy_value_eq END MARKER (do not remove)
-- The proof of processInsertionsLabeled_easy_value_eq is sorry-ed pending fix of
-- `split at *` failure after unfold performInsertionLabeled.
-- The statement IS true and was partially proved before.

/-- Hard-origin position pullback through `tryHardInsertionLabeled`.

At a successful `tryHardInsertionLabeled A p h = some result`, every hard
origin in `result` either is the newly-inserted hard at position `h` with
size `p`, or corresponds to a pre-existing hard at some position in `A`. -/
private lemma tryHardInsertionLabeled_hard_pos_pullback
    (A : List Labeled) (p h : ℕ) (result : List Labeled)
    (hr : tryHardInsertionLabeled A p h = some result)
    (i : ℕ) (hi : i < result.length) (r : ℕ)
    (h_hard : (result[i]'hi).origin = some (r, InsertionKind.hard)) :
    (i = h ∧ r = p ∧ (result[i]'hi).value = 3 * (p - h)) ∨
    (∃ (j : ℕ) (hj : j < A.length),
       i = (if j < h then j else j + 1) ∧
       (A[j]'hj).origin = some (r, InsertionKind.hard) ∧
       (result[i]'hi).value = if j < h then (A[j]'hj).value + 3 else (A[j]'hj).value) := by
  unfold tryHardInsertionLabeled at hr
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at hr
  split_ifs at hr with hfail hadm
  push_neg at hfail
  obtain ⟨hhp, hhA⟩ := hfail
  have hres : (List.map (fun x : Labeled × ℕ =>
                if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1) A.zipIdx).insertIdx
              h { value := 3 * (p - h), origin := some (p, InsertionKind.hard) } = result :=
    Option.some.inj hr
  set raised : List Labeled :=
    List.map (fun x : Labeled × ℕ => if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1) A.zipIdx
    with hraised_def
  set newPart : Labeled := ⟨3 * (p - h), some (p, InsertionKind.hard)⟩ with hnewPart_def
  have hlen_raised : raised.length = A.length := by simp [hraised_def]
  have hlen_result : result.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx]; simp [hlen_raised, hhA]
  have hraised_get : ∀ k (hk : k < A.length),
      raised[k]'(hlen_raised.symm ▸ hk) =
        if k < h then { value := (A[k]'hk).value + 3, origin := (A[k]'hk).origin }
        else (A[k]'hk) := by
    intro k hk
    simp [hraised_def, List.getElem_map, List.getElem_zipIdx]
  have hi_ins : i < (raised.insertIdx h newPart).length := by
    rw [List.length_insertIdx]; simp [hlen_raised, hhA]; omega
  have keyAll : result[i]'hi = (raised.insertIdx h newPart)[i]'hi_ins := by
    congr 1; exact hres.symm
  rw [keyAll]
  rw [keyAll] at h_hard
  rw [List.getElem_insertIdx] at h_hard ⊢
  by_cases h1 : i < h
  · rw [dif_pos h1] at h_hard ⊢
    have hi_A : i < A.length := by omega
    rw [hraised_get i hi_A] at h_hard ⊢
    simp only [h1, if_pos] at h_hard ⊢
    right
    refine ⟨i, hi_A, ?_, h_hard, by simp [h1]⟩
    simp [h1]
  · rw [dif_neg h1] at h_hard ⊢
    by_cases h2 : i = h
    · rw [dif_pos h2] at h_hard ⊢
      simp [hnewPart_def] at h_hard
      left
      refine ⟨h2, h_hard.symm, ?_⟩
      simp [hnewPart_def]
    · rw [dif_neg h2] at h_hard ⊢
      have hi_pos : i ≥ 1 := by omega
      have hi_minus : i - 1 < A.length := by omega
      have hi_minus_ge : ¬ (i - 1 < h) := by omega
      rw [hraised_get (i - 1) hi_minus] at h_hard ⊢
      simp only [hi_minus_ge, if_neg, not_false_iff] at h_hard ⊢
      right
      refine ⟨i - 1, hi_minus, ?_, h_hard, by simp [hi_minus_ge]⟩
      simp [hi_minus_ge]; omega

/- NOTE: processInsertionsLabeled_hard_not_FR is FALSE.
   Counterexample: A_init = embed [2, 1], ν = [2, 1].
   processInsertionsLabeled [2,1] (embed [2,1]) = [{5,none},{3,(2,hard)},{3,(1,easy)},{1,none}]
   Position 1 (hard, value 3): isFlatRemovableBool [5,3,3,1] 1 = true.
   The lemma claims hard elements are never FR, which is FALSE.

   The scan proof (s2_labeled_scan_records_perm_easyLabels) should use
   FrontierFRImpliesEasy instead of global I3 that depends on this false lemma.
    For now, we sorry the scan proof's I3 establishment (hI3_initial hard case). -/

-- Helper for the adjacent case in s2_labeled_scan_records_perm_easyLabels.
--   In a 3-flat list, if positions i+1 and i+2 have the same value (both multiples of 3),
--   and positions i and i+3 are both NOT multiples of 3, then gap(i, i+3) < 3.
--   The core-gap property is taken as a hypothesis and proved at the call site
--   from the structure of processInsertionsLabeled.
private def NoEasyInCheckedSuffix (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (j : ℕ) (hj : j < B.length),
    B.length - idx ≤ j →
      (B[j]'hj).origin.map Prod.snd ≠ some InsertionKind.easy

/-- Every unchecked easy-labeled part remains flat-removable. -/
private def AllRemainingEasyFR (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (j : ℕ) (hj : j < B.length),
    j < B.length - idx →
      (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy →
        isFlatRemovableBool (forget B) j = true

/-- If the current S2 frontier is flat-removable, then it is easy-labeled. -/
private def FrontierFRImpliesEasy (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (h_idx : idx < B.length),
    let actualIdx := B.length - 1 - idx
    isFlatRemovableBool (forget B) actualIdx = true →
      (B[actualIdx]'(by omega)).origin.map Prod.snd = some InsertionKind.easy

private inductive S2Reach (start : List Labeled) :
    List Labeled → ℕ → List ℕ → Prop
  | init : S2Reach start start 0 []
  | erase {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ}
      (hidx : idx < B.length)
      (hactual : actualIdx = B.length - 1 - idx)
      (hfr : isFlatRemovableBool (forget B) actualIdx = true)
      (hprev : S2Reach start B idx rec) :
      S2Reach start (B.eraseIdx actualIdx) idx
        (rec ++ [(forget B)[actualIdx]! / 3])
  | skip {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ}
      (hidx : idx < B.length)
      (hactual : actualIdx = B.length - 1 - idx)
      (hnfr : isFlatRemovableBool (forget B) actualIdx = false)
      (hprev : S2Reach start B idx rec) :
      S2Reach start B (idx + 1) rec

private lemma S2Reach.sublist {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (h : S2Reach start B idx rec) :
    B.Sublist start := by
  induction h with
  | init => exact List.Sublist.refl start
  | erase hidx hactual hfr hprev ih =>
      exact (List.eraseIdx_sublist _ _).trans ih
  | skip hidx hactual hnfr hprev ih =>
      exact ih

private lemma S2Reach.mem_start {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (h : S2Reach start B idx rec) {x : Labeled} (hx : x ∈ B) :
    x ∈ start :=
  (S2Reach.sublist h).mem hx

private structure S2Good
    (target : Multiset ℕ) (start B : List Labeled) (idx : ℕ) (rec : List ℕ) : Prop where
  reach : S2Reach start B idx rec
  flat : IsThreeFlat (forget B)
  rec_easy : recMS rec + easyMS B = target
  noEasyChecked : NoEasyInCheckedSuffix B idx
  remainingEasyFR : AllRemainingEasyFR B idx
  frontierFREasy : FrontierFRImpliesEasy B idx
  coreNotDiv : ∀ (j : ℕ) (hj : j < B.length),
    (B[j]'hj).origin = none → (B[j]'hj).value % 3 ≠ 0
  easyValue : ∀ (j : ℕ) (hj : j < B.length) (p : ℕ),
    (B[j]'hj).origin = some (p, InsertionKind.easy) → (B[j]'hj).value = 3 * p

private lemma noEasyInCheckedSuffix_zero (B : List Labeled) :
    NoEasyInCheckedSuffix B 0 := by
  intro j hj hge
  omega

private lemma allRemainingEasyFR_zero_processInsertionsLabeled
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    AllRemainingEasyFR (processInsertionsLabeled ν A_init) 0 := by
  intro j hj _ hkind
  exact easy_parts_are_flat_removable A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos j hj hkind

private lemma frontierFRImpliesEasy_zero_of_threeFlat
    (B : List Labeled) (hflat : IsThreeFlat (forget B)) :
    FrontierFRImpliesEasy B 0 := by
  intro hidx
  simp only [Nat.sub_zero]
  intro hfr
  exfalso
  have hne : forget B ≠ [] := by
    have : 0 < (forget B).length := by simpa [length_forget] using hidx
    exact List.ne_nil_of_length_pos this
  have hlast_lt3 := hflat.2.2 hne
  have hlast_eq : (forget B).getLast hne = (B[B.length - 1]'(by omega)).value := by
    rw [List.getLast_eq_getElem]
    simp [forget, List.getElem_map, length_forget]
  rw [hlast_eq] at hlast_lt3
  have hpos : 0 < (B[B.length - 1]'(by omega)).value := by
    have hmem : (B[B.length - 1]'(by omega)).value ∈ forget B := by
      simp [forget, List.mem_map]
      exact ⟨_, List.getElem_mem _, rfl⟩
    exact hflat.1.2 _ hmem
  have hmod : (B[B.length - 1]'(by omega)).value % 3 = 0 := by
    unfold isFlatRemovableBool at hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
    have hval_eq :
        (B[B.length - 1]'(by omega)).value = (forget B)[B.length - 1]! := by
      have hlt : B.length - 1 < (forget B).length := by simpa [length_forget] using (by omega : B.length - 1 < B.length)
      rw [getElem!_pos (forget B) (B.length - 1) hlt]
      simp [forget, List.getElem_map]
    rw [hval_eq]
    exact hfr.1.2
  omega

private lemma frontierFRImpliesEasy_of_noHard
    {B : List Labeled} {idx : ℕ}
    (hcore : ∀ (j : ℕ) (hj : j < B.length),
      (B[j]'hj).origin = none → (B[j]'hj).value % 3 ≠ 0)
    (hnoHard : ∀ (hidx : idx < B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
      (p : ℕ),
      (B[B.length - 1 - idx]'(by omega)).origin = some (p, InsertionKind.hard) →
        False) :
    FrontierFRImpliesEasy B idx := by
  intro hidx
  dsimp only
  intro hfr
  have hact : B.length - 1 - idx < B.length := by omega
  have hmod : (B[B.length - 1 - idx]'hact).value % 3 = 0 := by
    unfold isFlatRemovableBool at hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
    have hval_eq :
        (B[B.length - 1 - idx]'hact).value =
          (forget B)[B.length - 1 - idx]! := by
      have hlt : B.length - 1 - idx < (forget B).length := by
        simpa [length_forget] using hact
      rw [getElem!_pos (forget B) (B.length - 1 - idx) hlt]
      simp [forget, List.getElem_map]
    rw [hval_eq]
    exact hfr.1.2
  cases horig : (B[B.length - 1 - idx]'hact).origin with
  | none =>
      exfalso
      exact hcore (B.length - 1 - idx) hact horig hmod
  | some pr =>
      cases pr with
      | mk p kind =>
          cases kind
          · simp [horig]
          · exact False.elim (hnoHard hidx hfr p horig)

private lemma s2Good_initial_processInsertionsLabeled
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    S2Good (easyMS labeled) labeled labeled 0 [] := by
  intro labeled
  have hflat_labeled : IsThreeFlat (forget labeled) := by
    rw [show labeled = processInsertionsLabeled ν A_init from rfl]
    rw [forget_processInsertionsLabeled]
    suffices h : ∀ (parts : List ℕ) (B : List ℕ), IsThreeFlat B →
        IsThreeFlat (processInsertions parts B) from h ν _ hA_flat
    intro parts
    induction parts with
    | nil => intro B hB; exact hB
    | cons p rest ih =>
      intro B hB
      simp only [processInsertions]
      exact ih _ (performInsertion_preserves_flat' B p hB)
  refine ⟨S2Reach.init, hflat_labeled, ?_, noEasyInCheckedSuffix_zero labeled,
    ?_, frontierFRImpliesEasy_zero_of_threeFlat labeled hflat_labeled, ?_, ?_⟩
  · simp [recMS]
  · rw [show labeled = processInsertionsLabeled ν A_init from rfl]
    exact allRemainingEasyFR_zero_processInsertionsLabeled
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  · rw [show labeled = processInsertionsLabeled ν A_init from rfl]
    intro j hj hnone
    exact processInsertionsLabeled_origin_none_not_div3 A_init ν hA_reg hA_clean j hj hnone
  · rw [show labeled = processInsertionsLabeled ν A_init from rfl]
    intro j hj p heasy
    exact processInsertionsLabeled_easy_value_eq A_init ν hA_flat hA_clean hν_sort j hj p heasy

private lemma s2Good_frontier_origin_easy
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true) :
    ∃ (p : ℕ) (hact : B.length - 1 - idx < B.length),
      (B[B.length - 1 - idx]'hact).origin = some (p, InsertionKind.easy) := by
  have hlt : idx < B.length := by omega
  have hact : B.length - 1 - idx < B.length := by omega
  have hkind := hgood.frontierFREasy hlt hfr
  simp only at hkind
  cases horig : (B[B.length - 1 - idx]'hact).origin with
  | none =>
      simp [horig] at hkind
  | some pr =>
      cases pr with
      | mk p kind =>
          cases kind
          · exact ⟨p, hact, horig⟩
          · simp [horig] at hkind

private lemma s2Good_frontier_record_easy
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true) :
    (B[B.length - 1 - idx]'(by omega)).origin =
      some ((forget B)[B.length - 1 - idx]! / 3, InsertionKind.easy) := by
  obtain ⟨p, hact, heasy⟩ := s2Good_frontier_origin_easy hgood hidx hfr
  have hval := hgood.easyValue (B.length - 1 - idx) hact p heasy
  have hforget :
      (B[B.length - 1 - idx]'hact).value = (forget B)[B.length - 1 - idx]! := by
    have hlt : B.length - 1 - idx < (forget B).length := by
      simpa [length_forget] using hact
    rw [getElem!_pos (forget B) (B.length - 1 - idx) hlt]
    simp [forget, List.getElem_map]
  have hp : p = (forget B)[B.length - 1 - idx]! / 3 := by
    rw [← hforget, hval]
    exact (Nat.mul_div_cancel_left p (by norm_num : 0 < 3)).symm
  rw [heasy, hp]

private lemma hardLabels_scanFromSmallestLabeled_eq_of_S2Good_transitions
    {target : Multiset ℕ} {start : List Labeled}
    (hdelete : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        S2Good target start B idx rec →
          S2Good target start (B.eraseIdx (B.length - 1 - idx)) idx
            (rec ++ [(forget B)[B.length - 1 - idx]! / 3]))
    (hskip : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
        S2Good target start B idx rec →
          S2Good target start B (idx + 1) rec) :
    ∀ (fuel : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Good target start B idx rec →
        hardLabels (scanFromSmallestLabeled fuel B idx rec).1 = hardLabels B := by
  refine hardLabels_scanFromSmallestLabeled_eq_of_stepInvariant
    (Inv := fun _fuel B idx rec => S2Good target start B idx rec) ?_ ?_
  · intro fuel' B idx rec hidx hfr hgood
    obtain ⟨p, hact, heasy⟩ := s2Good_frontier_origin_easy hgood hidx hfr
    exact ⟨p, hact, heasy, hdelete B idx rec hidx hfr hgood⟩
  · intro fuel' B idx rec hidx hfr hgood
    exact hskip B idx rec hidx hfr hgood

private lemma allRemainingEasyFR_skip {B : List Labeled} {idx : ℕ}
    (hrem : AllRemainingEasyFR B idx) :
    AllRemainingEasyFR B (idx + 1) := by
  intro j hj hj_unchecked hkind
  exact hrem j hj (by omega) hkind

private lemma noEasyInCheckedSuffix_skip {B : List Labeled} {idx : ℕ}
    (hrem : AllRemainingEasyFR B idx)
    (hchecked : NoEasyInCheckedSuffix B idx)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false) :
    NoEasyInCheckedSuffix B (idx + 1) := by
  intro j hj hge hkind
  by_cases hj_frontier : j = B.length - 1 - idx
  · subst hj_frontier
    have hfr' := hrem (B.length - 1 - idx) (by omega) (by omega) hkind
    rw [hfr] at hfr'
    cases hfr'
  · exact hchecked j hj (by omega) hkind

private lemma noEasyInCheckedSuffix_delete {B : List Labeled} {idx : ℕ}
    (hchecked : NoEasyInCheckedSuffix B idx)
    (hidx : ¬ idx ≥ B.length) :
    NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx := by
  intro j hj hge hkind
  set actualIdx := B.length - 1 - idx with hactual
  have hact : actualIdx < B.length := by omega
  have hlen_erase : (B.eraseIdx actualIdx).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact
  have hj_actual : j < (B.eraseIdx actualIdx).length := by
    simpa [hactual] using hj
  have hkind_actual :
      ((B.eraseIdx actualIdx)[j]'hj_actual).origin.map Prod.snd =
        some InsertionKind.easy := by
    simpa [hactual] using hkind
  have hj_ge_actual : ¬ j < actualIdx := by
    rw [hactual] at hge
    rw [hlen_erase] at hge
    omega
  have hj1_lt : j + 1 < B.length := by
    rw [hlen_erase] at hj_actual
    omega
  have heq := List.getElem_eraseIdx (l := B) (i := actualIdx) (j := j) hj_actual
  simp only [heq, hj_ge_actual, dite_false] at hkind_actual
  exact hchecked (j + 1) hj1_lt (by rw [hactual] at hge; rw [hlen_erase] at hge; omega) hkind_actual

private lemma s2Good_skip
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false)
    (hfrontier_next : FrontierFRImpliesEasy B (idx + 1)) :
    S2Good target start B (idx + 1) rec := by
  refine ⟨?_, hgood.flat, hgood.rec_easy, ?_, ?_, hfrontier_next,
    hgood.coreNotDiv, hgood.easyValue⟩
  · exact S2Reach.skip (start := start) (B := B) (idx := idx)
      (actualIdx := B.length - 1 - idx) (rec := rec) (by omega) rfl hfr hgood.reach
  · exact noEasyInCheckedSuffix_skip hgood.remainingEasyFR hgood.noEasyChecked hidx hfr
  · exact allRemainingEasyFR_skip hgood.remainingEasyFR

private lemma s2Good_delete
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hrecord :
      (B[B.length - 1 - idx]'(by omega)).origin =
        some ((forget B)[B.length - 1 - idx]! / 3, InsertionKind.easy))
    (hchecked_erased : NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx)
    (hremaining_erased : AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx)
    (hfrontier_erased : FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx) :
    S2Good target start (B.eraseIdx (B.length - 1 - idx)) idx
      (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) := by
  set actualIdx := B.length - 1 - idx
  have hactual : actualIdx = B.length - 1 - idx := rfl
  have hact : actualIdx < B.length := by omega
  have hlen_erase : (B.eraseIdx actualIdx).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact
  have hflat_erased : IsThreeFlat (forget (B.eraseIdx actualIdx)) := by
    have h_fe : forget (B.eraseIdx actualIdx) = (forget B).eraseIdx actualIdx := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    unfold isFlatRemovableBool at hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
    exact isThreeFlatBool_implies' _ hfr.2
  refine ⟨?_, hflat_erased, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact S2Reach.erase (start := start) (B := B) (idx := idx)
      (actualIdx := actualIdx) (rec := rec) (by omega) hactual hfr hgood.reach
  · have hrecord' :
        (B[actualIdx]'hact).origin =
          some ((forget B)[actualIdx]! / 3, InsertionKind.easy) := by
      subst actualIdx
      exact hrecord
    set p := (forget B)[actualIdx]! / 3 with hp_def
    have heasyMS := easyMS_eraseIdx_of_easy B actualIdx hact
      p (by simpa [p] using hrecord')
    have hold : recMS rec + (easyMS (B.eraseIdx actualIdx) + ({p} : Multiset ℕ)) = target := by
      simpa [heasyMS, p, add_assoc, add_comm, add_left_comm] using hgood.rec_easy
    calc
      recMS (rec ++ [(forget B)[actualIdx]! / 3]) + easyMS (B.eraseIdx actualIdx)
          = (recMS rec + ({p} : Multiset ℕ)) + easyMS (B.eraseIdx actualIdx) := by
              rw [← hp_def]
              change (((rec ++ [p] : List ℕ) : Multiset ℕ) + easyMS (B.eraseIdx actualIdx) =
                (recMS rec + ({p} : Multiset ℕ)) + easyMS (B.eraseIdx actualIdx))
              rw [← Multiset.coe_add rec [p]]
              simp [recMS]
      _ = recMS rec + (easyMS (B.eraseIdx actualIdx) + ({p} : Multiset ℕ)) := by
              rw [add_assoc, add_comm ({p} : Multiset ℕ) (easyMS (B.eraseIdx actualIdx))]
      _ = target := hold
  · simpa [hactual] using hchecked_erased
  · simpa [hactual] using hremaining_erased
  · simpa [hactual] using hfrontier_erased
  · intro j hj hnone
    have heq := List.getElem_eraseIdx (l := B) (i := actualIdx) (j := j) hj
    by_cases hjlt : j < actualIdx
    · simp only [heq, hjlt, ↓reduceDIte] at hnone ⊢
      exact hgood.coreNotDiv j (by omega) hnone
    · simp only [heq, hjlt, ↓reduceDIte] at hnone ⊢
      exact hgood.coreNotDiv (j + 1) (by rw [hlen_erase] at hj; omega) hnone
  · intro j hj p heasy
    have heq := List.getElem_eraseIdx (l := B) (i := actualIdx) (j := j) hj
    by_cases hjlt : j < actualIdx
    · simp only [heq, hjlt, ↓reduceDIte] at heasy ⊢
      exact hgood.easyValue j (by omega) p heasy
    · simp only [heq, hjlt, ↓reduceDIte] at heasy ⊢
      exact hgood.easyValue (j + 1) (by rw [hlen_erase] at hj; omega) p heasy

private lemma s2Good_delete_from_preservation
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hchecked_erased : NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx)
    (hremaining_erased : AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx)
    (hfrontier_erased : FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx) :
    S2Good target start (B.eraseIdx (B.length - 1 - idx)) idx
      (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) := by
  exact s2Good_delete hgood hidx hfr
    (s2Good_frontier_record_easy hgood hidx hfr)
    hchecked_erased hremaining_erased hfrontier_erased

private lemma hardLabels_scanFromSmallestLabeled_eq_of_S2Good_geometric
    {target : Multiset ℕ} {start : List Labeled}
    (hdelete_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        S2Good target start B idx rec →
          NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx ∧
          AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
          FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx)
    (hskip_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
        S2Good target start B idx rec →
          FrontierFRImpliesEasy B (idx + 1)) :
    ∀ (fuel : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Good target start B idx rec →
        hardLabels (scanFromSmallestLabeled fuel B idx rec).1 = hardLabels B := by
  apply hardLabels_scanFromSmallestLabeled_eq_of_S2Good_transitions
  · intro B idx rec hidx hfr hgood
    obtain ⟨hchecked, hremaining, hfrontier⟩ := hdelete_geom B idx rec hidx hfr hgood
    exact s2Good_delete_from_preservation hgood hidx hfr hchecked hremaining hfrontier
  · intro B idx rec hidx hfr hgood
    exact s2Good_skip hgood hidx hfr (hskip_geom B idx rec hidx hfr hgood)

private lemma easyLabels_eq_nil_of_noEasyInCheckedSuffix
    {B : List Labeled} {idx : ℕ}
    (hchecked : NoEasyInCheckedSuffix B idx)
    (hidx : idx ≥ B.length) :
    easyLabels B = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro x hx
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
  have hno := hchecked j hj (by omega)
  subst hget
  cases horig : (B[j]'hj).origin with
  | none => simp [easyLabels, horig]
  | some pr =>
      cases pr with
      | mk p kind =>
          cases kind
          · exfalso
            exact hno (by simp [horig])
          · simp [easyLabels, horig]

private lemma s2Good_terminal_recMS_eq_target
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : idx ≥ B.length) :
    recMS rec = target := by
  have heasy : easyLabels B = [] :=
    easyLabels_eq_nil_of_noEasyInCheckedSuffix hgood.noEasyChecked hidx
  have h := hgood.rec_easy
  simpa [easyMS, heasy] using h

private lemma recMS_scanFromSmallestLabeled_eq_target_of_S2Good_geometric
    {target : Multiset ℕ} {start : List Labeled}
    (hdelete_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        S2Good target start B idx rec →
          NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx ∧
          AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
          FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx)
    (hskip_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
        S2Good target start B idx rec →
          FrontierFRImpliesEasy B (idx + 1)) :
    ∀ (fuel : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Good target start B idx rec →
      fuel ≥ B.length - idx →
        recMS (scanFromSmallestLabeled fuel B idx rec).2 = target := by
  intro fuel
  induction fuel with
  | zero =>
    intro B idx rec hgood hfuel
    have hterminal : idx ≥ B.length := by omega
    simp [scanFromSmallestLabeled]
    exact s2Good_terminal_recMS_eq_target hgood hterminal
  | succ fuel' ih =>
    intro B idx rec hgood hfuel
    by_cases hidx_ge : idx ≥ B.length
    · simp [scanFromSmallestLabeled, hidx_ge]
      exact s2Good_terminal_recMS_eq_target hgood hidx_ge
    · by_cases hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true
      · obtain ⟨hchecked, hremaining, hfrontier⟩ :=
          hdelete_geom B idx rec hidx_ge hfr hgood
        have hgood' := s2Good_delete_from_preservation hgood hidx_ge hfr
          hchecked hremaining hfrontier
        have hact : B.length - 1 - idx < B.length := by omega
        have hlen_erase : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
          List.length_eraseIdx_of_lt hact
        simp only [scanFromSmallestLabeled]
        rw [if_neg hidx_ge, if_pos hfr]
        apply ih
        · exact hgood'
        · rw [hlen_erase]
          omega
      · have hfr_false : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false := by
          cases hc : isFlatRemovableBool (forget B) (B.length - 1 - idx) with
          | false => rfl
          | true => exact False.elim (hfr hc)
        have hgood' := s2Good_skip hgood hidx_ge hfr_false
          (hskip_geom B idx rec hidx_ge hfr_false hgood)
        simp only [scanFromSmallestLabeled]
        rw [if_neg hidx_ge, if_neg (by simpa [hfr_false])]
        apply ih
        · exact hgood'
        · omega

private lemma s2_labeled_scan_records_perm_easyLabels_of_geometric
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    (hdelete_geom :
      let labeled := processInsertionsLabeled ν A_init
      ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        S2Good (easyMS labeled) labeled B idx rec →
          NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx ∧
          AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
          FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx)
    (hskip_geom :
      let labeled := processInsertionsLabeled ν A_init
      ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
        S2Good (easyMS labeled) labeled B idx rec →
          FrontierFRImpliesEasy B (idx + 1)) :
    let labeled := processInsertionsLabeled ν A_init
    (scanFromSmallestLabeled (forget labeled).length.succ labeled 0 []).2.Perm
      (easyLabels labeled) := by
  intro labeled
  have hgood0 : S2Good (easyMS labeled) labeled labeled 0 [] :=
    s2Good_initial_processInsertionsLabeled A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hfuel : (forget labeled).length.succ ≥ labeled.length - 0 := by
    simp [length_forget]
  have hms := recMS_scanFromSmallestLabeled_eq_target_of_S2Good_geometric
    (target := easyMS labeled) (start := labeled)
    hdelete_geom hskip_geom (forget labeled).length.succ labeled 0 [] hgood0 hfuel
  apply list_perm_of_coe_multiset_eq
  simpa [recMS, easyMS] using hms

/-! ### Phase A: Process-trajectory geometric invariants. -/

/-- Trajectory invariant: every hard FR part has an easy at the immediately
following position. -/
private def HardHasSupportingEasy (B : List Labeled) : Prop :=
  ∀ (i : ℕ) (hi : i < B.length) (p : ℕ),
    (B[i]'hi).origin = some (p, InsertionKind.hard) →
    isFlatRemovableBool (forget B) i = true →
      ∃ (hi1 : i + 1 < B.length),
        (B[i+1]'hi1).origin.map Prod.snd = some InsertionKind.easy

/-- Trajectory invariant: deleting the current easy frontier preserves FR of
remaining unchecked easies. -/
private def EasyFRPreservedUnderFrontierDelete
    (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (j : ℕ) (hj : j < (B.eraseIdx (B.length - 1 - idx)).length),
    j < (B.eraseIdx (B.length - 1 - idx)).length - idx →
      ((B.eraseIdx (B.length - 1 - idx))[j]'hj).origin.map Prod.snd =
        some InsertionKind.easy →
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) j = true

/-- Strengthening: existing labels' ranks dominate every remaining insertion size.

Carried alongside `HardHasSupportingEasy` so that the per-step preservation
argument can rule out adjacency cases that would otherwise be unprovable
(e.g. a new hard inserted exactly at `h_old + 1` between an old hard and its
supporting easy). The bound is `≥` because the supporting-easy adjacency
contradiction needs `q ≤ q_old`. -/
private def LabelSizesDominateTail (A : List Labeled) (tail : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < A.length) (p : ℕ) (k : InsertionKind),
    (A[i]'hi).origin = some (p, k) →
      ∀ q ∈ tail, p ≥ q

/-- Combined process invariant carried through the ν-induction.
* `support`: every hard FR part has an easy at the immediately following position.
* `sizeBound`: existing labels' ranks dominate every remaining insertion size.
* `hardValueMod3`: every hard part's value is a multiple of 3 (preserved
  through both hard and easy insertions since raises are +3 and easy
  insertions don't touch existing values). -/
private structure HardSupportProcessInv (A : List Labeled) (tail : List ℕ) :
    Prop where
  support : HardHasSupportingEasy A
  sizeBound : LabelSizesDominateTail A tail
  hardValueMod3 : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
    (A[i]'hi).origin = some (p, InsertionKind.hard) →
    (A[i]'hi).value % 3 = 0

/-- S3 rank: number of core-origin positions in the prefix.  Stable under skips
even when equal core values occur. -/
private def corePrefixAbove (A : List Labeled) (i : ℕ) : ℕ :=
  (A.take i).countP (fun y => y.origin = none)

private def HardRankAtS3 (A : List Labeled) (i p : ℕ) : Prop :=
  ∃ hi : i < A.length,
    (A[i]'hi).origin = some (p, .hard) ∧
    (A[i]'hi).value + 3 * corePrefixAbove A i = 3 * p

/-- Trajectory rank invariant for `processInsertionsLabeled ν A_init`: every hard
label has a `HardRankAtS3` witness in the current state. -/
private def ProcessHardRankS3Inv (A : List Labeled) : Prop :=
  ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
    (A[i]'hi).origin = some (p, InsertionKind.hard) →
    HardRankAtS3 A i p

private lemma corePrefixAbove_succ_eq_of_not_core
    {A : List Labeled} {k : ℕ} (hk : k < A.length)
    (hk_not_core : (A[k]'hk).origin ≠ none) :
    corePrefixAbove A (k + 1) = corePrefixAbove A k := by
  unfold corePrefixAbove
  rw [List.take_succ_eq_append_getElem hk, List.countP_append]
  have : ([A[k]'hk]).countP (fun y : Labeled => decide (y.origin = none)) = 0 := by
    simp [hk_not_core]
  rw [this]; simp

private lemma corePrefixAbove_eraseIdx_of_le
    {A : List Labeled} {k i : ℕ} (h : i ≤ k) :
    corePrefixAbove (A.eraseIdx k) i = corePrefixAbove A i := by
  unfold corePrefixAbove
  rw [List.take_eraseIdx_eq_take_of_le A i k h]

/-- `corePrefixAbove` shifts by one index when crossing the erased non-core element.
For `i > k` with `A[k]` not core, the prefix-take after erasure has the same core
count as the original prefix-take of length `i + 1`. -/
private lemma corePrefixAbove_eraseIdx_of_gt
    {A : List Labeled} {k : ℕ} (hk : k < A.length)
    (hk_not_core : (A[k]'hk).origin ≠ none)
    {i : ℕ} (hi : k < i) (hi_le : i + 1 ≤ A.length) :
    corePrefixAbove (A.eraseIdx k) i = corePrefixAbove A (i + 1) := by
  unfold corePrefixAbove
  -- Decompose A.eraseIdx k = A.take k ++ A.drop (k+1).
  have hdecomp : A.eraseIdx k = A.take k ++ A.drop (k + 1) :=
    List.eraseIdx_eq_take_drop_succ A k
  rw [hdecomp]
  -- Length facts.
  have hlen_take_k : (A.take k).length = k := by
    rw [List.length_take]; omega
  have hlen_drop : (A.drop (k + 1)).length = A.length - (k + 1) := by
    rw [List.length_drop]
  -- (A.take k ++ A.drop (k+1)).take i = A.take k ++ (A.drop (k+1)).take (i - k).
  have htake_app : (A.take k ++ A.drop (k + 1)).take i =
      A.take k ++ (A.drop (k + 1)).take (i - k) := by
    rw [List.take_append]
    congr 1
    · apply List.take_of_length_le; rw [hlen_take_k]; omega
    · rw [hlen_take_k]
  rw [htake_app]
  -- A.take (i+1) = A.take k ++ A[k] :: (A.drop (k+1)).take (i-k).
  have htake_succ : A.take (i + 1) = A.take k ++ A[k]'hk :: (A.drop (k + 1)).take (i - k) := by
    have h1 : A.take (i + 1) = A.take k ++ (A.drop k).take (i + 1 - k) := by
      conv_lhs => rw [show (i + 1 : ℕ) = k + (i + 1 - k) from by omega]
      exact List.take_add
    have h2 : A.drop k = A[k]'hk :: A.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h1, h2]
    have h3 : i + 1 - k = (i - k) + 1 := by omega
    rw [h3, List.take_succ_cons]
  rw [htake_succ]
  -- countP append+cons decomposition.
  simp only [List.countP_append, List.countP_cons]
  -- Term `if p A[k] = true then 1 else 0` simplifies to 0 via hk_not_core.
  have hp_at_k : (fun y : Labeled => decide (y.origin = none)) (A[k]'hk) = false := by
    simp [hk_not_core]
  simp [hp_at_k]

/-- `ProcessHardRankS3Inv` is preserved under erasure of a non-core element.
This is the key transport lemma: when S2 erases an easy-labeled element (whose
origin is `some (_, .easy)`, hence ≠ none), the rank witnesses for all surviving
hard labels transport correctly. -/
private lemma processHardRankS3Inv_eraseIdx_of_not_core
    {A : List Labeled} {k : ℕ} (hk : k < A.length)
    (hk_not_core : (A[k]'hk).origin ≠ none)
    (hInv : ProcessHardRankS3Inv A) :
    ProcessHardRankS3Inv (A.eraseIdx k) := by
  intro i hi p hhard
  have hlen_e : (A.eraseIdx k).length = A.length - 1 := List.length_eraseIdx_of_lt hk
  by_cases hik : i < k
  · -- i < k case: the prefix is untouched, value & origin preserved.
    have hi_A : i < A.length := by omega
    have heq : (A.eraseIdx k)[i]'hi = A[i]'hi_A := by
      rw [List.getElem_eraseIdx]; simp [hik]
    rw [heq] at hhard
    obtain ⟨_, horg_old, hsum_old⟩ := hInv i hi_A p hhard
    refine ⟨hi, ?_, ?_⟩
    · rw [heq]; exact horg_old
    · rw [heq]
      rw [corePrefixAbove_eraseIdx_of_le (Nat.le_of_lt hik)]
      exact hsum_old
  · -- i ≥ k case: shifted from position i+1 in A.
    push_neg at hik
    have hi1_A : i + 1 < A.length := by rw [hlen_e] at hi; omega
    have heq : (A.eraseIdx k)[i]'hi = A[i+1]'hi1_A := by
      rw [List.getElem_eraseIdx]; simp [show ¬ i < k from Nat.not_lt.mpr hik]
    rw [heq] at hhard
    obtain ⟨_, horg_old, hsum_old⟩ := hInv (i+1) hi1_A p hhard
    refine ⟨hi, ?_, ?_⟩
    · rw [heq]; exact horg_old
    · rw [heq]
      have h_cpa : corePrefixAbove (A.eraseIdx k) i = corePrefixAbove A (i + 1) := by
        by_cases hi_eq_k : i = k
        · rw [hi_eq_k, corePrefixAbove_eraseIdx_of_le (le_refl k),
              corePrefixAbove_succ_eq_of_not_core hk hk_not_core]
        · exact corePrefixAbove_eraseIdx_of_gt hk hk_not_core (by omega) (Nat.le_of_lt hi1_A)
      rw [h_cpa]
      exact hsum_old

/-- Scan-chain preservation of `ProcessHardRankS3Inv` under `scanFromSmallestLabeled`,
parameterized on the assumption that cores have value not divisible by 3 (which
guarantees no core is erased — FR requires `value % 3 = 0`).  Cores never get
erased because they fail the FR check, so each erase is on a non-core element. -/
private lemma processHardRankS3Inv_scanFromSmallestLabeled
    (fuel : ℕ) :
    ∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ),
      ProcessHardRankS3Inv A →
      (∀ (j : ℕ) (hj : j < A.length),
          (A[j]'hj).origin = none → (A[j]'hj).value % 3 ≠ 0) →
      ProcessHardRankS3Inv (scanFromSmallestLabeled fuel A idx rec).1 := by
  induction fuel with
  | zero =>
    intro A idx rec hInv _hCore
    simp only [scanFromSmallestLabeled]
    exact hInv
  | succ fuel' ih =>
    intro A idx rec hInv hCore
    simp only [scanFromSmallestLabeled]
    split
    · exact hInv
    · split
      · next hfr =>
        -- Erase case: derive that erased element is non-core.
        rename_i hidx_ge
        push_neg at hidx_ge
        set actualIdx := A.length - 1 - idx with hact_def
        have hact : actualIdx < A.length := by
          rw [hact_def]; omega
        -- Extract value % 3 = 0 from FR.
        have hmod : (A[actualIdx]'hact).value % 3 = 0 := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          have hf := hfr.1.2
          have hval_eq : (forget A)[actualIdx]! = (A[actualIdx]'hact).value := by
            rw [getElem!_pos (forget A) actualIdx (by rw [length_forget]; omega)]
            simp [forget, List.getElem_map]
          rw [hval_eq] at hf
          exact hf
        -- Erased element is non-core (origin ≠ none).
        have hnot_core : (A[actualIdx]'hact).origin ≠ none := by
          intro hcore
          exact hCore actualIdx hact hcore hmod
        -- Apply per-step preservation.
        have hInv' : ProcessHardRankS3Inv (A.eraseIdx actualIdx) :=
          processHardRankS3Inv_eraseIdx_of_not_core hact hnot_core hInv
        -- coreNotDiv survives erase.
        have hCore' : ∀ (j : ℕ) (hj : j < (A.eraseIdx actualIdx).length),
            ((A.eraseIdx actualIdx)[j]'hj).origin = none →
            ((A.eraseIdx actualIdx)[j]'hj).value % 3 ≠ 0 := by
          intro j hj horg
          have hlen : (A.eraseIdx actualIdx).length = A.length - 1 :=
            List.length_eraseIdx_of_lt hact
          rw [List.getElem_eraseIdx] at horg ⊢
          by_cases hjk : j < actualIdx
          · simp only [hjk, ↓reduceDIte] at horg ⊢
            exact hCore j (by omega) horg
          · simp only [hjk, ↓reduceDIte] at horg ⊢
            exact hCore (j+1) (by rw [hlen] at hj; omega) horg
        exact ih (A.eraseIdx actualIdx) idx _ hInv' hCore'
      · -- Skip case: A unchanged.
        exact ih A (idx + 1) rec hInv hCore

private lemma S2Reach_flat
    {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach start B idx rec)
    (hflat_start : IsThreeFlat (forget start)) :
    IsThreeFlat (forget B) := by
  refine S2Reach.rec (motive := fun B _idx _rec _ => IsThreeFlat (forget B))
    ?init ?eraseCase ?skipCase hreach
  · exact hflat_start
  · intro B' idx' actualIdx' rec' hidx hactual hfr hprev ih
    have h_fe : forget (B'.eraseIdx actualIdx') = (forget B').eraseIdx actualIdx' := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    unfold isFlatRemovableBool at hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
    exact isThreeFlatBool_implies' _ hfr.2
  · intro B' idx' actualIdx' rec' hidx hactual hnfr hprev ih
    exact ih

/-- Easy-label values are preserved along arbitrary `S2Reach` prefixes.

The S2 phase only erases elements; any easy-labeled survivor in a reachable
state is literally an element of the labeled insertion output, where
`processInsertionsLabeled_easy_value_eq` gives value `3*p`. -/
private lemma S2Reach_easy_value_eq
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (j : ℕ) (hj : j < B.length) (p : ℕ)
    (heasy : (B[j]'hj).origin = some (p, InsertionKind.easy)) :
    (B[j]'hj).value = 3 * p := by
  have hmem : B[j]'hj ∈ B := List.getElem_mem hj
  have hmem_start := S2Reach.mem_start hreach hmem
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem_start
  have heasy_start :
      ((processInsertionsLabeled ν A_init)[k]'hk).origin =
        some (p, InsertionKind.easy) := by
    rw [hget]
    exact heasy
  have hval_start :=
    processInsertionsLabeled_easy_value_eq A_init ν hA_flat hA_clean hν_sort
      k hk p heasy_start
  rw [hget] at hval_start
  exact hval_start

private lemma countP_eq_length_of_all {α : Type*} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = true) → xs.countP p = xs.length
  | [], _ => by simp
  | x :: xs, h => by
      have hx : p x = true := h x (by simp)
      have hxs : ∀ y ∈ xs, p y = true := by
        intro y hy
        exact h y (by simp [hy])
      simp [List.countP_cons, hx, countP_eq_length_of_all p xs hxs]

private lemma corePrefixAbove_eq_of_all_core
    {A : List Labeled} {h : ℕ} (hh : h ≤ A.length)
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < h → (A[j]'hj).origin = none) :
    corePrefixAbove A h = h := by
  unfold corePrefixAbove
  have hall : ∀ x ∈ A.take h, (fun y : Labeled => decide (y.origin = none)) x = true := by
    intro x hx
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
    have hlen_take : (A.take h).length = h := by rw [List.length_take]; omega
    have hj_bound : j < h := by rw [hlen_take] at hj; exact hj
    have hjA : j < A.length := by omega
    have hgetA : (A.take h)[j]'hj = A[j]'hjA := List.getElem_take
    rw [← hget, hgetA]
    simp [hprefix j hjA hj_bound]
  rw [countP_eq_length_of_all _ _ hall, List.length_take]
  omega

/-- `corePrefixAbove A i ≤ i` always (counting cores in `A.take i` of length `≤ i`). -/
private lemma corePrefixAbove_le {A : List Labeled} (i : ℕ) :
    corePrefixAbove A i ≤ i := by
  unfold corePrefixAbove
  have h1 : (A.take i).countP (fun y : Labeled => decide (y.origin = none)) ≤
      (A.take i).length := List.countP_le_length
  have h2 : (A.take i).length ≤ i := by rw [List.length_take]; omega
  omega

/-- `corePrefixAbove` under insertion of a non-core element: prefix `i ≤ pos`
is unchanged. -/
private lemma corePrefixAbove_insertIdx_of_le
    {A : List Labeled} {pos : ℕ} (newPart : Labeled)
    {i : ℕ} (h : i ≤ pos) :
    corePrefixAbove (A.insertIdx pos newPart) i = corePrefixAbove A i := by
  unfold corePrefixAbove
  rw [List.take_insertIdx_eq_take_of_le A newPart i pos h]

/-- `corePrefixAbove` under insertion of a non-core element: for `i > pos`,
the prefix-take shifts by one across the inserted element.
Proved via the `eraseIdx_insertIdx_self` adjunction: `A = (A.insertIdx pos newPart).eraseIdx pos`,
then `corePrefixAbove_eraseIdx_of_gt` gives the relation. -/
private lemma corePrefixAbove_insertIdx_of_gt
    {A : List Labeled} {pos : ℕ} (hpos : pos ≤ A.length)
    {newPart : Labeled} (hnewPart_not_core : newPart.origin ≠ none)
    {i : ℕ} (hi : pos < i) (hi_le : i ≤ A.length + 1) :
    corePrefixAbove (A.insertIdx pos newPart) i = corePrefixAbove A (i - 1) := by
  have hlen_r : (A.insertIdx pos newPart).length = A.length + 1 := by
    rw [List.length_insertIdx]; simp [hpos]
  have hpos_r : pos < (A.insertIdx pos newPart).length := by rw [hlen_r]; omega
  have hr_at_pos_not_core : ((A.insertIdx pos newPart)[pos]'hpos_r).origin ≠ none := by
    rw [Hints.origin_insertIdx_at A pos newPart hpos_r]
    exact hnewPart_not_core
  have hera : (A.insertIdx pos newPart).eraseIdx pos = A :=
    List.eraseIdx_insertIdx_self newPart
  -- Apply corePrefixAbove_eraseIdx_of_gt: for j > pos with j+1 ≤ r.length,
  -- corePrefixAbove (r.eraseIdx pos) j = corePrefixAbove r (j+1).
  by_cases hj_gt : pos < i - 1
  · -- i > pos + 1
    have h := corePrefixAbove_eraseIdx_of_gt (A := A.insertIdx pos newPart)
      hpos_r hr_at_pos_not_core hj_gt (by rw [hlen_r]; omega)
    rw [hera] at h
    have hsucc : i - 1 + 1 = i := by omega
    rw [hsucc] at h
    exact h.symm
  · -- i = pos + 1
    push_neg at hj_gt
    have hi_eq : i = pos + 1 := by omega
    rw [hi_eq]
    -- cpa r (pos + 1) = cpa A pos
    show corePrefixAbove (A.insertIdx pos newPart) (pos + 1) = corePrefixAbove A pos
    unfold corePrefixAbove
    rw [List.take_succ_eq_append_getElem hpos_r]
    rw [List.countP_append]
    have htake_eq : (A.insertIdx pos newPart).take pos = A.take pos :=
      List.take_insertIdx_eq_take_of_le A newPart pos pos (le_refl pos)
    rw [htake_eq]
    have hp_zero : ([(A.insertIdx pos newPart)[pos]'hpos_r]).countP
        (fun y : Labeled => decide (y.origin = none)) = 0 := by
      simp [Hints.origin_insertIdx_at A pos newPart hpos_r, hnewPart_not_core]
    rw [hp_zero]; simp

/-- The "raise" operation in hard insertion preserves origins.  Hence
`corePrefixAbove` is unchanged across the raise. -/
private lemma corePrefixAbove_raised_eq (A : List Labeled) (h i : ℕ) :
    corePrefixAbove
      (A.zipIdx.map (fun (x : Labeled × ℕ) =>
        if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)) i =
    corePrefixAbove A i := by
  unfold corePrefixAbove
  set raised : List Labeled :=
    A.zipIdx.map (fun (x : Labeled × ℕ) =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised_def
  -- Reduce countP to countP on origins via List.countP_map.
  have hp_eq : (fun y : Labeled => decide (y.origin = none)) =
      (fun o : Option (ℕ × InsertionKind) => decide (o = none)) ∘ (·.origin) := rfl
  rw [hp_eq, ← List.countP_map, ← List.countP_map]
  -- Now reduce to: (raised.take i .map ·.origin).countP = (A.take i .map ·.origin).countP.
  -- Show raised.map (·.origin) = A.map (·.origin) (origins preserved by raise).
  have horigins : raised.map (·.origin) = A.map (·.origin) := by
    rw [hraised_def]
    simp only [List.map_map]
    have : (fun x : Labeled × ℕ =>
        (if x.2 < h then { value := x.1.value + 3, origin := x.1.origin : Labeled } else x.1).origin) =
        (·.origin) ∘ (·.1) := by
      funext ⟨x, j⟩
      simp only [Function.comp]
      split <;> rfl
    rw [show ((fun x : Labeled => x.origin) ∘
        (fun (x : Labeled × ℕ) =>
          if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)) =
        ((·.origin) ∘ Prod.fst) from this]
    rw [← List.map_map]
    -- (A.zipIdx).map Prod.fst = A
    simp [List.map_zipIdx, List.zipIdx_map_fst]
  -- map and take commute.
  rw [List.map_take, List.map_take, horigins]

/-- Easy insertion preserves `ProcessHardRankS3Inv`: existing hards keep their
rank witness because the new easy is non-core (so cpa shifts cleanly across it). -/
private lemma tryEasyInsertionLabeled_preserves_hardRankS3Inv
    {A : List Labeled} {q : ℕ} {r : List Labeled}
    (hRank : ProcessHardRankS3Inv A)
    (he : tryEasyInsertionLabeled A q = some r) :
    ProcessHardRankS3Inv r := by
  intro i hi p hhard
  unfold tryEasyInsertionLabeled at he
  simp only at he
  split_ifs at he with hcond
  set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
  set pos := (A.takeWhile (·.value ≥ 3 * q)).length
  have hres : A.insertIdx pos newPart = r := Option.some.inj he
  have hpos_le : pos ≤ A.length :=
    List.IsPrefix.length_le (List.takeWhile_prefix _)
  have hlen_r : r.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx]; simp [hpos_le]
  have hnewPart_nc : newPart.origin ≠ none := by simp [newPart]
  subst hres
  rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
  · -- i < pos: hard in r at i comes from hard in A at i.
    have hpre : i < A.length := by omega
    have horig := Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
    rw [horig] at hhard
    obtain ⟨_, _, hsum⟩ := hRank i hpre p hhard
    refine ⟨hi, ?_, ?_⟩
    · rw [horig]; exact hhard
    · have hval_eq : ((A.insertIdx pos newPart)[i]'hi).value = (A[i]'hpre).value := by
        rw [List.getElem_insertIdx]; simp [hlt]
      rw [hval_eq, corePrefixAbove_insertIdx_of_le newPart (Nat.le_of_lt hlt)]
      exact hsum
  · -- i = pos: r[pos] = newPart (easy). Contradicts hhard.
    subst heq
    have horig := Hints.origin_insertIdx_at A pos newPart hi
    rw [horig] at hhard
    simp [newPart] at hhard
  · -- i > pos: hard in r at i comes from hard in A at i-1.
    have hpre : i - 1 < A.length := by omega
    have horig := Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
    rw [horig] at hhard
    obtain ⟨_, _, hsum⟩ := hRank (i-1) hpre p hhard
    refine ⟨hi, ?_, ?_⟩
    · rw [horig]; exact hhard
    · have hval_eq : ((A.insertIdx pos newPart)[i]'hi).value = (A[i-1]'hpre).value := by
        rw [List.getElem_insertIdx]
        have hnotlt : ¬ (i < pos) := by omega
        have hnoteq : i ≠ pos := by omega
        simp [hnotlt, hnoteq]
      rw [hval_eq, corePrefixAbove_insertIdx_of_gt hpos_le hnewPart_nc hgt (by omega)]
      exact hsum

/-- Substantive geometric lemma: after a successful `tryHardInsertionLabeled A q h = some r`,
the prefix `A[0..h-1]` must be all-core.  A label at `j < h` would have value bounded
below by `3*(q-j)` (hard via rank) or `3*q` (easy via easyValue + sizeBound), but
upper-bound + descent force `value < 3*q - h - 2 - 2*j`, leading to contradiction. -/
private lemma tryHardInsertionLabeled_prefix_all_core
    {A : List Labeled} {q h : ℕ} {r : List Labeled}
    (hflat : IsThreeFlat (forget A))
    (hRank : ProcessHardRankS3Inv A)
    (hEasy : ∀ (i : ℕ) (hi : i < A.length) (r' : ℕ),
      (A[i]'hi).origin = some (r', InsertionKind.easy) → (A[i]'hi).value = 3 * r')
    (hBound : ∀ (i : ℕ) (hi : i < A.length) (r' : ℕ) (k : InsertionKind),
      (A[i]'hi).origin = some (r', k) → r' ≥ q)
    (htry : tryHardInsertionLabeled A q h = some r) :
    ∀ (j : ℕ) (hj : j < A.length), j < h → (A[j]'hj).origin = none := by
  intro j hj hjh
  -- Unlabeled try succeeds; extract guard and admissibility facts.
  have hforget := forget_tryHardInsertionLabeled A q h
  rw [htry] at hforget
  have h_unl_some : tryHardInsertion (forget A) q h = some (forget r) := by
    simp only [Option.map_some] at hforget
    exact hforget.symm
  have h_unl_isSome : (tryHardInsertion (forget A) q h).isSome := by
    rw [h_unl_some]; rfl
  -- h ≥ 1 (since j < h and j ≥ 0).
  have hh_pos : 1 ≤ h := by omega
  -- h ≤ A.length from the guard.
  have hh_le_A : h ≤ A.length := by
    unfold tryHardInsertionLabeled at htry
    simp only [ge_iff_le] at htry
    split_ifs at htry with hf
    push_neg at hf; exact hf.2
  have hh_le_forget : h ≤ (forget A).length := by rw [length_forget]; exact hh_le_A
  -- Geometric bound: A[j].value < 3*q - h - 2 - 2*j (via upper_bound + descent).
  have hub := tryHardInsertion_upper_bound_early h_unl_isSome hh_pos hh_le_forget
  have hh1_lt_A : h - 1 < A.length := by omega
  have hub_A : (A[h-1]'hh1_lt_A).value < 3 * q - 3 * h := by
    have hf : (forget A)[h-1]'(by rw [length_forget]; omega) = (A[h-1]'hh1_lt_A).value := by
      simp [forget, List.getElem_map]
    rw [← hf]; exact hub
  have hdesc := threeFlat_descent_bound_early hflat (show j ≤ h - 1 by omega)
    (by rw [length_forget]; omega)
  have hdesc_A : (A[j]'hj).value ≤ (A[h-1]'hh1_lt_A).value + 2 * (h - 1 - j) := by
    have hf1 : (forget A)[j]'(by rw [length_forget]; exact hj) = (A[j]'hj).value := by
      simp [forget, List.getElem_map]
    have hf2 : (forget A)[h-1]'(by rw [length_forget]; omega) =
        (A[h-1]'hh1_lt_A).value := by
      simp [forget, List.getElem_map]
    rw [hf1, hf2] at hdesc
    exact hdesc
  -- Case on the origin.
  match horg : (A[j]'hj).origin with
  | none => rfl
  | some (p, kind) =>
    exfalso
    cases kind with
    | easy =>
      have hval := hEasy j hj p horg
      have hp_ge := hBound j hj p .easy horg
      omega
    | hard =>
      obtain ⟨_, _, hsum⟩ := hRank j hj p horg
      have hp_ge := hBound j hj p .hard horg
      have hcpa_le := corePrefixAbove_le (A := A) j
      omega
/-- Hard insertion preserves `ProcessHardRankS3Inv`.  The new hard at `h` has
rank `q` via the all-core prefix (cpa = h, value = 3(q-h), sum = 3q).  Existing
hards at positions `j ≥ h` shift to `j+1` in `r` with cpa preserved (the
inserted slot is hard, not core, and the raise preserves origin).  Existing
hards at positions `j < h` are ruled out by `prefix_all_core`. -/
private lemma tryHardInsertionLabeled_preserves_hardRankS3Inv
    {A : List Labeled} {q h : ℕ} {r : List Labeled}
    (hflat : IsThreeFlat (forget A))
    (hRank : ProcessHardRankS3Inv A)
    (hEasy : ∀ (i : ℕ) (hi : i < A.length) (r' : ℕ),
      (A[i]'hi).origin = some (r', InsertionKind.easy) → (A[i]'hi).value = 3 * r')
    (hBound : ∀ (i : ℕ) (hi : i < A.length) (r' : ℕ) (k : InsertionKind),
      (A[i]'hi).origin = some (r', k) → r' ≥ q)
    (htry : tryHardInsertionLabeled A q h = some r) :
    ProcessHardRankS3Inv r := by
  have hprefix_core := tryHardInsertionLabeled_prefix_all_core hflat hRank hEasy hBound htry
  -- Extract structure of r via subst.
  have htry_orig : tryHardInsertionLabeled A q h = some r := htry
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf had
  push_neg at hf
  obtain ⟨hh_q, hh_A⟩ := hf
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised_def
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩ with hnewPart_def
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry
  subst hres
  -- Now r ≡ raised.insertIdx h newPart everywhere.
  have hlen_raised : raised.length = A.length := by simp [hraised_def]
  have hlen_r : (raised.insertIdx h newPart).length = A.length + 1 := by
    rw [List.length_insertIdx]; simp [hlen_raised, hh_A]
  have hnewPart_nc : newPart.origin ≠ none := by simp [hnewPart_def]
  -- Helper: for k < h, r[k] is raised[k] which has A[k].origin.
  have hraised_origin : ∀ (k : ℕ) (hk : k < A.length) (hkh : k < h),
      ((raised.insertIdx h newPart)[k]'(by rw [hlen_r]; omega)).origin = (A[k]'hk).origin := by
    intro k hk hkh
    rw [List.getElem_insertIdx]
    simp [hkh, hraised_def, List.getElem_map, List.getElem_zipIdx]
  intro i hi p hhard
  obtain h1 | h2 :=
    tryHardInsertionLabeled_hard_pos_pullback A q h (raised.insertIdx h newPart)
      htry_orig i hi p hhard
  · -- New hard at h, i.e., i = h, p = q.
    obtain ⟨hi_eq, hp_eq, hval⟩ := h1
    have hh_lt_r : h < (raised.insertIdx h newPart).length := by rw [hlen_r]; omega
    -- Show cpa r h = h via prefix all-core.
    have hr_prefix_core : ∀ (k : ℕ) (hk : k < (raised.insertIdx h newPart).length),
        k < h → ((raised.insertIdx h newPart)[k]'hk).origin = none := by
      intro k hk hkh
      have hkA : k < A.length := by omega
      rw [hraised_origin k hkA hkh]
      exact hprefix_core k hkA hkh
    have hcpa_h : corePrefixAbove (raised.insertIdx h newPart) h = h :=
      corePrefixAbove_eq_of_all_core (by rw [hlen_r]; omega) hr_prefix_core
    refine ⟨hi, ?_, ?_⟩
    · exact hhard
    · -- Show: (r[i]).value + 3 * cpa r i = 3 * p.
      have hcpa_i : corePrefixAbove (raised.insertIdx h newPart) i = h := by
        rw [show i = h from hi_eq]; exact hcpa_h
      rw [hval, hcpa_i, hp_eq]
      omega
  · -- Existing hard at j.
    obtain ⟨j, hj, hi_eq, hjorig, hval⟩ := h2
    by_cases hjh : j < h
    · exfalso
      have := hprefix_core j hj hjh
      rw [this] at hjorig; cases hjorig
    · push_neg at hjh
      have hi_eq' : i = j + 1 := by
        simp [show ¬ j < h from Nat.not_lt.mpr hjh] at hi_eq; exact hi_eq
      -- Value preserved.
      have hval_eq : ((raised.insertIdx h newPart)[i]'hi).value = (A[j]'hj).value := by
        rw [hval]; simp [show ¬ j < h from Nat.not_lt.mpr hjh]
      -- cpa (raised.insertIdx h newPart) i = cpa A j.
      have hh_le_raised : h ≤ raised.length := by rw [hlen_raised]; exact hh_A
      have hcpa_eq : corePrefixAbove (raised.insertIdx h newPart) i = corePrefixAbove A j := by
        rw [hi_eq']
        rw [corePrefixAbove_insertIdx_of_gt hh_le_raised hnewPart_nc (by omega)
              (by rw [hlen_raised]; omega)]
        rw [show (j + 1 - 1 : ℕ) = j from by omega]
        exact corePrefixAbove_raised_eq A h j
      obtain ⟨_, _, hsum⟩ := hRank j hj p hjorig
      refine ⟨hi, hhard, ?_⟩
      rw [hval_eq, hcpa_eq]
      exact hsum

/-- FR transfer through easy insertion (reverse direction, "before" case).

When `r = xs.insertIdx pos (3 * q)` is 3-flat, `xs` is 3-flat, and the FR
query position `i` satisfies `i + 1 < pos` (the seam at i lives strictly
before the insertion bridge), then FR at `i` in `r` transfers down to FR
at `i` in `xs`.

The seam gap `xs[i-1] - xs[i+1]` in `xs.eraseIdx i` equals the seam gap
`r[i-1] - r[i+1]` in `r.eraseIdx i` (since `i-1, i+1 < pos`). All other
gaps either coincide directly with `xs`'s gaps or are derivable from
`xs` being 3-flat. -/
private lemma easyInsert_FR_transfer_before
    (xs : List ℕ) (q pos i : ℕ)
    (hpos_le : pos ≤ xs.length)
    (hflat_xs : isThreeFlatBool xs = true)
    (hi : i < xs.length)
    (hi1_lt : i + 1 < pos)
    (hFR_r : isFlatRemovableBool (xs.insertIdx pos (3 * q)) i = true) :
    isFlatRemovableBool xs i = true := by
  unfold isFlatRemovableBool at hFR_r ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hFR_r ⊢
  obtain ⟨⟨hi_lt_r, hmod_r⟩, hflat_erase_r⟩ := hFR_r
  have hlen_r : (xs.insertIdx pos (3 * q)).length = xs.length + 1 := by
    simp [List.length_insertIdx, hpos_le]
  have hi_pos_or : i = 0 ∨ 0 < i := Nat.eq_zero_or_pos i
  refine ⟨⟨hi, ?_⟩, ?_⟩
  · -- xs[i]! % 3 = 0 from r[i]! % 3 = 0 (since r[i] = xs[i] for i < pos)
    have hilt : i < pos := by omega
    have hi_lt_xs : i < xs.length := hi
    rw [getElem!_pos xs i hi_lt_xs]
    rw [getElem!_pos _ i hi_lt_r] at hmod_r
    have heq : (xs.insertIdx pos (3 * q))[i]'hi_lt_r = xs[i]'hi_lt_xs := by
      rw [List.getElem_insertIdx]; simp [hilt]
    rw [heq] at hmod_r
    exact hmod_r
  · -- isThreeFlatBool (xs.eraseIdx i) = true
    apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap xs i hi hflat_xs
    · -- gap: xs[i-1] - xs[i+1] < 3 when 0 < i, i + 1 < xs.length.
      intro hi_pos hi1_lt_xs
      have hflat_e := isThreeFlatBool_implies' _ hflat_erase_r
      obtain ⟨_, hgaps_e, _⟩ := hflat_e
      have hlen_e : ((xs.insertIdx pos (3 * q)).eraseIdx i).length = xs.length := by
        rw [List.length_eraseIdx_of_lt hi_lt_r]; omega
      have him1_in_e : i - 1 < ((xs.insertIdx pos (3 * q)).eraseIdx i).length := by
        rw [hlen_e]; omega
      have hi1_in_e : (i - 1) + 1 < ((xs.insertIdx pos (3 * q)).eraseIdx i).length := by
        rw [hlen_e]; omega
      have hgap_e := hgaps_e (i - 1) hi1_in_e
      have hi1_in_r : i + 1 < (xs.insertIdx pos (3 * q)).length := by rw [hlen_r]; omega
      have him1_in_r : i - 1 < (xs.insertIdx pos (3 * q)).length := by rw [hlen_r]; omega
      -- (r.eraseIdx i)[i-1] = r[i-1] (since i-1 < i)
      have herase_im1 :
          ((xs.insertIdx pos (3 * q)).eraseIdx i)[i - 1]'him1_in_e
            = (xs.insertIdx pos (3 * q))[i - 1]'him1_in_r := by
        rw [List.getElem_eraseIdx]; simp [show i - 1 < i from by omega]
      -- (r.eraseIdx i)[(i-1)+1] = r[(i-1)+1+1] = r[i+1] (since (i-1)+1 = i ≥ i)
      have herase_i1 :
          ((xs.insertIdx pos (3 * q)).eraseIdx i)[(i - 1) + 1]'hi1_in_e
            = (xs.insertIdx pos (3 * q))[i + 1]'hi1_in_r := by
        rw [List.getElem_eraseIdx]
        simp [show ¬((i - 1) + 1 < i) from by omega]
        congr 1; omega
      -- r[i-1] = xs[i-1] (since i-1 < pos)
      have hr_im1 : (xs.insertIdx pos (3 * q))[i - 1]'him1_in_r = xs[i - 1]'(by omega) := by
        rw [List.getElem_insertIdx]; simp [show i - 1 < pos from by omega]
      -- r[i+1] = xs[i+1] (since i+1 < pos)
      have hr_i1 : (xs.insertIdx pos (3 * q))[i + 1]'hi1_in_r = xs[i + 1]'hi1_lt_xs := by
        rw [List.getElem_insertIdx]; simp [show i + 1 < pos from by omega]
      rw [herase_im1, herase_i1, hr_im1, hr_i1] at hgap_e
      exact hgap_e
    · -- last: i + 1 = xs.length → 0 < i → xs[i-1] < 3
      -- This is impossible: i + 1 < pos ≤ xs.length, so i + 1 < xs.length.
      intro hi1_eq _
      exfalso; omega

/-- FR transfer through easy insertion (reverse direction, "after" case).

When `r = xs.insertIdx pos (3 * q)` is 3-flat, `xs` is 3-flat, and the pull-back
position `j` satisfies `pos < j` (so the corresponding position in `r` is
`j + 1 > pos + 1`), then FR at `j + 1` in `r` transfers to FR at `j` in `xs`.

The seam gap `xs[j-1] - xs[j+1]` in `xs.eraseIdx j` equals the seam gap
in `r.eraseIdx (j+1)` since `j - 1 > pos`. -/
private lemma easyInsert_FR_transfer_after
    (xs : List ℕ) (q pos j : ℕ)
    (hpos_le : pos ≤ xs.length)
    (hflat_xs : isThreeFlatBool xs = true)
    (hj : j < xs.length)
    (hj_gt : pos < j)
    (hFR_r : isFlatRemovableBool (xs.insertIdx pos (3 * q)) (j + 1) = true) :
    isFlatRemovableBool xs j = true := by
  unfold isFlatRemovableBool at hFR_r ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hFR_r ⊢
  obtain ⟨⟨hi_lt_r, hmod_r⟩, hflat_erase_r⟩ := hFR_r
  have hlen_r : (xs.insertIdx pos (3 * q)).length = xs.length + 1 := by
    simp [List.length_insertIdx, hpos_le]
  refine ⟨⟨hj, ?_⟩, ?_⟩
  · -- xs[j]! % 3 = 0 from r[j+1]! % 3 = 0 (r[j+1] = xs[j] for j+1 > pos)
    rw [getElem!_pos xs j hj]
    rw [getElem!_pos _ (j + 1) hi_lt_r] at hmod_r
    have heq : (xs.insertIdx pos (3 * q))[j + 1]'hi_lt_r = xs[j]'hj := by
      rw [List.getElem_insertIdx]
      simp [show ¬(j + 1 < pos) from by omega, show ¬(j + 1 = pos) from by omega]
    rw [heq] at hmod_r
    exact hmod_r
  · -- isThreeFlatBool (xs.eraseIdx j) = true
    apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap xs j hj hflat_xs
    · -- gap: xs[j-1] - xs[j+1] < 3
      intro hj_pos hj1_lt_xs
      have hflat_e := isThreeFlatBool_implies' _ hflat_erase_r
      obtain ⟨_, hgaps_e, _⟩ := hflat_e
      have hlen_e : ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length = xs.length := by
        rw [List.length_eraseIdx_of_lt hi_lt_r]; omega
      have hj_in_e' : j < ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length := by
        rw [hlen_e]; omega
      have hj1_in_e : j + 1 < ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length := by
        rw [hlen_e]; omega
      have hgap_e := hgaps_e j hj1_in_e
      have hj_in_r : j < (xs.insertIdx pos (3 * q)).length := by rw [hlen_r]; omega
      have hj2_in_r : j + 2 < (xs.insertIdx pos (3 * q)).length := by rw [hlen_r]; omega
      -- (r.eraseIdx (j+1))[j] = r[j] (since j < j+1)
      have herase_j :
          ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1))[j]'hj_in_e'
            = (xs.insertIdx pos (3 * q))[j]'hj_in_r := by
        rw [List.getElem_eraseIdx]; simp [show j < j + 1 from by omega]
      -- (r.eraseIdx (j+1))[j+1] = r[j+2] (since j+1 ≥ j+1)
      have herase_j1 :
          ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1))[j + 1]'hj1_in_e
            = (xs.insertIdx pos (3 * q))[j + 2]'hj2_in_r := by
        rw [List.getElem_eraseIdx]; simp [show ¬(j + 1 < j + 1) from by omega]
      -- r[j] = xs[j-1] (since j > pos)
      have hr_j : (xs.insertIdx pos (3 * q))[j]'hj_in_r = xs[j - 1]'(by omega) := by
        rw [List.getElem_insertIdx]
        simp [show ¬(j < pos) from by omega, show ¬(j = pos) from by omega]
      -- r[j+2] = xs[j+1] (since j+2 > pos)
      have hr_j2 : (xs.insertIdx pos (3 * q))[j + 2]'hj2_in_r = xs[j + 1]'hj1_lt_xs := by
        rw [List.getElem_insertIdx]
        simp [show ¬(j + 2 < pos) from by omega, show ¬(j + 2 = pos) from by omega]
      rw [herase_j, herase_j1, hr_j, hr_j2] at hgap_e
      exact hgap_e
    · -- last: j + 1 = xs.length case
      intro hj1_eq _
      -- r is 3-flat with r.last < 3. r.last is at position r.length - 1 = xs.length.
      -- (r.eraseIdx (j+1)) has length xs.length, its last index = j.
      -- (r.eraseIdx (j+1))[j] = r[j] = xs[j-1] (since j > pos).
      have hflat_e := isThreeFlatBool_implies' _ hflat_erase_r
      obtain ⟨_, _, hlast_e⟩ := hflat_e
      have hlen_e : ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length = xs.length := by
        rw [List.length_eraseIdx_of_lt hi_lt_r]; omega
      have hne : (xs.insertIdx pos (3 * q)).eraseIdx (j + 1) ≠ [] := by
        intro h
        have : ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length = 0 := by
          rw [h]; rfl
        rw [hlen_e] at this; omega
      have hlast_val := hlast_e hne
      rw [List.getLast_eq_getElem] at hlast_val
      -- The last position is xs.length - 1 = j (since hj1_eq says j + 1 = xs.length).
      -- Direct rewrite of element via getElem_eraseIdx + getElem_insertIdx.
      have hidx_lt_e : ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length - 1
          < ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length := by
        rw [hlen_e]; omega
      rw [List.getElem_eraseIdx] at hlast_val
      have hidx_lt_j1 : ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length - 1 < j + 1 := by
        rw [hlen_e]; omega
      simp [hidx_lt_j1] at hlast_val
      rw [List.getElem_insertIdx] at hlast_val
      have hidx_lt_pos : ¬ (((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length - 1 < pos) := by
        rw [hlen_e]; omega
      have hidx_ne_pos : ((xs.insertIdx pos (3 * q)).eraseIdx (j + 1)).length - 1 ≠ pos := by
        rw [hlen_e]; omega
      simp [hidx_lt_pos, hidx_ne_pos] at hlast_val
      -- hlast_val: xs[(r.eraseIdx (j+1)).length - 1 - 1] < 3, with the index = j - 1
      convert hlast_val using 2
      rw [hlen_e]; omega

/-- Admissibility extraction: a successful `tryHardInsertion A p h = some result`
implies the newly inserted part at position `h` is NOT flat-removable in `result`. -/
private lemma tryHardInsertion_admissibility_at_h
    {A : List ℕ} {p h : ℕ} {result : List ℕ}
    (hsome : tryHardInsertion A p h = some result) :
    isFlatRemovableBool result h = false := by
  simp only [tryHardInsertion] at hsome
  split at hsome
  · simp at hsome
  · split at hsome
    · next hcond =>
      have heq := Option.some.inj hsome.symm
      rw [heq]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      exact hcond.2
    · simp at hsome

/-- Labeled-side admissibility: the new hard at `h` is NOT flat-removable in `forget r`. -/
private lemma tryHardInsertionLabeled_admissibility_at_h
    {A : List Labeled} {q h : ℕ} {r : List Labeled}
    (hr : tryHardInsertionLabeled A q h = some r) :
    isFlatRemovableBool (forget r) h = false := by
  have hcomm := forget_tryHardInsertionLabeled A q h
  rw [hr] at hcomm
  simp only [Option.map_some] at hcomm
  exact tryHardInsertion_admissibility_at_h hcomm.symm

/-- Lower bound at the seam (h, h+1) in the result, from a successful
`tryHardInsertion`.  Mirrors `tryHardInsertion_upper_bound_early` on the other
seam.  Defined here (before its forward consumers) by copying the original
proof body that lives later in the file. -/
private lemma tryHardInsertion_lower_bound_early {A : List ℕ} {p h : ℕ}
    (hsuc : (tryHardInsertion A p h).isSome) (hlen : h < A.length) :
    A[h]'hlen > 3 * (p - h) - 3 := by
  unfold tryHardInsertion at hsuc
  split at hsuc
  · simp at hsuc
  · next hguard =>
    push_neg at hguard
    set raised := List.map (fun x : ℕ × ℕ => if x.2 < h then x.1 + 3 else x.1) A.zipIdx
    set result := List.insertIdx raised h (3 * (p - h))
    have hcond : isThreeFlatBool result = true := by
      simp only [result, raised] at hsuc ⊢
      split at hsuc
      · next hc =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        exact hc.1
      · simp at hsuc
    unfold isThreeFlatBool isPositivePartitionBool at hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcond
    obtain ⟨⟨⟨_, _⟩, hgaps⟩, _⟩ := hcond
    have hraised_len : raised.length = A.length := by
      simp [raised, List.length_map, List.length_zipIdx]
    have hresult_len : result.length = A.length + 1 := by
      simp only [result, List.length_insertIdx]
      split
      · omega
      · omega
    have hh_lt_result_sub : h < result.length - 1 := by omega
    have hgap_h := hgaps h hh_lt_result_sub
    rw [getElem!_pos result h (by omega), getElem!_pos result (h + 1) (by omega)] at hgap_h
    have hresult_h : result[h]'(by omega) = 3 * (p - h) := by
      simp only [result, List.getElem_insertIdx]
      split
      · next hlt => exact absurd hlt (Nat.lt_irrefl h)
      · split
        · rfl
        · next _ hne => exact absurd trivial hne
    have hresult_h1 : result[h + 1]'(by omega) = raised[h]'(by omega) := by
      simp only [result, List.getElem_insertIdx]
      split
      · next hlt => exfalso; omega
      · split
        · next _ heq => exfalso; omega
        · simp_all
    have hraised_h : raised[h]'(by omega) = A[h]'hlen := by
      simp only [raised]
      rw [List.getElem_map]
      simp only [List.getElem_zipIdx]
      simp
    rw [hresult_h, hresult_h1, hraised_h] at hgap_h
    omega

/-- From a successful `tryHardInsertion`, `h < A.length` (strict): if `h = A.length`
then the last position of the result is the newly inserted `3*(p-h)`, which would
violate the 3-flat last-element check. -/
private lemma tryHardInsertion_h_lt_len {A : List ℕ} {p h : ℕ} {result : List ℕ}
    (htry : tryHardInsertion A p h = some result) :
    h < A.length := by
  have h_isSome : (tryHardInsertion A p h).isSome := by rw [htry]; rfl
  unfold tryHardInsertion at htry
  split at htry
  · simp at htry
  · next hguard =>
    push_neg at hguard
    obtain ⟨hh_p, hh_A⟩ := hguard
    rcases lt_or_eq_of_le hh_A with hlt | heq
    · exact hlt
    · exfalso
      -- h = A.length: result.last = 3*(p-h), but result 3-flat requires last < 3.
      set raised := List.map (fun x : ℕ × ℕ => if x.2 < h then x.1 + 3 else x.1) A.zipIdx
        with hraised_def
      set newPart := 3 * (p - h)
      have hraised_len : raised.length = A.length := by
        simp [hraised_def]
      have hcond : isThreeFlatBool (raised.insertIdx h newPart) = true := by
        simp only [hraised_def, raised, newPart] at htry
        split_ifs at htry with hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        exact hc.1
      have hflat := isThreeFlatBool_implies' _ hcond
      obtain ⟨⟨_, _⟩, _, hlast⟩ := hflat
      have hlen_ins : (raised.insertIdx h newPart).length = A.length + 1 := by
        rw [List.length_insertIdx]; simp [hraised_len]; omega
      have hne : raised.insertIdx h newPart ≠ [] := by
        intro hh
        have : (raised.insertIdx h newPart).length = 0 := by rw [hh]; rfl
        omega
      have hlast_val := hlast hne
      rw [List.getLast_eq_getElem] at hlast_val
      have hidx_lt : (raised.insertIdx h newPart).length - 1 <
          (raised.insertIdx h newPart).length := by omega
      have hidx_eq : (raised.insertIdx h newPart).length - 1 = h := by
        rw [hlen_ins, heq]; omega
      have hh_idx_in : h < (raised.insertIdx h newPart).length := by omega
      have hidx_get : (raised.insertIdx h newPart)[
          (raised.insertIdx h newPart).length - 1]'hidx_lt =
          (raised.insertIdx h newPart)[h]'hh_idx_in := by
        congr 1
      rw [hidx_get] at hlast_val
      have hh_get : (raised.insertIdx h newPart)[h]'hh_idx_in = newPart := by
        rw [List.getElem_insertIdx]
        simp [show ¬(h < h) from Nat.lt_irrefl h]
      rw [hh_get] at hlast_val
      -- newPart = 3*(p-h), p > h means p - h ≥ 1, so newPart ≥ 3.
      have : 0 < p - h := by omega
      have : 3 ≤ newPart := by simp [newPart]; omega
      omega

/-- The insertion-time lower seam for a newly inserted hard.

After a successful hard insertion at positive height `h`, the raised left
neighbor at `h-1` is at least the unraised right neighbor at `h` plus `3`.
In the result list this is exactly the seam across the new hard:
`r[h-1].value >= r[h+1].value + 3`.  This is the local ancestor of the
hard/easy boundary seam used later in S2. -/
private lemma tryHardInsertionLabeled_new_hard_neighbor_lower_seam
    {A r : List Labeled} {q h : ℕ}
    (hflat : IsThreeFlat (forget A))
    (htry : tryHardInsertionLabeled A q h = some r)
    (hh_pos : 0 < h) :
    (r[h - 1]'(by
      have hforget := forget_tryHardInsertionLabeled A q h
      rw [htry] at hforget
      have h_unl_some : tryHardInsertion (forget A) q h = some (forget r) := by
        simp only [Option.map_some] at hforget
        exact hforget.symm
      have hh_lt_forget := tryHardInsertion_h_lt_len h_unl_some
      rw [length_forget] at hh_lt_forget
      have hlen_r : r.length = A.length + 1 := by
        unfold tryHardInsertionLabeled at htry
        simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
        split_ifs at htry with hf had
        push_neg at hf
        set raised : List Labeled :=
          A.zipIdx.map (fun x : Labeled × ℕ =>
            if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
        set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩
        have hres : raised.insertIdx h newPart = r := Option.some.inj htry
        rw [← hres, List.length_insertIdx]
        simp [raised, hf.2]
      omega)).value ≥
      (r[h + 1]'(by
        have hforget := forget_tryHardInsertionLabeled A q h
        rw [htry] at hforget
        have h_unl_some : tryHardInsertion (forget A) q h = some (forget r) := by
          simp only [Option.map_some] at hforget
          exact hforget.symm
        have hh_lt_forget := tryHardInsertion_h_lt_len h_unl_some
        rw [length_forget] at hh_lt_forget
        have hlen_r : r.length = A.length + 1 := by
          unfold tryHardInsertionLabeled at htry
          simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
          split_ifs at htry with hf had
          push_neg at hf
          set raised : List Labeled :=
            A.zipIdx.map (fun x : Labeled × ℕ =>
              if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
          set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩
          have hres : raised.insertIdx h newPart = r := Option.some.inj htry
          rw [← hres, List.length_insertIdx]
          simp [raised, hf.2]
        omega)).value + 3 := by
  have hforget := forget_tryHardInsertionLabeled A q h
  rw [htry] at hforget
  have h_unl_some : tryHardInsertion (forget A) q h = some (forget r) := by
    simp only [Option.map_some] at hforget
    exact hforget.symm
  have hh_lt_forget := tryHardInsertion_h_lt_len h_unl_some
  have hh_lt_A : h < A.length := by
    simpa [length_forget] using hh_lt_forget
  have hh1_lt_A : h - 1 < A.length := by omega
  have htry_struct := htry
  unfold tryHardInsertionLabeled at htry_struct
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry_struct
  split_ifs at htry_struct with hf had
  push_neg at hf
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
      with hraised_def
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩
    with hnewPart_def
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry_struct
  have hlen_raised : raised.length = A.length := by
    simp [hraised_def]
  have hlen_r : r.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx]
    simp [hlen_raised, hf.2]
  have hleft :
      (r[h - 1]'(by omega)).value = (A[h - 1]'hh1_lt_A).value + 3 := by
    have hidx : h - 1 < (raised.insertIdx h newPart).length := by
      rw [List.length_insertIdx]
      simp [hlen_raised, hf.2]
      omega
    have hget : r[h - 1]'(by omega) = (raised.insertIdx h newPart)[h - 1]'hidx := by
      congr 1
      exact hres.symm
    rw [hget, List.getElem_insertIdx]
    simp [show h - 1 < h from by omega, hraised_def, List.getElem_map,
      List.getElem_zipIdx]
  have hright :
      (r[h + 1]'(by omega)).value = (A[h]'hh_lt_A).value := by
    have hidx : h + 1 < (raised.insertIdx h newPart).length := by
      rw [List.length_insertIdx]
      simp [hlen_raised, hf.2]
      omega
    have hget : r[h + 1]'(by omega) = (raised.insertIdx h newPart)[h + 1]'hidx := by
      congr 1
      exact hres.symm
    rw [hget, List.getElem_insertIdx]
    simp [show ¬(h + 1 < h) from by omega, show ¬(h + 1 = h) from by omega,
      hraised_def, List.getElem_map, List.getElem_zipIdx]
  have hdec :
      (A[h - 1]'hh1_lt_A).value ≥ (A[h]'hh_lt_A).value := by
    have hpw := hflat.1.1
    have h :=
      List.pairwise_iff_getElem.mp hpw (h - 1) h
        (by rw [length_forget]; exact hh1_lt_A)
        (by rw [length_forget]; exact hh_lt_A)
        (by omega)
    simpa [forget, List.getElem_map] using h
  rw [hleft, hright]
  omega

private lemma tryHardInsertionLabeled_preserves_HardHasSupportingEasy
    {A : List Labeled} {q h : ℕ} {r : List Labeled}
    (hflat : IsThreeFlat (forget A))
    (hSupp : HardHasSupportingEasy A)
    (hMod : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
      (A[i]'hi).origin = some (p, InsertionKind.hard) → (A[i]'hi).value % 3 = 0)
    (htry : tryHardInsertionLabeled A q h = some r) :
    HardHasSupportingEasy r := by
  -- Bridge to unlabeled.
  have hforget := forget_tryHardInsertionLabeled A q h
  rw [htry] at hforget
  have h_unl_some : tryHardInsertion (forget A) q h = some (forget r) := by
    simp only [Option.map_some] at hforget; exact hforget.symm
  have h_unl_isSome : (tryHardInsertion (forget A) q h).isSome := by
    rw [h_unl_some]; rfl
  -- Extract h < (forget A).length, i.e., h < A.length.
  have hh_lt_forget := tryHardInsertion_h_lt_len h_unl_some
  have hh_lt_A : h < A.length := by rw [length_forget] at hh_lt_forget; exact hh_lt_forget
  -- Extract guard.
  have hh_q : h < q := by
    unfold tryHardInsertion at h_unl_some
    split at h_unl_some
    · simp at h_unl_some
    · next hng => push_neg at hng; exact hng.1
  -- Result structure: r = raised.insertIdx h newPart.
  have htry_orig : tryHardInsertionLabeled A q h = some r := htry
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf hadm_check
  push_neg at hf
  obtain ⟨_hh_q', hh_A'⟩ := hf
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩ with hnewPart_def
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised_def
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry
  have hlen_raised : raised.length = A.length := by simp [hraised_def]
  have hh_le_raised : h ≤ raised.length := by rw [hlen_raised]; omega
  have hlen_r : r.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx, hlen_raised]; simp [hh_A']
  -- Now the main case analysis.
  intro i hi p hhard hfr_r
  obtain h_new | h_old :=
    tryHardInsertionLabeled_hard_pos_pullback A q h r htry_orig i hi p hhard
  · -- New hard at i = h: NOT FR by admissibility.
    obtain ⟨hi_eq, _, _⟩ := h_new
    subst hi_eq
    exfalso
    rw [tryHardInsertionLabeled_admissibility_at_h htry_orig] at hfr_r
    cases hfr_r
  · -- Old hard at j.
    obtain ⟨j, hj, hi_eq, hjorig, hval_r⟩ := h_old
    -- Bounds.
    have hh_le_forget : h ≤ (forget A).length := by rw [length_forget]; omega
    by_cases hjh : j < h
    · -- subcase j < h: i = j (no shift but value raised).
      have hi_eq_j : i = j := by simp [hjh] at hi_eq; exact hi_eq
      by_cases hjh1 : j + 1 < h
      · -- j + 1 < h, i.e., j ≤ h - 2: FR pullback works, then transport easy via hSupp.
        have hj1_lt_A : j + 1 < A.length := by omega
        have hjm1_lt_A : 0 < j → j - 1 < A.length := fun _ => by omega
        have hflat_unl : isThreeFlatBool (forget A) = true :=
          Hints.isThreeFlatBool_of_IsThreeFlat hflat
        have hf_eq_A : ∀ k (hk : k < A.length),
            (forget A)[k]'(by rw [length_forget]; exact hk) = (A[k]'hk).value := by
          intro k hk; simp [forget, List.getElem_map]
        have hlen_forget_r : (forget r).length = A.length + 1 := by
          rw [length_forget, hlen_r]
        have hlen_erase_r : ((forget r).eraseIdx j).length = A.length := by
          rw [List.length_eraseIdx_of_lt (by rw [hlen_forget_r]; omega)]
          rw [hlen_forget_r]; omega
        -- Key computation: r[k] for k < h equals ⟨A[k].value+3, A[k].origin⟩.
        have hr_get_lt_h : ∀ (k : ℕ) (hk : k < A.length) (hkh : k < h),
            r[k]'(by rw [hlen_r]; omega) =
              ⟨(A[k]'hk).value + 3, (A[k]'hk).origin⟩ := by
          intro k hk hkh
          have hk_in_ins : k < (raised.insertIdx h newPart).length := by
            rw [List.length_insertIdx, hlen_raised]; split <;> omega
          have hr_eq_ins : r[k]'(by rw [hlen_r]; omega) =
              (raised.insertIdx h newPart)[k]'hk_in_ins := by
            congr 1; exact hres.symm
          rw [hr_eq_ins, List.getElem_insertIdx]
          simp [hkh, hraised_def, List.getElem_map, List.getElem_zipIdx]
        -- Forget version.
        have hforget_r_lt_h : ∀ (k : ℕ) (hk : k < A.length) (hkh : k < h),
            (forget r)[k]'(by rw [hlen_forget_r]; omega) = (A[k]'hk).value + 3 := by
          intro k hk hkh
          simp only [forget, List.getElem_map]
          rw [hr_get_lt_h k hk hkh]
        -- FR at j in (forget r).
        have hFR_unl_r : isFlatRemovableBool (forget r) j = true := by
          rw [← hi_eq_j]; exact hfr_r
        unfold isFlatRemovableBool at hFR_unl_r
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hFR_unl_r
        obtain ⟨⟨_, _⟩, hflat_erase_r⟩ := hFR_unl_r
        have hflat_erase_r' : IsThreeFlat ((forget r).eraseIdx j) :=
          isThreeFlatBool_implies' _ hflat_erase_r
        obtain ⟨_, hgaps_erase_r, _⟩ := hflat_erase_r'
        -- Step 1: prove isFlatRemovableBool (forget A) j = true.
        have hFR_unl_A : isFlatRemovableBool (forget A) j = true := by
          unfold isFlatRemovableBool
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [length_forget]; exact hj
          · rw [getElem!_pos _ j (by rw [length_forget]; exact hj)]
            rw [hf_eq_A j hj]
            exact hMod j hj p hjorig
          · apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap (forget A) j
              (by rw [length_forget]; exact hj) hflat_unl
            · -- Gap subgoal: (forget A)[j-1]'_ - (forget A)[j+1]'_ < 3.
              intro hj_pos hj1_in
              have hjm1_A : j - 1 < A.length := hjm1_lt_A hj_pos
              have hjm1_lt_h : j - 1 < h := by omega
              have hj1_lt_h_loc : j + 1 < h := hjh1
              -- Get the gap from the erased r.
              have hjm1_in_e : j - 1 < ((forget r).eraseIdx j).length := by
                rw [hlen_erase_r]; omega
              have hje_succ : (j - 1) + 1 < ((forget r).eraseIdx j).length := by
                rw [hlen_erase_r]; omega
              have hgap_e := hgaps_erase_r (j - 1) hje_succ
              -- Identify gap_e indices.
              have hjm1_in_r : j - 1 < (forget r).length := by rw [hlen_forget_r]; omega
              have hj1_in_r : j + 1 < (forget r).length := by rw [hlen_forget_r]; omega
              have herase_jm1 : ((forget r).eraseIdx j)[j - 1]'hjm1_in_e
                  = (forget r)[j - 1]'hjm1_in_r := by
                rw [List.getElem_eraseIdx]; simp [show j - 1 < j from by omega]
              have herase_je : ((forget r).eraseIdx j)[(j - 1) + 1]'hje_succ
                  = (forget r)[j + 1]'hj1_in_r := by
                rw [List.getElem_eraseIdx]
                have hne : ¬((j - 1) + 1 < j) := by omega
                simp only [hne, ↓reduceDIte]
                congr 1; omega
              rw [herase_jm1, herase_je] at hgap_e
              -- hgap_e: (forget r)[j-1] - (forget r)[j+1] < 3.
              rw [hforget_r_lt_h (j - 1) hjm1_A hjm1_lt_h,
                  hforget_r_lt_h (j + 1) hj1_lt_A hj1_lt_h_loc] at hgap_e
              -- Goal in safe getElem form.
              rw [hf_eq_A (j - 1) hjm1_A, hf_eq_A (j + 1) hj1_lt_A]
              omega
            · -- Last case: j + 1 = length, impossible since j ≤ h - 2.
              intro hj1_eq _
              exfalso
              rw [length_forget] at hj1_eq
              omega
        -- Step 2: apply hSupp.
        obtain ⟨_, heasy_A⟩ := hSupp j hj p hjorig hFR_unl_A
        -- Step 3: transport easy from A[j+1] to r[j+1].
        have hi1_lt_r : i + 1 < r.length := by rw [hi_eq_j, hlen_r]; omega
        refine ⟨hi1_lt_r, ?_⟩
        have hi1_eq_j1 : i + 1 = j + 1 := by rw [hi_eq_j]
        have hj1_lt_h_loc : j + 1 < h := hjh1
        have hr_get_j1 : r[i + 1]'hi1_lt_r =
            ⟨(A[j + 1]'hj1_lt_A).value + 3, (A[j + 1]'hj1_lt_A).origin⟩ := by
          have heq : r[i + 1]'hi1_lt_r = r[j + 1]'(by rw [hlen_r]; omega) := by
            congr 1
          rw [heq]
          exact hr_get_lt_h (j + 1) hj1_lt_A hj1_lt_h_loc
        rw [hr_get_j1]
        exact heasy_A
      · -- j + 1 ≥ h and j < h: j = h - 1.  Vacuous via bounds.
        push_neg at hjh1
        have hj_eq : j = h - 1 := by omega
        have hh_pos : 1 ≤ h := by omega
        have hh1_lt_A : h - 1 < A.length := by omega
        exfalso
        have hjorig_h1 : (A[h-1]'hh1_lt_A).origin = some (p, .hard) := by
          have hget : (A[h-1]'hh1_lt_A) = (A[j]'hj) := by congr 1; omega
          rw [hget]; exact hjorig
        have hA_h1_mod : (A[h-1]'hh1_lt_A).value % 3 = 0 :=
          hMod (h-1) hh1_lt_A p hjorig_h1
        have hub_unl := tryHardInsertion_upper_bound_early h_unl_isSome hh_pos hh_le_forget
        have hf_eq_A : ∀ k (hk : k < A.length),
            (forget A)[k]'(by rw [length_forget]; exact hk) = (A[k]'hk).value := by
          intro k hk; simp [forget, List.getElem_map]
        rw [hf_eq_A (h-1) hh1_lt_A] at hub_unl
        have hlb_unl := tryHardInsertion_lower_bound_early h_unl_isSome
          (by rw [length_forget]; exact hh_lt_A)
        rw [hf_eq_A h hh_lt_A] at hlb_unl
        obtain ⟨⟨hpw_unl, _⟩, _, _⟩ := hflat
        have hdec_unl := List.pairwise_iff_getElem.mp hpw_unl (h-1) h
          (by rw [length_forget]; exact hh1_lt_A)
          (by rw [length_forget]; exact hh_lt_A) (by omega)
        rw [hf_eq_A (h-1) hh1_lt_A, hf_eq_A h hh_lt_A] at hdec_unl
        -- A[h-1] < 3*q-3*h = 3(q-h), A[h] > 3(q-h)-3, A[h] ≤ A[h-1].
        -- Combine: A[h-1] ≥ A[h] ≥ 3(q-h)-2, A[h-1] ≤ 3(q-h)-1, A[h-1] % 3 = 0.
        -- 3(q-h)-2 and 3(q-h)-1 are not multiples of 3.
        omega
    · -- subcase j ≥ h: i = j + 1.
      push_neg at hjh
      have hi_eq_j1 : i = j + 1 := by
        have hjh_not : ¬ (j < h) := Nat.not_lt.mpr hjh
        simp [hjh_not] at hi_eq; exact hi_eq
      by_cases hjeq : j = h
      · -- j = h: vacuous via bounds (same combinatorial argument).
        exfalso
        have hh_dichotomy : 1 ≤ h ∨ h = 0 := by omega
        -- A[h] hard, A[h] % 3 = 0 by hMod.
        have hjorig_h : (A[h]'hh_lt_A).origin = some (p, .hard) := by
          have hget : (A[h]'hh_lt_A) = (A[j]'hj) := by congr 1; omega
          rw [hget]; exact hjorig
        have hA_h_mod : (A[h]'hh_lt_A).value % 3 = 0 := hMod h hh_lt_A p hjorig_h
        -- Lower bound at h.
        have hlb_unl := tryHardInsertion_lower_bound_early h_unl_isSome
          (by rw [length_forget]; exact hh_lt_A)
        have hf_eq_A : ∀ k (hk : k < A.length),
            (forget A)[k]'(by rw [length_forget]; exact hk) = (A[k]'hk).value := by
          intro k hk; simp [forget, List.getElem_map]
        rw [hf_eq_A h hh_lt_A] at hlb_unl
        -- Use upper bound + decreasing if h ≥ 1, otherwise direct.
        rcases hh_dichotomy with hpos | hzero
        · -- h ≥ 1: get A[h-1] < 3(q-h), A[h] ≤ A[h-1].
          have hh1_lt_A : h - 1 < A.length := by omega
          have hub_unl := tryHardInsertion_upper_bound_early h_unl_isSome hpos hh_le_forget
          rw [hf_eq_A (h-1) hh1_lt_A] at hub_unl
          obtain ⟨⟨hpw_unl, _⟩, _, _⟩ := hflat
          have hdec_unl := List.pairwise_iff_getElem.mp hpw_unl (h-1) h
            (by rw [length_forget]; exact hh1_lt_A)
            (by rw [length_forget]; exact hh_lt_A) (by omega)
          rw [hf_eq_A (h-1) hh1_lt_A, hf_eq_A h hh_lt_A] at hdec_unl
          omega
        · -- h = 0: tryHard at 0 cannot succeed for non-empty 3-flat A — the new
          -- hard at 0 would itself be flat-removable (its eraseIdx is the
          -- unraised A, which is 3-flat), contradicting admissibility.
          subst hzero
          have hadm := tryHardInsertionLabeled_admissibility_at_h htry_orig
          -- Compute (forget r) explicitly at h = 0.
          -- raised = A unchanged (no positions < 0).  So r = newPart :: A and
          -- (forget r).eraseIdx 0 = forget A which is 3-flat.
          have hraised_eq_A : raised = A := by
            apply List.ext_getElem
            · simp [hraised_def]
            · intro k hk1 hk2
              simp [hraised_def, List.getElem_map, List.getElem_zipIdx]
          have hr_eq : r = newPart :: A := by
            rw [← hres, hraised_eq_A, List.insertIdx_zero]
          have hforget_r : forget r = 3 * q :: forget A := by
            rw [hr_eq]; simp [forget, hnewPart_def]
          have hFR : isFlatRemovableBool (forget r) 0 = true := by
            unfold isFlatRemovableBool
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [hforget_r]; simp
            · rw [hforget_r]
              rw [getElem!_pos _ 0 (by simp)]
              simp
            · rw [hforget_r]
              show isThreeFlatBool ((3 * q :: forget A).eraseIdx 0) = true
              simp only [List.eraseIdx_cons_zero]
              exact Hints.isThreeFlatBool_of_IsThreeFlat hflat
          rw [hFR] at hadm
          cases hadm
      · -- j ≥ h + 1: FR pullback works ("after" side), then transport easy via hSupp.
        push_neg at hjeq
        have hjh1 : h + 1 ≤ j :=
          Nat.lt_iff_add_one_le.mp (lt_of_le_of_ne hjh (Ne.symm hjeq))
        have hjm1_lt_A : j - 1 < A.length := by omega
        have hj1_lt_A : j + 1 ≤ A.length := by omega  -- could equal length
        have hflat_unl : isThreeFlatBool (forget A) = true :=
          Hints.isThreeFlatBool_of_IsThreeFlat hflat
        have hf_eq_A : ∀ k (hk : k < A.length),
            (forget A)[k]'(by rw [length_forget]; exact hk) = (A[k]'hk).value := by
          intro k hk; simp [forget, List.getElem_map]
        have hlen_forget_r : (forget r).length = A.length + 1 := by
          rw [length_forget, hlen_r]
        have hi_lt_forget_r : i < (forget r).length := by rw [length_forget]; exact hi
        have hlen_erase_r : ((forget r).eraseIdx i).length = A.length := by
          rw [List.length_eraseIdx_of_lt hi_lt_forget_r]
          rw [hlen_forget_r]; omega
        -- Computation: for k > h, r[k] = A[k-1].
        have hr_get_gt_h : ∀ (k : ℕ) (hk : k - 1 < A.length) (hkh : h < k)
            (hk_in : k < r.length),
            r[k]'hk_in = A[k-1]'hk := by
          intro k hk hkh hk_in
          have hk_in_ins : k < (raised.insertIdx h newPart).length := by
            rw [List.length_insertIdx, hlen_raised]; split <;> omega
          have hr_eq_ins : r[k]'hk_in = (raised.insertIdx h newPart)[k]'hk_in_ins := by
            congr 1; exact hres.symm
          rw [hr_eq_ins, List.getElem_insertIdx]
          have hnotlt : ¬(k < h) := by omega
          have hnoteq : k ≠ h := by omega
          have hkm1_ge_h : ¬(k - 1 < h) := by omega
          simp only [hnotlt, hnoteq, ↓reduceDIte]
          simp [hraised_def, List.getElem_map, List.getElem_zipIdx, hkm1_ge_h]
        -- (forget r) version.
        have hforget_r_gt_h : ∀ (k : ℕ) (hk : k - 1 < A.length) (hkh : h < k)
            (hk_in : k < (forget r).length),
            (forget r)[k]'hk_in = (A[k - 1]'hk).value := by
          intro k hk hkh hk_in
          simp only [forget, List.getElem_map]
          have hk_in_r : k < r.length := by rw [hlen_r]; omega
          have := hr_get_gt_h k hk hkh hk_in_r
          rw [this]
        -- FR at i in (forget r).
        have hFR_unl_r : isFlatRemovableBool (forget r) i = true := hfr_r
        unfold isFlatRemovableBool at hFR_unl_r
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hFR_unl_r
        obtain ⟨_, hflat_erase_r⟩ := hFR_unl_r
        have hflat_erase_r' : IsThreeFlat ((forget r).eraseIdx i) :=
          isThreeFlatBool_implies' _ hflat_erase_r
        obtain ⟨_, hgaps_erase_r, hlast_erase_r⟩ := hflat_erase_r'
        -- Step 1: prove isFlatRemovableBool (forget A) j = true.
        have hFR_unl_A : isFlatRemovableBool (forget A) j = true := by
          unfold isFlatRemovableBool
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [length_forget]; exact hj
          · rw [getElem!_pos _ j (by rw [length_forget]; exact hj)]
            rw [hf_eq_A j hj]
            exact hMod j hj p hjorig
          · apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap (forget A) j
              (by rw [length_forget]; exact hj) hflat_unl
            · -- Gap subgoal: 0 < j → j + 1 < lenA → A[j-1] - A[j+1] < 3.
              intro hj_pos hj1_in
              have hj1_lt_A_strict : j + 1 < A.length := by rw [length_forget] at hj1_in; exact hj1_in
              -- Gap at position j in (forget r).eraseIdx i (with i = j + 1).
              have hj1_in_e : j + 1 < ((forget r).eraseIdx i).length := by
                rw [hlen_erase_r]; omega
              have hgap_e := hgaps_erase_r j hj1_in_e
              -- (forget r).eraseIdx i at position j: since j < i = j+1, equals (forget r)[j].
              have hj_in_e : j < ((forget r).eraseIdx i).length := by
                rw [hlen_erase_r]; omega
              have hj_in_r : j < (forget r).length := by rw [hlen_forget_r]; omega
              have hj2_in_r : j + 2 < (forget r).length := by rw [hlen_forget_r]; omega
              have herase_j : ((forget r).eraseIdx i)[j]'hj_in_e
                  = (forget r)[j]'hj_in_r := by
                rw [List.getElem_eraseIdx]; simp [show j < i from by omega]
              -- (forget r).eraseIdx i at position j+1: since j+1 ≥ i, equals (forget r)[j+2].
              have herase_j1 : ((forget r).eraseIdx i)[j + 1]'hj1_in_e
                  = (forget r)[j + 2]'hj2_in_r := by
                rw [List.getElem_eraseIdx]
                simp [show ¬(j + 1 < i) from by omega]
              rw [herase_j, herase_j1] at hgap_e
              -- (forget r)[j] = A[j-1].value (j > h).
              have hj_gt_h : h < j := by omega
              have hj2_gt_h : h < j + 2 := by omega
              have hjm1_in_A : (j) - 1 < A.length := hjm1_lt_A
              have hj1_in_A : (j + 2) - 1 < A.length := by omega
              rw [hforget_r_gt_h j hjm1_in_A hj_gt_h hj_in_r] at hgap_e
              rw [hforget_r_gt_h (j + 2) hj1_in_A hj2_gt_h hj2_in_r] at hgap_e
              -- hgap_e: A[j-1].value - A[(j+2)-1].value < 3, i.e., A[j-1] - A[j+1] < 3.
              have hAj1_eq : (A[(j + 2) - 1]'hj1_in_A) = (A[j + 1]'hj1_lt_A_strict) := by
                congr 1
              rw [hAj1_eq] at hgap_e
              -- Goal: (forget A)[j-1]'_ - (forget A)[j+1]'_ < 3.
              rw [hf_eq_A (j - 1) hjm1_lt_A, hf_eq_A (j + 1) hj1_lt_A_strict]
              exact hgap_e
            · -- Last subgoal: j + 1 = lenA → 0 < j → A[j-1] < 3.
              intro hj1_eq hj_pos
              have hj1_eq_A : j + 1 = A.length := by rw [length_forget] at hj1_eq; exact hj1_eq
              -- (forget r).eraseIdx i.last < 3.
              have hne : (forget r).eraseIdx i ≠ [] := by
                intro h_empty
                have hlen0 : ((forget r).eraseIdx i).length = 0 := by rw [h_empty]; rfl
                rw [hlen_erase_r] at hlen0; omega
              have hlast_val := hlast_erase_r hne
              rw [List.getLast_eq_getElem] at hlast_val
              -- ((forget r).eraseIdx i).length - 1 = lenA - 1 = j.
              have hlen_eq : ((forget r).eraseIdx i).length - 1 = j := by
                rw [hlen_erase_r]; omega
              have hj_in_e : j < ((forget r).eraseIdx i).length := by
                rw [hlen_erase_r]; omega
              have hget_eq : ((forget r).eraseIdx i)[
                  ((forget r).eraseIdx i).length - 1]'(by omega) =
                  ((forget r).eraseIdx i)[j]'hj_in_e := by
                congr 1
              rw [hget_eq] at hlast_val
              -- ((forget r).eraseIdx i)[j] = (forget r)[j] (since j < i = j+1).
              have hj_in_r : j < (forget r).length := by rw [hlen_forget_r]; omega
              have herase_j : ((forget r).eraseIdx i)[j]'hj_in_e
                  = (forget r)[j]'hj_in_r := by
                rw [List.getElem_eraseIdx]; simp [show j < i from by omega]
              rw [herase_j] at hlast_val
              -- (forget r)[j] = A[j-1].value (since j > h).
              have hj_gt_h : h < j := by omega
              rw [hforget_r_gt_h j hjm1_lt_A hj_gt_h hj_in_r] at hlast_val
              -- Goal: (forget A)[j - 1]'_ < 3.
              rw [hf_eq_A (j - 1) hjm1_lt_A]
              exact hlast_val
        -- Step 2: apply hSupp.
        obtain ⟨_, heasy_A⟩ := hSupp j hj p hjorig hFR_unl_A
        -- Step 3: transport easy from A[j+1] to r[i+1] = r[j+2].
        have hj1_lt_A_strict : j + 1 < A.length := by
          -- A[j+1] exists since hSupp gave us i+1 < A.length where i = j.
          -- Wait, hSupp gives (A[j+1]'?).origin ... so j+1 < A.length is implicit.
          -- From the obtain, _ : j + 1 < A.length is what we destructed.
          exact ‹j + 1 < A.length›
        have hi1_lt_r : i + 1 < r.length := by rw [hi_eq_j1, hlen_r]; omega
        refine ⟨hi1_lt_r, ?_⟩
        -- r[i+1] = r[j+2] = ⟨A[j+1].value, A[j+1].origin⟩.
        have hi1_eq_j2 : i + 1 = j + 2 := by rw [hi_eq_j1]
        have hj2_gt_h : h < j + 2 := by omega
        have hj1_in_A : (j + 2) - 1 < A.length := by omega
        have hr_get_j2 : r[i + 1]'hi1_lt_r =
            ⟨(A[(j + 2) - 1]'hj1_in_A).value, (A[(j + 2) - 1]'hj1_in_A).origin⟩ := by
          have heq : r[i + 1]'hi1_lt_r = r[j + 2]'(by rw [hlen_r]; omega) := by
            congr 1
          rw [heq]
          exact hr_get_gt_h (j + 2) hj1_in_A hj2_gt_h _
        rw [hr_get_j2]
        have hA_eq : (A[(j + 2) - 1]'hj1_in_A) = (A[j + 1]'hj1_lt_A_strict) := by
          congr 1
        rw [hA_eq]
        exact heasy_A

/-- Helper for the init case: `HardHasSupportingEasy` holds for the initial
state `processInsertionsLabeled ν A_init`. Proved via strengthened induction
with `HardSupportProcessInv`. -/
private lemma processInsertionsLabeled_HardHasSupportingEasy
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    HardHasSupportingEasy (processInsertionsLabeled ν A_init) := by
  -- Strengthened induction: HardSupportProcessInv carries through each step.
  suffices hgen : ∀ (ν' : List ℕ) (A : List Labeled),
      IsThreeFlat (forget A) →
      HardSupportProcessInv A ν' →
      ν'.Pairwise (· ≥ ·) →
      (∀ x ∈ ν', 0 < x) →
      HardHasSupportingEasy (processInsertionsLabeled ν' A) by
    refine hgen ν A_init hA_flat ?_ hν_sort hν_pos
    refine ⟨?_, ?_, ?_⟩
    -- support: HardHasSupportingEasy A_init is vacuous (all-core).
    · intro i hi p horg _hfr
      have hmem := List.getElem_mem hi
      have hclean := hA_clean _ hmem
      rw [hclean] at horg
      cases horg
    -- sizeBound: A_init has no labels, vacuous.
    · intro i hi p k horg q hq
      have hmem := List.getElem_mem hi
      have hclean := hA_clean _ hmem
      rw [hclean] at horg
      cases horg
    -- hardValueMod3: vacuous
    · intro i hi p horg
      have hmem := List.getElem_mem hi
      have hclean := hA_clean _ hmem
      rw [hclean] at horg
      cases horg
  intro ν' A hAflat hinv hνsort hνpos
  induction ν' generalizing A with
  | nil =>
      simp only [processInsertionsLabeled]
      exact hinv.support
  | cons q rest ih =>
      simp only [processInsertionsLabeled]
      have hAflat' : IsThreeFlat (forget (performInsertionLabeled A q)) := by
        rw [forget_performInsertionLabeled]
        exact performInsertion_preserves_flat' (forget A) q hAflat
      -- Preservation of HardSupportProcessInv through performInsertionLabeled.
      -- Three branches: hard insertion, easy insertion, fallthrough.
      have hq_dom_rest : ∀ s ∈ rest, q ≥ s :=
        (List.pairwise_cons.mp hνsort).1
      have hinv' : HardSupportProcessInv (performInsertionLabeled A q) rest := by
        unfold performInsertionLabeled
        cases hf : findHardInsertionLabeled A q with
        | some r =>
            -- Hard insertion case.
            refine ⟨?support, ?sizeBound, ?hardValueMod3⟩
            case support =>
              have hsupp_hard : ∀ (h₀ : ℕ) (result : List Labeled),
                  findHardInsertionLabeled A q h₀ = some result →
                  HardHasSupportingEasy result := by
                intro h₀
                induction h₀ using findHardInsertionLabeled.induct A q with
                | case1 h hguard =>
                    intro result hfind
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard] at hfind
                | case2 h hguard r_h htry =>
                    intro result hfind
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard, htry] at hfind
                    subst hfind
                    exact tryHardInsertionLabeled_preserves_HardHasSupportingEasy
                      hAflat hinv.support hinv.hardValueMod3 htry
                | case3 h hguard htry_fail ih =>
                    intro result hfind
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard, htry_fail] at hfind
                    exact ih result hfind
              intro i hi p hhard hfr_r
              exact hsupp_hard 0 r hf i hi p hhard hfr_r
            case hardValueMod3 =>
              -- New hard has value 3*(q-h), % 3 = 0. Old hards: value preserved
              -- (positions ≥ h) or raised by 3 (positions < h); either way mod 3.
              -- Induction over findHardInsertionLabeled.
              have hmod_hard :
                  ∀ (h₀ : ℕ) (result : List Labeled),
                    findHardInsertionLabeled A q h₀ = some result →
                    ∀ (i : ℕ) (hi : i < result.length) (p : ℕ),
                      (result[i]'hi).origin = some (p, InsertionKind.hard) →
                      (result[i]'hi).value % 3 = 0 := by
                intro h₀
                induction h₀ using findHardInsertionLabeled.induct A q with
                | case1 h hguard =>
                    intro result hfind i hi p horg
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard] at hfind
                | case2 h hguard r_h htry =>
                    intro result hfind i hi p horg
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard, htry] at hfind
                    subst hfind
                    obtain h1 | h2 :=
                      tryHardInsertionLabeled_hard_pos_pullback A q h r_h
                        htry i hi p horg
                    · -- New hard at h
                      obtain ⟨_, _, hval⟩ := h1
                      rw [hval]
                      exact Nat.mul_mod_right 3 (q - h)
                    · -- Existing hard
                      obtain ⟨j, hj, _, hjorig, hval⟩ := h2
                      have hold_mod := hinv.hardValueMod3 j hj p hjorig
                      rw [hval]
                      by_cases hjh : j < h
                      · simp [hjh]; omega
                      · simp [hjh]; exact hold_mod
                | case3 h hguard htry_fail ih =>
                    intro result hfind i hi p horg
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard, htry_fail] at hfind
                    exact ih result hfind i hi p horg
              intro i hi p horg
              exact hmod_hard 0 r hf i hi p horg
            case sizeBound =>
              -- New hard at h has rank q; old labels have rank ≥ q ≥ all rest.
              -- Induction on h₀ via findHardInsertionLabeled.induct.
              have hbound_hard :
                  ∀ (h₀ : ℕ) (result : List Labeled),
                    findHardInsertionLabeled A q h₀ = some result →
                    ∀ (i : ℕ) (hi : i < result.length) (p : ℕ)
                      (k : InsertionKind),
                      (result[i]'hi).origin = some (p, k) →
                      ∀ s ∈ rest, p ≥ s := by
                intro h₀
                induction h₀ using findHardInsertionLabeled.induct A q with
                | case1 h hguard =>
                    intro result hfind i hi p k horg s hs_rest
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard] at hfind
                | case2 h hguard r_h htry =>
                    intro result hfind i hi p k horg s hs_rest
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard, htry] at hfind
                    subst hfind
                    cases k with
                    | hard =>
                        obtain h1 | h2 :=
                          tryHardInsertionLabeled_hard_pos_pullback A q h r_h
                            htry i hi p horg
                        · -- New hard: p = q
                          obtain ⟨_, hp_eq, _⟩ := h1
                          rw [hp_eq]; exact hq_dom_rest s hs_rest
                        · -- Existing hard pulled back to A
                          obtain ⟨j, hj, _, hjorig, _⟩ := h2
                          exact hinv.sizeBound j hj p InsertionKind.hard
                            hjorig s (List.mem_cons_of_mem q hs_rest)
                    | easy =>
                        have horg_easy :
                            (r_h[i]'hi).origin.map Prod.snd =
                              some InsertionKind.easy := by
                          rw [horg]; rfl
                        obtain ⟨j, hj, _, h_origin⟩ :=
                          tryHardInsertionLabeled_easy_pos_pullback A q h
                            r_h htry i hi horg_easy
                        have horg_A :
                            (A[j]'hj).origin = some (p, InsertionKind.easy) := by
                          rw [h_origin]; exact horg
                        exact hinv.sizeBound j hj p InsertionKind.easy
                          horg_A s (List.mem_cons_of_mem q hs_rest)
                | case3 h hguard htry_fail ih =>
                    intro result hfind i hi p k horg s hs_rest
                    unfold findHardInsertionLabeled at hfind
                    simp [hguard, htry_fail] at hfind
                    exact ih result hfind i hi p k horg s hs_rest
              intro i hi p k horg s hs_rest
              exact hbound_hard 0 r hf i hi p k horg s hs_rest
        | none =>
            cases he : tryEasyInsertionLabeled A q with
            | some r =>
                -- Easy insertion case.
                refine ⟨?support, ?sizeBound, ?hardValueMod3⟩
                case support =>
                  intro i hi p hhard hfr_r
                  unfold tryEasyInsertionLabeled at he
                  simp only at he
                  split_ifs at he with hcond
                  set newPart : Labeled :=
                    ⟨3 * q, some (q, InsertionKind.easy)⟩ with hnewPart_def
                  set pos := (A.takeWhile (·.value ≥ 3 * q)).length with hpos_def
                  have hres : A.insertIdx pos newPart = r := Option.some.inj he
                  have hpos_le : pos ≤ A.length :=
                    List.IsPrefix.length_le (List.takeWhile_prefix _)
                  have hlen_r : r.length = A.length + 1 := by
                    rw [← hres, List.length_insertIdx]; simp [hpos_le]
                  have hcond_split :
                      isThreeFlatBool (forget (A.insertIdx pos newPart)) = true ∧
                      isFlatRemovableBool (forget (A.insertIdx pos newPart)) pos = true := by
                    simp only [Bool.and_eq_true] at hcond
                    exact hcond
                  have hforget_eq : forget (A.insertIdx pos newPart) =
                      (forget A).insertIdx pos (3 * q) :=
                    Hints.forget_insertIdx A pos newPart
                  have hflat_xs : isThreeFlatBool (forget A) = true := by
                    obtain ⟨⟨hpw, hpos_a⟩, hgap, hlast⟩ := hAflat
                    unfold isThreeFlatBool isPositivePartitionBool
                    simp only [Bool.and_eq_true, decide_eq_true_eq,
                      List.all_eq_true, List.mem_range]
                    refine ⟨⟨⟨hpw, ?_⟩, ?_⟩, ?_⟩
                    · intro x hx; exact hpos_a x hx
                    · intro k hk
                      have := hgap k (by omega)
                      rw [getElem!_pos _ k (by omega),
                        getElem!_pos _ (k + 1) (by omega)]
                      exact this
                    · cases hl : (forget A).getLast? with
                      | none => simp
                      | some x =>
                        simp [decide_eq_true_eq]
                        have hne : forget A ≠ [] := by
                          intro h; rw [h] at hl; simp at hl
                        rw [List.getLast?_eq_some_getLast hne] at hl
                        exact Option.some.inj hl ▸ hlast hne
                  have hlen_forget : (forget A).length = A.length := length_forget A
                  have hpos_le_forget : pos ≤ (forget A).length := by
                    rw [hlen_forget]; exact hpos_le
                  have hfr_r_unl : isFlatRemovableBool
                      ((forget A).insertIdx pos (3 * q)) i = true := by
                    rw [← hres] at hfr_r
                    rw [hforget_eq] at hfr_r
                    exact hfr_r
                  -- Save admissibility constraints in a usable form
                  have hflat_r_unl : isThreeFlatBool
                      ((forget A).insertIdx pos (3 * q)) = true := by
                    rw [← hforget_eq]; exact hcond_split.1
                  subst hres
                  -- Goal: ∃ hi1 : i + 1 < (A.insertIdx pos newPart).length,
                  --   ((A.insertIdx pos newPart)[i+1]).origin.map Prod.snd = some easy
                  rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
                  · -- Case i < pos
                    have hi_in_A : i < A.length := by
                      have : i < A.length + 1 := by rw [← hlen_r]; exact hi
                      omega
                    have horig_i :
                        ((A.insertIdx pos newPart)[i]'hi).origin
                          = (A[i]'hi_in_A).origin :=
                      Hints.origin_insertIdx_of_lt A pos i newPart
                        hi hi_in_A hlt
                    rw [horig_i] at hhard
                    by_cases hi1_eq_pos : i + 1 = pos
                    · -- Sub-case i + 1 = pos: r[i+1] = newPart (easy). ✓
                      have hi1_lt_r : i + 1 < (A.insertIdx pos newPart).length := by
                        simp [List.length_insertIdx, hpos_le]; omega
                      refine ⟨hi1_lt_r, ?_⟩
                      -- Goal: ((A.insertIdx pos newPart)[i+1]).origin.map Prod.snd = some easy
                      rw [List.getElem_insertIdx]
                      simp [show ¬(i + 1 < pos) from by omega,
                            show i + 1 = pos from hi1_eq_pos, hnewPart_def]
                    · -- Sub-case i + 1 < pos: use FR transfer "before"
                      have hi1_lt_pos : i + 1 < pos := by omega
                      have hi1_lt_A : i + 1 < A.length := by omega
                      have hfr_xs_i : isFlatRemovableBool (forget A) i = true :=
                        easyInsert_FR_transfer_before (forget A) q pos i
                          hpos_le_forget hflat_xs
                          (by rw [hlen_forget]; exact hi_in_A)
                          hi1_lt_pos hfr_r_unl
                      obtain ⟨_, heasy_A⟩ :=
                        hinv.support i hi_in_A p hhard hfr_xs_i
                      have hi1_lt_r : i + 1 < (A.insertIdx pos newPart).length := by
                        simp [List.length_insertIdx, hpos_le]; omega
                      refine ⟨hi1_lt_r, ?_⟩
                      have horig_i1 :
                          ((A.insertIdx pos newPart)[i + 1]'hi1_lt_r).origin
                            = (A[i + 1]'hi1_lt_A).origin :=
                        Hints.origin_insertIdx_of_lt A pos (i + 1) newPart
                          hi1_lt_r hi1_lt_A hi1_lt_pos
                      rw [horig_i1]
                      exact heasy_A
                  · -- Case i = pos: r[pos] = newPart (easy), contradicts hard.
                    subst heq
                    have horig_i := Hints.origin_insertIdx_at A pos newPart hi
                    rw [horig_i] at hhard
                    exfalso
                    have : newPart.origin = some (q, InsertionKind.easy) := rfl
                    rw [this] at hhard
                    cases hhard
                  · -- Case i > pos.
                    have hi_in_A1 : i < A.length + 1 := by rw [← hlen_r]; exact hi
                    have hi_minus_in_A : i - 1 < A.length := by omega
                    have horig_i :
                        ((A.insertIdx pos newPart)[i]'hi).origin
                          = (A[i - 1]'hi_minus_in_A).origin :=
                      Hints.origin_insertIdx_of_gt A pos i newPart
                        hi hi_minus_in_A hgt
                    rw [horig_i] at hhard
                    by_cases hi_eq_p1 : i = pos + 1
                    · -- Sub-case i = pos + 1: vacuous via hardValueMod3 contradiction.
                      exfalso
                      subst hi_eq_p1
                      have hpos_lt_A : pos < A.length := by
                        have h1 : pos + 1 - 1 = pos := by omega
                        rw [← h1]; exact hi_minus_in_A
                      have hA_pos_mod : (A[pos]'hpos_lt_A).value % 3 = 0 :=
                        hinv.hardValueMod3 pos hpos_lt_A p hhard
                      -- A[pos].value < 3q from takeWhile
                      have hA_pos_lt_3q : (A[pos]'hpos_lt_A).value < 3 * q := by
                        have hsuff : ∀ (B : List Labeled) (v : ℕ)
                            (h : (B.takeWhile (·.value ≥ v)).length < B.length),
                            (B[(B.takeWhile (·.value ≥ v)).length]'h).value < v := by
                          intro B v h
                          induction B with
                          | nil => simp at h
                          | cons a t ih =>
                            simp only [List.takeWhile_cons]
                            split
                            · next hge =>
                              simp only [List.length_cons, List.getElem_cons_succ]
                              exact ih (by simp [hge] at h; omega)
                            · next hlt_pred =>
                              simp only [List.length_nil, List.getElem_cons_zero]
                              simp [decide_eq_true_eq] at hlt_pred
                              exact hlt_pred
                        exact hsuff A (3 * q) hpos_lt_A
                      have hA_pos_val_pos : 0 < (A[pos]'hpos_lt_A).value := by
                        obtain ⟨⟨_, hpos_check⟩, _, _⟩ := hAflat
                        have hmem : (A[pos]'hpos_lt_A).value ∈ forget A := by
                          simp [forget, List.mem_map]
                          exact ⟨_, List.getElem_mem _, rfl⟩
                        exact hpos_check _ hmem
                      -- value > 0 + value % 3 = 0 → value ≥ 3
                      have hA_pos_ge3 : 3 ≤ (A[pos]'hpos_lt_A).value := by omega
                      -- Two sub-cases: pos + 1 = A.length or < A.length.
                      by_cases hp1_eq_alen : pos + 1 = A.length
                      · -- pos + 1 = A.length: in r, position pos + 1 = A.length is last.
                        -- r 3-flat → last < 3. But last = A[pos].value ≥ 3. Contradiction.
                        have hflat_r' := isThreeFlatBool_implies' _ hcond_split.1
                        obtain ⟨_, _, hlast_r⟩ := hflat_r'
                        have hne_r : forget (A.insertIdx pos newPart) ≠ [] := by
                          intro hempty
                          have hlen0 : (forget (A.insertIdx pos newPart)).length = 0 := by
                            rw [hempty]; rfl
                          simp [length_forget, List.length_insertIdx, hpos_le] at hlen0
                        have hlast_r_val := hlast_r hne_r
                        rw [List.getLast_eq_getElem] at hlast_r_val
                        -- (forget (A.insertIdx pos newPart))[length - 1] < 3
                        -- length - 1 = A.length = pos + 1
                        -- At position pos + 1 in forget r: it's the value at A[pos] (shifted up).
                        have hlen_r_forget :
                            (forget (A.insertIdx pos newPart)).length = A.length + 1 := by
                          simp [length_forget, List.length_insertIdx, hpos_le]
                        have hidx_in_r : pos + 1 <
                            (forget (A.insertIdx pos newPart)).length := by
                          rw [hlen_r_forget]; omega
                        -- The last position equals pos + 1.
                        have hlast_idx_lt :
                            (forget (A.insertIdx pos newPart)).length - 1 <
                              (forget (A.insertIdx pos newPart)).length := by
                          rw [hlen_r_forget]; omega
                        -- (forget (A.insertIdx pos newPart))[pos + 1]: r[pos+1] = A[pos] (since pos+1 > pos)
                        have hval_at_p1 :
                            (forget (A.insertIdx pos newPart))[pos + 1]'hidx_in_r
                              = (A[pos]'hpos_lt_A).value := by
                          simp [forget, List.getElem_map, List.getElem_insertIdx]
                        -- Goal: derive contradiction. The "last index" equals pos + 1, so
                        -- the last value equals A[pos].value, which is ≥ 3, contradicting < 3.
                        have hidx_eq :
                            (forget (A.insertIdx pos newPart)).length - 1 = pos + 1 := by
                          rw [hlen_r_forget]; omega
                        have hidx_lookup :
                            (forget (A.insertIdx pos newPart))[(forget (A.insertIdx pos
                              newPart)).length - 1]'hlast_idx_lt =
                            (forget (A.insertIdx pos newPart))[pos + 1]'hidx_in_r := by
                          congr 1
                        rw [hidx_lookup, hval_at_p1] at hlast_r_val
                        omega
                      · -- pos + 1 < A.length: A[pos+1] exists.
                        have hpos1_lt_A : pos + 1 < A.length := by omega
                        unfold isFlatRemovableBool at hfr_r_unl
                        simp only [Bool.and_eq_true, decide_eq_true_eq,
                          beq_iff_eq] at hfr_r_unl
                        obtain ⟨_, hflat_erase_bool⟩ := hfr_r_unl
                        have hflat_erase := isThreeFlatBool_implies' _ hflat_erase_bool
                        obtain ⟨_, hgaps_erase, _⟩ := hflat_erase
                        have hlen_r_ins :
                            ((forget A).insertIdx pos (3 * q)).length
                              = (forget A).length + 1 :=
                          Hints.length_insertIdx_le (forget A) pos (3 * q) hpos_le_forget
                        have hlen_e_r :
                            (((forget A).insertIdx pos (3 * q)).eraseIdx (pos + 1)).length
                              = (forget A).length := by
                          rw [List.length_eraseIdx_of_lt]
                          · rw [hlen_r_ins]; omega
                          · rw [hlen_r_ins]; omega
                        have hp1_in_e : pos + 1 <
                            (((forget A).insertIdx pos (3 * q)).eraseIdx (pos + 1)).length := by
                          rw [hlen_e_r, hlen_forget]; omega
                        have hgap_e := hgaps_erase pos hp1_in_e
                        have hpos_in_r : pos <
                            ((forget A).insertIdx pos (3 * q)).length := by
                          rw [hlen_r_ins]; omega
                        have hpos2_in_r : pos + 2 <
                            ((forget A).insertIdx pos (3 * q)).length := by
                          rw [hlen_r_ins]; omega
                        have hp_in_e : pos <
                            (((forget A).insertIdx pos (3 * q)).eraseIdx (pos + 1)).length := by
                          rw [hlen_e_r, hlen_forget]; omega
                        have herase_pos :
                            (((forget A).insertIdx pos (3 * q)).eraseIdx (pos + 1))[pos]'hp_in_e
                              = ((forget A).insertIdx pos (3 * q))[pos]'hpos_in_r := by
                          rw [List.getElem_eraseIdx]; simp [show pos < pos + 1 from by omega]
                        have herase_p1 :
                            (((forget A).insertIdx pos (3 * q)).eraseIdx (pos + 1))[pos + 1]'hp1_in_e
                              = ((forget A).insertIdx pos (3 * q))[pos + 2]'hpos2_in_r := by
                          rw [List.getElem_eraseIdx]
                          simp [show ¬(pos + 1 < pos + 1) from by omega]
                        have hr_pos :
                            ((forget A).insertIdx pos (3 * q))[pos]'hpos_in_r = 3 * q := by
                          rw [List.getElem_insertIdx]; simp
                        have hr_pos2 :
                            ((forget A).insertIdx pos (3 * q))[pos + 2]'hpos2_in_r =
                              (forget A)[pos + 1]'(by rw [hlen_forget]; exact hpos1_lt_A) := by
                          rw [List.getElem_insertIdx]
                          simp [show ¬(pos + 2 < pos) from by omega,
                                show ¬(pos + 2 = pos) from by omega]
                        rw [herase_pos, herase_p1, hr_pos, hr_pos2] at hgap_e
                        have hforget_lookup :
                            (forget A)[pos + 1]'(by rw [hlen_forget]; exact hpos1_lt_A)
                              = (A[pos + 1]'hpos1_lt_A).value := by
                          simp [forget, List.getElem_map]
                        rw [hforget_lookup] at hgap_e
                        have hA_decr : (A[pos + 1]'hpos1_lt_A).value
                            ≤ (A[pos]'hpos_lt_A).value := by
                          obtain ⟨hpair_struct, _, _⟩ := hAflat
                          have hpw_forget : (forget A).Pairwise (· ≥ ·) := hpair_struct.1
                          have hpw_iff := List.pairwise_iff_getElem.mp hpw_forget pos (pos + 1)
                            (by rw [hlen_forget]; exact hpos_lt_A)
                            (by rw [hlen_forget]; exact hpos1_lt_A)
                            (by omega)
                          simp [forget, List.getElem_map] at hpw_iff
                          exact hpw_iff
                        omega
                    · -- Sub-case i > pos + 1: use FR transfer "after"
                      have hi_gt_p1 : pos + 1 < i := by omega
                      have hpos_lt_im1 : pos < i - 1 := by omega
                      have hfr_xs_im1 : isFlatRemovableBool (forget A) (i - 1) = true := by
                        have hi_idx : i = (i - 1) + 1 := by omega
                        rw [hi_idx] at hfr_r_unl
                        exact easyInsert_FR_transfer_after (forget A) q pos (i - 1)
                          hpos_le_forget hflat_xs
                          (by rw [hlen_forget]; exact hi_minus_in_A)
                          hpos_lt_im1 hfr_r_unl
                      obtain ⟨_, heasy_A⟩ :=
                        hinv.support (i - 1) hi_minus_in_A p hhard hfr_xs_im1
                      -- heasy_A : (A[(i-1)+1]).origin.map Prod.snd = easy
                      have hi_in_A : i < A.length := by omega
                      have heasy_A_at_i :
                          (A[i]'hi_in_A).origin.map Prod.snd
                            = some InsertionKind.easy := by
                        have h_idx : (i - 1) + 1 = i := by omega
                        have h_get :
                            A[i]'hi_in_A = A[(i - 1) + 1]'(by omega) := by
                          congr 1; omega
                        rw [h_get]
                        exact heasy_A
                      have hi1_lt_r : i + 1 < (A.insertIdx pos newPart).length := by
                        simp [List.length_insertIdx, hpos_le]; omega
                      refine ⟨hi1_lt_r, ?_⟩
                      have hi1_gt : pos < i + 1 := by omega
                      have hi1_pre : (i + 1) - 1 < A.length := by omega
                      have horig_i1 :
                          ((A.insertIdx pos newPart)[i + 1]'hi1_lt_r).origin
                            = (A[(i + 1) - 1]'hi1_pre).origin :=
                        Hints.origin_insertIdx_of_gt A pos (i + 1) newPart
                          hi1_lt_r hi1_pre hi1_gt
                      rw [horig_i1]
                      -- Goal: (A[(i+1)-1]).origin.map .snd = some easy
                      -- heasy_A_at_i : (A[i]).origin.map .snd = some easy
                      have h_get :
                          A[(i + 1) - 1]'hi1_pre = A[i]'hi_in_A := by
                        congr 1
                      rw [h_get]
                      exact heasy_A_at_i
                case hardValueMod3 =>
                  -- Easy insertion doesn't touch existing hards' values.
                  intro i hi p hhard
                  unfold tryEasyInsertionLabeled at he
                  simp only at he
                  split_ifs at he with hcond
                  set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
                  set pos := (A.takeWhile (·.value ≥ 3 * q)).length
                  have hres : A.insertIdx pos newPart = r := Option.some.inj he
                  have hpos_le : pos ≤ A.length :=
                    List.IsPrefix.length_le (List.takeWhile_prefix _)
                  have hlen_r : r.length = A.length + 1 := by
                    rw [← hres, List.length_insertIdx]; simp [hpos_le]
                  subst hres
                  rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
                  · have hpre : i < A.length := by omega
                    have horig := Hints.origin_insertIdx_of_lt A pos i newPart
                      hi hpre hlt
                    rw [horig] at hhard
                    have hval_eq : ((A.insertIdx pos newPart)[i]'hi).value
                        = (A[i]'hpre).value := by
                      rw [List.getElem_insertIdx]; simp [hlt]
                    rw [hval_eq]
                    exact hinv.hardValueMod3 i hpre p hhard
                  · subst heq
                    have horig := Hints.origin_insertIdx_at A pos newPart hi
                    rw [horig] at hhard
                    exfalso
                    have : newPart.origin = some (q, InsertionKind.easy) := rfl
                    rw [this] at hhard
                    cases hhard
                  · have hpre : i - 1 < A.length := by rw [hlen_r] at hi; omega
                    have horig := Hints.origin_insertIdx_of_gt A pos i newPart
                      hi hpre hgt
                    rw [horig] at hhard
                    have hval_eq : ((A.insertIdx pos newPart)[i]'hi).value
                        = (A[i - 1]'hpre).value := by
                      rw [List.getElem_insertIdx]
                      simp [show ¬(i < pos) from by omega, show ¬(i = pos) from by omega]
                    rw [hval_eq]
                    exact hinv.hardValueMod3 (i - 1) hpre p hhard
                case sizeBound =>
                  intro i hi p k horg s hs_rest
                  -- tryEasyInsertionLabeled A q = some r ⇒ r is A.insertIdx pos newPart
                  -- with pos = length of takeWhile (·.value ≥ 3*q), newPart = ⟨3q, (q, .easy)⟩.
                  unfold tryEasyInsertionLabeled at he
                  simp only at he
                  split_ifs at he with hcond
                  set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
                  set pos := (A.takeWhile (·.value ≥ 3 * q)).length
                  have hres : A.insertIdx pos newPart = r := Option.some.inj he
                  have hpos_le : pos ≤ A.length :=
                    List.IsPrefix.length_le (List.takeWhile_prefix _)
                  have hlen_r : r.length = A.length + 1 := by
                    rw [← hres, List.length_insertIdx]; simp [hpos_le]
                  subst hres
                  rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
                  · have hpre : i < A.length := by omega
                    have horig :=
                      Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
                    rw [horig] at horg
                    exact hinv.sizeBound i hpre p k horg s
                      (List.mem_cons_of_mem q hs_rest)
                  · subst heq
                    have horig :=
                      Hints.origin_insertIdx_at A pos newPart hi
                    rw [horig] at horg
                    simp [newPart] at horg
                    -- horg : some (q, .easy) = some (p, k), so p = q
                    obtain ⟨hp, _hk⟩ := horg
                    rw [← hp]
                    exact hq_dom_rest s hs_rest
                  · have hpre : i - 1 < A.length := by rw [hlen_r] at hi; omega
                    have horig :=
                      Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
                    rw [horig] at horg
                    exact hinv.sizeBound (i - 1) hpre p k horg s
                      (List.mem_cons_of_mem q hs_rest)
            | none =>
                -- Fallthrough: result = A, invariant transports with smaller tail.
                refine ⟨hinv.support, ?_, hinv.hardValueMod3⟩
                intro i hi p k horg s hs
                exact hinv.sizeBound i hi p k horg s
                  (List.mem_cons_of_mem q hs)
      apply ih _ hAflat' hinv'
      · exact (List.pairwise_cons.mp hνsort).2
      · intro x hx; exact hνpos x (List.mem_cons_of_mem q hx)

/-- A successful hard-insertion search preserves the fact that every hard label
has value divisible by `3`.  New hard labels have value `3 * (q - h)`, while
old hard labels are either unchanged or raised by `3`. -/
private lemma findHardInsertionLabeled_preserves_hard_value_mod3
    {A result : List Labeled} {q h₀ : ℕ}
    (hMod : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
      (A[i]'hi).origin = some (p, InsertionKind.hard) →
        (A[i]'hi).value % 3 = 0)
    (hfind : findHardInsertionLabeled A q h₀ = some result) :
    ∀ (i : ℕ) (hi : i < result.length) (p : ℕ),
      (result[i]'hi).origin = some (p, InsertionKind.hard) →
        (result[i]'hi).value % 3 = 0 := by
  induction h₀ using findHardInsertionLabeled.induct A q with
  | case1 h hguard =>
      intro i hi p hhard
      unfold findHardInsertionLabeled at hfind
      simp [hguard] at hfind
  | case2 h hguard r htry =>
      intro i hi p hhard
      unfold findHardInsertionLabeled at hfind
      simp [hguard, htry] at hfind
      subst hfind
      obtain hnew | hold :=
        tryHardInsertionLabeled_hard_pos_pullback A q h r htry i hi p hhard
      · obtain ⟨_, _, hval⟩ := hnew
        rw [hval]
        exact Nat.mul_mod_right 3 (q - h)
      · obtain ⟨j, hj, _, hhard_A, hval⟩ := hold
        have hmod_A := hMod j hj p hhard_A
        rw [hval]
        by_cases hjh : j < h
        · simp [hjh]
          omega
        · simp [hjh]
          exact hmod_A
  | case3 h hguard htry_fail ih =>
      unfold findHardInsertionLabeled at hfind
      simp [hguard, htry_fail] at hfind
      exact ih hfind

/-- One labeled insertion step preserves hard-label divisibility by `3`. -/
private lemma performInsertionLabeled_preserves_hard_value_mod3
    (A : List Labeled) (q : ℕ)
    (hMod : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
      (A[i]'hi).origin = some (p, InsertionKind.hard) →
        (A[i]'hi).value % 3 = 0) :
    ∀ (i : ℕ) (hi : i < (performInsertionLabeled A q).length) (p : ℕ),
      ((performInsertionLabeled A q)[i]'hi).origin =
          some (p, InsertionKind.hard) →
        ((performInsertionLabeled A q)[i]'hi).value % 3 = 0 := by
  unfold performInsertionLabeled
  cases hf : findHardInsertionLabeled A q with
  | some r =>
      exact findHardInsertionLabeled_preserves_hard_value_mod3 hMod hf
  | none =>
      cases he : tryEasyInsertionLabeled A q with
      | none =>
          simpa using hMod
      | some r =>
          intro i hi p hhard
          unfold tryEasyInsertionLabeled at he
          simp only at he
          split_ifs at he with hcond
          set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
          set pos := (A.takeWhile (·.value ≥ 3 * q)).length
          have hres : A.insertIdx pos newPart = r := Option.some.inj he
          have hpos_le : pos ≤ A.length :=
            List.IsPrefix.length_le (List.takeWhile_prefix _)
          have hlen_r : r.length = A.length + 1 := by
            rw [← hres, List.length_insertIdx]
            simp [hpos_le]
          subst hres
          rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
          · have hiA : i < A.length := by omega
            have horig :=
              Hints.origin_insertIdx_of_lt A pos i newPart hi hiA hlt
            rw [horig] at hhard
            have hval :
                ((A.insertIdx pos newPart)[i]'hi).value = (A[i]'hiA).value := by
              rw [List.getElem_insertIdx]
              simp [hlt]
            rw [hval]
            exact hMod i hiA p hhard
          · subst heq
            have horig := Hints.origin_insertIdx_at A pos newPart hi
            rw [horig] at hhard
            simp [newPart] at hhard
          · have hiA : i - 1 < A.length := by
              rw [hlen_r] at hi
              omega
            have horig :=
              Hints.origin_insertIdx_of_gt A pos i newPart hi hiA hgt
            rw [horig] at hhard
            have hval :
                ((A.insertIdx pos newPart)[i]'hi).value = (A[i - 1]'hiA).value := by
              rw [List.getElem_insertIdx]
              simp [show ¬ i < pos from by omega, show i ≠ pos from by omega]
            rw [hval]
            exact hMod (i - 1) hiA p hhard

/-- A successful hard-insertion *step* (`tryHardInsertionLabeled`) preserves the
fact that every non-core (labeled) element has value divisible by `3`.  The new
hard has value `3 * (q - h)`; existing elements below `h` are raised by `3`
(value `+3`, mod-3 preserved) and the rest are unchanged. -/
private lemma tryHardInsertionLabeled_preserves_value_mod3
    {A r : List Labeled} {q h : ℕ}
    (hMod : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (htry : tryHardInsertionLabeled A q h = some r) :
    ∀ (i : ℕ) (hi : i < r.length),
      (r[i]'hi).origin ≠ none → (r[i]'hi).value % 3 = 0 := by
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf had
  push_neg at hf
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩ with hnp
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry
  have hlen_raised : raised.length = A.length := by simp [hraised]
  have hh_le : h ≤ A.length := hf.2
  subst hres
  have hlen : (raised.insertIdx h newPart).length = A.length + 1 := by
    rw [List.length_insertIdx]; simp [hlen_raised, hh_le]
  intro i hi hne
  rcases Nat.lt_trichotomy i h with hlt | heq | hgt
  · have hiA : i < A.length := by omega
    have hval : ((raised.insertIdx h newPart)[i]'hi).value = (A[i]'hiA).value + 3 := by
      rw [List.getElem_insertIdx]
      simp [hlt, hraised, List.getElem_map, List.getElem_zipIdx]
    have horig : ((raised.insertIdx h newPart)[i]'hi).origin = (A[i]'hiA).origin := by
      rw [List.getElem_insertIdx]
      simp [hlt, hraised, List.getElem_map, List.getElem_zipIdx]
    rw [horig] at hne
    have := hMod i hiA hne
    rw [hval]; omega
  · subst heq
    have hval : ((raised.insertIdx i newPart)[i]'hi).value = 3 * (q - i) := by
      rw [List.getElem_insertIdx_self (by rw [hlen]; omega)]
    rw [hval]; omega
  · have hiA : i - 1 < A.length := by omega
    have hval : ((raised.insertIdx h newPart)[i]'hi).value = (A[i - 1]'hiA).value := by
      rw [List.getElem_insertIdx]
      simp [show ¬ i < h by omega, show i ≠ h by omega, hraised,
        List.getElem_map, List.getElem_zipIdx, show ¬ i - 1 < h by omega]
    have horig : ((raised.insertIdx h newPart)[i]'hi).origin = (A[i - 1]'hiA).origin := by
      rw [List.getElem_insertIdx]
      simp [show ¬ i < h by omega, show i ≠ h by omega, hraised,
        List.getElem_map, List.getElem_zipIdx, show ¬ i - 1 < h by omega]
    rw [horig] at hne
    have := hMod (i - 1) hiA hne
    rw [hval]; exact this

/-- A successful easy-insertion step preserves "non-core ⇒ value `≡ 0 mod 3`":
the new easy has value `3 * q`; existing elements are unchanged. -/
private lemma tryEasyInsertionLabeled_preserves_value_mod3
    {A r : List Labeled} {q : ℕ}
    (hMod : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (htry : tryEasyInsertionLabeled A q = some r) :
    ∀ (i : ℕ) (hi : i < r.length),
      (r[i]'hi).origin ≠ none → (r[i]'hi).value % 3 = 0 := by
  unfold tryEasyInsertionLabeled at htry
  simp only at htry
  split_ifs at htry with hcond
  set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩ with hnp
  set pos := (A.takeWhile (·.value ≥ 3 * q)).length with hpos
  have hres : A.insertIdx pos newPart = r := Option.some.inj htry
  have hpos_le : pos ≤ A.length :=
    List.IsPrefix.length_le (List.takeWhile_prefix _)
  have hlen_r : r.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx]; simp [hpos_le]
  subst hres
  intro i hi hne
  rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
  · have hiA : i < A.length := by omega
    have hval : ((A.insertIdx pos newPart)[i]'hi).value = (A[i]'hiA).value := by
      rw [List.getElem_insertIdx]; simp [hlt]
    rw [hval]
    rw [Hints.origin_insertIdx_of_lt A pos i newPart hi hiA hlt] at hne
    exact hMod i hiA hne
  · subst heq
    have hval : ((A.insertIdx pos newPart)[pos]'hi).value = 3 * q := by
      rw [List.getElem_insertIdx_self (by omega)]
    rw [hval]; omega
  · have hiA : i - 1 < A.length := by rw [hlen_r] at hi; omega
    have hval : ((A.insertIdx pos newPart)[i]'hi).value = (A[i - 1]'hiA).value := by
      rw [List.getElem_insertIdx]
      simp [show ¬ i < pos by omega, show i ≠ pos by omega]
    rw [hval]
    rw [Hints.origin_insertIdx_of_gt A pos i newPart hi hiA hgt] at hne
    exact hMod (i - 1) hiA hne

/-- A successful hard-insertion *search* preserves "non-core ⇒ value `≡ 0 mod 3`". -/
private lemma findHardInsertionLabeled_preserves_value_mod3
    {A result : List Labeled} {q h₀ : ℕ}
    (hMod : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (hfind : findHardInsertionLabeled A q h₀ = some result) :
    ∀ (i : ℕ) (hi : i < result.length),
      (result[i]'hi).origin ≠ none → (result[i]'hi).value % 3 = 0 := by
  induction h₀ using findHardInsertionLabeled.induct A q with
  | case1 h hguard =>
      unfold findHardInsertionLabeled at hfind
      simp [hguard] at hfind
  | case2 h hguard r htry =>
      unfold findHardInsertionLabeled at hfind
      simp [hguard, htry] at hfind
      subst hfind
      exact tryHardInsertionLabeled_preserves_value_mod3 hMod htry
  | case3 h hguard htry_fail ih =>
      unfold findHardInsertionLabeled at hfind
      simp [hguard, htry_fail] at hfind
      exact ih hfind

/-- One labeled insertion step preserves "non-core ⇒ value `≡ 0 mod 3`". -/
private lemma performInsertionLabeled_preserves_value_mod3
    (A : List Labeled) (q : ℕ)
    (hMod : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0) :
    ∀ (i : ℕ) (hi : i < (performInsertionLabeled A q).length),
      ((performInsertionLabeled A q)[i]'hi).origin ≠ none →
        ((performInsertionLabeled A q)[i]'hi).value % 3 = 0 := by
  unfold performInsertionLabeled
  cases hf : findHardInsertionLabeled A q with
  | some r => exact findHardInsertionLabeled_preserves_value_mod3 hMod hf
  | none =>
      cases he : tryEasyInsertionLabeled A q with
      | none => simpa using hMod
      | some r => exact tryEasyInsertionLabeled_preserves_value_mod3 hMod he

/-- In the fully processed labeled insertion output, every hard label has value
divisible by `3`. -/
private lemma processInsertionsLabeled_hard_value_mod3
    (A_init : List Labeled) (ν : List ℕ)
    (hA_clean : ∀ x ∈ A_init, x.origin = none) :
    ∀ (i : ℕ) (hi : i < (processInsertionsLabeled ν A_init).length) (p : ℕ),
      ((processInsertionsLabeled ν A_init)[i]'hi).origin =
          some (p, InsertionKind.hard) →
        ((processInsertionsLabeled ν A_init)[i]'hi).value % 3 = 0 := by
  suffices hgen : ∀ (ν' : List ℕ) (A : List Labeled),
      (∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
        (A[i]'hi).origin = some (p, InsertionKind.hard) →
          (A[i]'hi).value % 3 = 0) →
      ∀ (i : ℕ) (hi : i < (processInsertionsLabeled ν' A).length) (p : ℕ),
        ((processInsertionsLabeled ν' A)[i]'hi).origin =
            some (p, InsertionKind.hard) →
          ((processInsertionsLabeled ν' A)[i]'hi).value % 3 = 0 by
    apply hgen ν A_init
    intro i hi p hhard
    have hnone := hA_clean (A_init[i]'hi) (List.getElem_mem hi)
    rw [hnone] at hhard
    cases hhard
  intro ν'
  induction ν' with
  | nil =>
      intro A hMod
      simpa only [processInsertionsLabeled] using hMod
  | cons q rest ih =>
      intro A hMod
      simp only [processInsertionsLabeled]
      exact ih (performInsertionLabeled A q)
        (performInsertionLabeled_preserves_hard_value_mod3 A q hMod)

/-- Hard-label value divisibility is preserved along arbitrary S2 prefixes,
because S2 only erases elements. -/
private lemma S2Reach_hard_value_mod3
    (A_init : List Labeled) (ν : List ℕ)
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (i : ℕ) (hi : i < B.length) (p : ℕ)
    (hhard : (B[i]'hi).origin = some (p, InsertionKind.hard)) :
    (B[i]'hi).value % 3 = 0 := by
  have hmem : B[i]'hi ∈ B := List.getElem_mem hi
  have hmem_start := S2Reach.mem_start hreach hmem
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem_start
  have hhard_start :
      ((processInsertionsLabeled ν A_init)[k]'hk).origin =
        some (p, InsertionKind.hard) := by
    rw [hget]
    exact hhard
  have hmod_start :=
    processInsertionsLabeled_hard_value_mod3 A_init ν hA_clean
      k hk p hhard_start
  rw [hget] at hmod_start
  exact hmod_start

/-! ## Hard lower-seam invariant (dual to CoreEasyGap) -/

private lemma getElem_length_takeWhile_value_ge_lt (A : List Labeled) (q : ℕ)
    (h : (A.takeWhile (·.value ≥ q)).length < A.length) :
    (A[(A.takeWhile (·.value ≥ q)).length]'h).value < q := by
  induction A with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    split
    · next hge =>
        simp only [List.length_cons, List.getElem_cons_succ]
        exact ih (by simp [hge] at h; omega)
    · next hlt_pred =>
        simp only [List.length_nil, List.getElem_cons_zero]
        simp only [decide_eq_true_eq, not_le] at hlt_pred
        exact hlt_pred

private def HardLowerGap (B : List Labeled) : Prop :=
  ∀ (i b : ℕ), i < b → ∀ (hi : i < B.length) (hb : b < B.length),
    0 < i →
    (B[i]'hi).origin.map Prod.snd = some InsertionKind.hard →
    (∀ (k : ℕ) (hk : k < B.length), i < k → k < b →
      (B[k]'hk).origin.map Prod.snd = some InsertionKind.easy) →
    (B[b]'hb).origin.map Prod.snd ≠ some InsertionKind.easy →
    (B[b]'hb).value + 3 ≤ (B[i-1]'(by omega)).value

private lemma HardLowerGap.of_clean {B : List Labeled}
    (hclean : ∀ x ∈ B, x.origin = none) :
    HardLowerGap B := by
  intro i b hib hi hb hipos hhard _ _
  exfalso
  have hnone : (B[i]'hi).origin = none := hclean _ (List.getElem_mem _)
  rw [hnone] at hhard; simp at hhard

private lemma forget_threeFlat_value_le {B : List Labeled}
    (hflat : IsThreeFlat (forget B)) {x y : ℕ} (hx : x < B.length) (hy : y < B.length)
    (hxy : x ≤ y) : (B[y]'hy).value ≤ (B[x]'hx).value := by
  rcases Nat.eq_or_lt_of_le hxy with h | h
  · subst h; exact le_refl _
  · have hpw := hflat.1.1
    have := List.pairwise_iff_getElem.mp hpw x y
      (by rw [length_forget]; exact hx) (by rw [length_forget]; exact hy) h
    simpa [forget, List.getElem_map] using this

private lemma tryEasyInsertionLabeled_preserves_HardLowerGap
    {A r : List Labeled} {p : ℕ}
    (hmod3A : ∀ (i : ℕ) (hi : i < A.length) (q : ℕ),
      (A[i]'hi).origin = some (q, InsertionKind.hard) → (A[i]'hi).value % 3 = 0)
    (htry : tryEasyInsertionLabeled A p = some r)
    (hA : HardLowerGap A) :
    HardLowerGap r := by
  unfold tryEasyInsertionLabeled at htry
  simp only at htry
  split at htry
  · rename_i hcond
    have hres := Option.some.inj htry
    set newPart : Labeled := ⟨3 * p, some (p, InsertionKind.easy)⟩ with hnp
    set pos := (A.takeWhile (·.value ≥ 3 * p)).length with hpos
    have hpos_le : pos ≤ A.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    subst hres
    have hflat_r : IsThreeFlat (forget (A.insertIdx pos newPart)) := by
      simp only [Bool.and_eq_true] at hcond
      exact isThreeFlatBool_implies' _ hcond.1
    have hlen : (A.insertIdx pos newPart).length = A.length + 1 := by
      rw [List.length_insertIdx]; simp [hpos_le]
    have getlt : ∀ (k : ℕ) (hkA : k < A.length) (hk : k < pos),
        (A.insertIdx pos newPart)[k]'(by rw [hlen]; omega) = A[k]'hkA := by
      intro k hkA hk
      rw [List.getElem_insertIdx]; simp [hk]
    have getgt : ∀ (k : ℕ) (hkA : k - 1 < A.length)
        (hkr : k < (A.insertIdx pos newPart).length) (hk : pos < k),
        (A.insertIdx pos newPart)[k]'hkr = A[k - 1]'hkA := by
      intro k hkA hkr hk
      rw [List.getElem_insertIdx]; simp [show ¬ k < pos by omega, show k ≠ pos by omega]
    intro i b hib hi hb hipos hhard hbet hbne
    have hane : i ≠ pos := by
      rintro rfl; rw [List.getElem_insertIdx_self (by omega)] at hhard; simp [hnp] at hhard
    have hbnepos : b ≠ pos := by
      rintro rfl; rw [List.getElem_insertIdx_self (by omega)] at hbne; simp [hnp] at hbne
    rcases Nat.lt_or_ge i pos with hipos2 | hipos2
    · have him1 : i - 1 < pos := by omega
      rcases Nat.lt_or_ge b pos with hbpos | hbpos
      · rw [getlt (i - 1) (by omega) him1, getlt b (by omega) hbpos]
        refine hA i b hib (by omega) (by omega) hipos ?_ ?_ ?_
        · rw [getlt i (by omega) hipos2] at hhard; exact hhard
        · intro k hkA hik hkb
          have hkr : k < (A.insertIdx pos newPart).length := by rw [hlen]; omega
          have := hbet k hkr hik (by omega)
          rwa [getlt k hkA (by omega)] at this
        · rw [getlt b (by omega) hbpos] at hbne; exact hbne
      · have hbgt : pos < b := by omega
        rw [getlt (i - 1) (by omega) him1, getgt b (by omega) hb hbgt]
        refine hA i (b - 1) (by omega) (by omega) (by omega) hipos ?_ ?_ ?_
        · rw [getlt i (by omega) hipos2] at hhard; exact hhard
        · intro k hkA hik hkb
          rcases Nat.lt_or_ge k pos with hkp | hkp
          · have hkr : k < (A.insertIdx pos newPart).length := by rw [hlen]; omega
            have := hbet k hkr hik (by omega)
            rwa [getlt k hkA hkp] at this
          · have hkr : k + 1 < (A.insertIdx pos newPart).length := by rw [hlen]; omega
            have := hbet (k + 1) hkr (by omega) (by omega)
            rw [getgt (k + 1) (by omega) hkr (by omega)] at this; simpa using this
        · rw [getgt b (by omega) hb hbgt] at hbne; exact hbne
    · have hbgt : pos < b := by omega
      rcases Nat.lt_or_ge pos (i - 1) with him1 | him1
      · rw [getgt (i - 1) (by omega) (by omega) him1, getgt b (by omega) hb hbgt]
        refine hA (i - 1) (b - 1) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
        · rw [getgt i (by omega) hi (by omega)] at hhard; simpa using hhard
        · intro k hkA hik hkb
          have hkr : k + 1 < (A.insertIdx pos newPart).length := by rw [hlen]; omega
          have := hbet (k + 1) hkr (by omega) (by omega)
          rw [getgt (k + 1) (by omega) hkr (by omega)] at this; simpa using this
        · rw [getgt b (by omega) hb hbgt] at hbne; exact hbne
      · have hieq : i = pos + 1 := by omega
        have hpos_lt_A : pos < A.length := by omega
        have hi1_val : ((A.insertIdx pos newPart)[i - 1]'(by omega)).value = 3 * p := by
          rw [List.getElem_insertIdx]
          simp [show ¬ (i - 1 < pos) by omega, show i - 1 = pos by omega, hnp]
        have hi_eq : (A.insertIdx pos newPart)[i]'hi = A[pos]'hpos_lt_A := by
          rw [getgt i (by omega) hi (by omega)]; congr 1; omega
        have hhardpos : (A[pos]'hpos_lt_A).origin.map Prod.snd = some InsertionKind.hard := by
          rw [← hi_eq]; exact hhard
        obtain ⟨⟨qh, kh⟩, hqh, hkh⟩ := Option.map_eq_some_iff.mp hhardpos
        have hkh' : kh = InsertionKind.hard := hkh
        subst hkh'
        have hApos_mod : (A[pos]'hpos_lt_A).value % 3 = 0 := hmod3A pos hpos_lt_A qh hqh
        have hApos_lt : (A[pos]'hpos_lt_A).value < 3 * p :=
          getElem_length_takeWhile_value_ge_lt A (3 * p) hpos_lt_A
        have hdesc : ((A.insertIdx pos newPart)[b]'hb).value ≤ (A[pos]'hpos_lt_A).value := by
          have h1 := forget_threeFlat_value_le hflat_r (x := i) (y := b) hi hb (by omega)
          rw [hi_eq] at h1; exact h1
        omega
  · exact absurd htry (by simp)

private lemma tryHardInsertionLabeled_preserves_HardLowerGap
    {A r : List Labeled} {q h : ℕ}
    (hflatA : IsThreeFlat (forget A))
    (hmod3A : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (htry : tryHardInsertionLabeled A q h = some r)
    (hA : HardLowerGap A) :
    HardLowerGap r := by
  have htry0 := htry
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf had
  push_neg at hf
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩ with hnp
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry
  have hlen_raised : raised.length = A.length := by simp [hraised]
  have hh_le : h ≤ A.length := hf.2
  subst hres
  have hflat_r : IsThreeFlat (forget (raised.insertIdx h newPart)) :=
    isThreeFlatBool_implies' _ had.1
  have hlen : (raised.insertIdx h newPart).length = A.length + 1 := by
    rw [List.length_insertIdx]; simp [hlen_raised, hh_le]
  have getlt : ∀ (k : ℕ) (hkA : k < A.length) (hk : k < h),
      ((raised.insertIdx h newPart)[k]'(by rw [hlen]; omega)).value
          = (A[k]'hkA).value + 3 ∧
        ((raised.insertIdx h newPart)[k]'(by rw [hlen]; omega)).origin
          = (A[k]'hkA).origin := by
    intro k hkA hk
    refine ⟨?_, ?_⟩ <;>
      · rw [List.getElem_insertIdx]
        simp [hk, hraised, List.getElem_map, List.getElem_zipIdx]
  have getgt : ∀ (k : ℕ) (hkA : k - 1 < A.length)
      (hkr : k < (raised.insertIdx h newPart).length) (hk : h < k),
      (raised.insertIdx h newPart)[k]'hkr = A[k - 1]'hkA := by
    intro k hkA hkr hk
    rw [List.getElem_insertIdx]
    simp [show ¬ k < h by omega, show k ≠ h by omega, hraised,
      List.getElem_map, List.getElem_zipIdx, show ¬ k - 1 < h by omega]
  have get_h : (raised.insertIdx h newPart)[h]'(by rw [hlen]; omega) = newPart := by
    rw [List.getElem_insertIdx_self (by rw [hlen]; omega)]
  -- Consecutive 3-flat gap, transported into value-space of `result`.
  have vgap : ∀ (k : ℕ) (hk1 : k + 1 < (raised.insertIdx h newPart).length),
      ((raised.insertIdx h newPart)[k]'(by omega)).value
        - ((raised.insertIdx h newPart)[k + 1]'hk1).value < 3 := by
    intro k hk1
    have hg := hflat_r.2.1 k (by rw [length_forget]; exact hk1)
    simpa [forget, List.getElem_map] using hg
  -- Descending order in value-space of `result`.
  have vle : ∀ (x y : ℕ) (hx : x < (raised.insertIdx h newPart).length)
      (hy : y < (raised.insertIdx h newPart).length), x ≤ y →
      ((raised.insertIdx h newPart)[y]'hy).value
        ≤ ((raised.insertIdx h newPart)[x]'hx).value := by
    intro x y hx hy hxy
    exact forget_threeFlat_value_le hflat_r hx hy hxy
  intro i b hib hi hb hipos hhard hbet hbne
  rcases Nat.lt_trichotomy i h with hih | hih | hih
  · obtain ⟨hvi1, hoi1⟩ := getlt (i - 1) (by omega) (by omega)
    obtain ⟨hvi, hoi⟩ := getlt i (by omega) hih
    rcases Nat.lt_trichotomy b h with hbh | hbh | hbh
    · obtain ⟨hvb, hob⟩ := getlt b (by omega) hbh
      rw [hvi1, hvb]
      have hmain := hA i b hib (by omega) (by omega) hipos (by rw [← hoi]; exact hhard)
        ?_ (by rw [← hob]; exact hbne)
      · omega
      · intro k hkA hik hkb
        have hkr : k < (raised.insertIdx h newPart).length := by rw [hlen]; omega
        have hb2 := hbet k hkr hik (by omega)
        obtain ⟨_, hok⟩ := getlt k hkA (by omega)
        rwa [hok] at hb2
    · -- b = h: the new hard `newPart` is itself the boundary below the existing
      -- hard's run.  Goal: `result[b].value + 3 ≤ result[i-1].value`, i.e.
      -- `newPart.value + 3 ≤ A[i-1].value + 3`, i.e. `newPart.value ≤ A[i-1].value`.
      subst b
      -- `h < A.length`: otherwise `newPart` (value `3*(q-h) ≥ 3`) is the last
      -- element, contradicting 3-flatness (`getLast < 3`).
      have hhA : h < A.length := by
        by_contra hge
        have hheq : h = A.length := by omega
        have hne : forget (raised.insertIdx h newPart) ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [length_forget, hlen]; omega
        have hlast_lt3 := hflat_r.2.2 hne
        have hLlen : (raised.insertIdx h newPart).length - 1 = h := by rw [hlen]; omega
        have hlast_eq : (forget (raised.insertIdx h newPart)).getLast hne
            = ((raised.insertIdx h newPart)[(raised.insertIdx h newPart).length - 1]'(by omega)).value := by
          rw [List.getLast_eq_getElem]
          simp [forget, List.getElem_map, length_forget]
        rw [hlast_eq] at hlast_lt3
        have hval_last : ((raised.insertIdx h newPart)[
            (raised.insertIdx h newPart).length - 1]'(by omega)).value = newPart.value := by
          have he : ((raised.insertIdx h newPart)[
              (raised.insertIdx h newPart).length - 1]'(by omega))
              = ((raised.insertIdx h newPart)[h]'(by rw [hlen]; omega)) := by
            congr 1
          rw [he, get_h]
        rw [hval_last] at hlast_lt3
        have hnpval : newPart.value = 3 * (q - h) := by rw [hnp]
        rw [hnpval] at hlast_lt3
        have hhq : h < q := hf.1
        omega
      -- `result[b] = result[h] = newPart` (value `3*(q-h)`).
      have hvb : ((raised.insertIdx h newPart)[h]'hb).value = newPart.value := by
        rw [show ((raised.insertIdx h newPart)[h]'hb) = newPart from get_h]
      -- `result[h+1] = A[h]`.
      have hAh_get : ((raised.insertIdx h newPart)[h + 1]'(by rw [hlen]; omega)).value
          = (A[h]'(by omega)).value := by
        rw [getgt (h + 1) (by omega) (by rw [hlen]; omega) (by omega)]
        simp only [Nat.add_sub_cancel]
      -- 3-flat gap at h: `newPart.value - A[h].value < 3`.
      have hgaph := vgap h (by rw [hlen]; omega)
      have hgeth : ((raised.insertIdx h newPart)[h]'(by omega)).value = newPart.value := by
        rw [show ((raised.insertIdx h newPart)[h]'(by omega)) = newPart from get_h]
      rw [hgeth, hAh_get] at hgaph
      -- descending order `A[h].value ≤ newPart.value`.
      have hdeschh : (A[h]'(by omega)).value ≤ newPart.value := by
        have := vle h (h + 1) (by rw [hlen]; omega) (by rw [hlen]; omega) (by omega)
        rwa [hgeth, hAh_get] at this
      have hnp_mod : newPart.value % 3 = 0 := by rw [hnp]; exact Nat.mul_mod_right 3 (q - h)
      -- Determine whether `A[h]` is easy.
      by_cases heasyAh :
          (A[h]'(by omega)).origin.map Prod.snd = some InsertionKind.easy
      · -- `A[h]` easy ⇒ `A[h].value ≡ 0 mod 3`.  Then `newPart.value = A[h].value`,
        -- and the gap at `h-1` (`result[h-1] = A[h-1]+3`) forces
        -- `A[h-1].value < A[h].value`, contradicting descending order.  Vacuous.
        exfalso
        have hAh_ne : (A[h]'(by omega)).origin ≠ none := by
          intro hnone; rw [hnone] at heasyAh; simp at heasyAh
        have hAh_mod : (A[h]'(by omega)).value % 3 = 0 := hmod3A h (by omega) hAh_ne
        -- `result[h-1].value = A[h-1].value + 3`.
        obtain ⟨hvh1, _⟩ := getlt (h - 1) (by omega) (by omega)
        -- gap at `h-1`: `result[h-1].value - result[h].value < 3`.
        have hgaph1 := vgap (h - 1) (by rw [hlen]; omega)
        have hgeth' : ((raised.insertIdx h newPart)[h - 1 + 1]'(by rw [hlen]; omega)).value
            = newPart.value := by
          rw [List.getElem_insertIdx]
          simp [show ¬ (h - 1 + 1 < h) by omega, show h - 1 + 1 = h by omega]
        rw [hvh1, hgeth'] at hgaph1
        -- descending in A: `A[h].value ≤ A[h-1].value`.
        have hAdesc := forget_threeFlat_value_le hflatA
          (x := h - 1) (y := h) (by omega) (by omega) (by omega)
        omega
      · -- `A[h]` non-easy ⇒ apply old seam `hA` at `(i, h)`.
        have hAi_hard : (A[i]'(by omega)).origin.map Prod.snd = some InsertionKind.hard := by
          rw [← hoi]; exact hhard
        have hrun : ∀ (k : ℕ) (hk : k < A.length), i < k → k < h →
            (A[k]'hk).origin.map Prod.snd = some InsertionKind.easy := by
          intro k hkA hik hkh
          have hkr : k < (raised.insertIdx h newPart).length := by rw [hlen]; omega
          have hb2 := hbet k hkr hik hkh
          obtain ⟨_, hok⟩ := getlt k hkA hkh
          rwa [hok] at hb2
        have hseam := hA i h hih (by omega) (by omega) hipos hAi_hard hrun heasyAh
        -- Goal: `result[h].value + 3 ≤ result[i-1].value`.
        rw [hvb, hvi1]
        -- `newPart.value < A[h].value + 3 ≤ A[i-1].value`.
        omega
    · exfalso
      have hkr : h < (raised.insertIdx h newPart).length := by rw [hlen]; omega
      have := hbet h hkr hih hbh
      rw [get_h] at this; simp [hnp] at this
  · subst hih
    obtain ⟨hvi1, _⟩ := getlt (i - 1) (by omega) (by omega)
    have hseam := tryHardInsertionLabeled_new_hard_neighbor_lower_seam hflatA htry0 hipos
    have hi1_lt : i + 1 < (raised.insertIdx i newPart).length := by rw [hlen]; omega
    have hdesc := forget_threeFlat_value_le hflat_r (x := i + 1) (y := b) hi1_lt hb (by omega)
    rw [hvi1] at hseam ⊢
    omega
  · rcases Nat.lt_or_ge h (i - 1) with him1 | him1
    · rw [getgt (i - 1) (by omega) (by omega) him1, getgt b (by omega) hb (by omega)]
      refine hA (i - 1) (b - 1) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
      · rw [getgt i (by omega) hi hih] at hhard; simpa using hhard
      · intro k hkA hik hkb
        have hkr : k + 1 < (raised.insertIdx h newPart).length := by rw [hlen]; omega
        have hb2 := hbet (k + 1) hkr (by omega) (by omega)
        rw [getgt (k + 1) (by omega) hkr (by omega)] at hb2; simpa using hb2
      · rw [getgt b (by omega) hb (by omega)] at hbne; simpa using hbne
    · -- i = h + 1: `result[h] = newPart` and `result[h+1] = A[h]` are *adjacent
      -- equal hards*, which is impossible in a 3-flat list.
      exfalso
      have hieq : i = h + 1 := by omega
      -- `result[i] = A[i-1] = A[h]` is hard.
      have hAget : (raised.insertIdx h newPart)[i]'hi = A[i - 1]'(by omega) :=
        getgt i (by omega) hi hih
      have hAeq : A[i - 1]'(by omega) = A[h]'(by omega) := by congr 1; omega
      have hAh_hard : (A[h]'(by omega)).origin.map Prod.snd = some InsertionKind.hard := by
        rw [← hAeq, ← hAget]; exact hhard
      have hAh_ne : (A[h]'(by omega)).origin ≠ none := by
        intro hnone; rw [hnone] at hAh_hard; simp at hAh_hard
      have hAh_mod : (A[h]'(by omega)).value % 3 = 0 := hmod3A h (by omega) hAh_ne
      have hnp_mod : newPart.value % 3 = 0 := by rw [hnp]; exact Nat.mul_mod_right 3 (q - h)
      rcases Nat.eq_zero_or_pos h with hh0 | hhpos
      · -- h = 0: a hard insertion at position 0 is itself flat-removable
        -- (erasing it leaves the already-3-flat `A`), contradicting the guard.
        subst hh0
        have hraised_eq : forget raised = forget A := by
          apply List.ext_getElem
          · rw [length_forget, length_forget, hlen_raised]
          · intro k hk1 hk2
            rw [length_forget, hlen_raised] at hk1
            simp only [forget, List.getElem_map, hraised, List.getElem_map,
              List.getElem_zipIdx, Nat.not_lt_zero, if_false]
        have hFR : isFlatRemovableBool (forget (raised.insertIdx 0 newPart)) 0 = true := by
          unfold isFlatRemovableBool
          have hlen0 : 0 < (forget (raised.insertIdx 0 newPart)).length := by
            rw [length_forget, hlen]; omega
          have h0val : (forget (raised.insertIdx 0 newPart))[0]'hlen0 = newPart.value := by
            simp only [forget, List.getElem_map]
            rw [List.getElem_insertIdx_self (by rw [hlen]; omega)]
          have herase : (forget (raised.insertIdx 0 newPart)).eraseIdx 0 = forget A := by
            rw [Hints.forget_insertIdx, List.eraseIdx_insertIdx_self, hraised_eq]
          rw [herase]
          have hflatBool : isThreeFlatBool (forget A) = true :=
            Hints.isThreeFlatBool_of_IsThreeFlat hflatA
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          refine ⟨⟨hlen0, ?_⟩, hflatBool⟩
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen0, Option.getD_some,
            h0val, hnp]
          exact Nat.mul_mod_right 3 (q - 0)
        rw [hFR] at had
        simp at had
      · -- h > 0: descending order + 3-flat gaps give `A[h-1].value < A[h].value`,
        -- contradicting the descending order `A[h].value ≤ A[h-1].value`.
        -- `result[h].value = newPart.value`.
        have hgeth : ((raised.insertIdx h newPart)[h]'(by rw [hlen]; omega)).value
            = newPart.value := by
          rw [show ((raised.insertIdx h newPart)[h]'(by rw [hlen]; omega)) = newPart from get_h]
        -- `result[h+1].value = A[h].value`.
        have hgeth1 : ((raised.insertIdx h newPart)[h + 1]'(by rw [hlen]; omega)).value
            = (A[h]'(by omega)).value := by
          rw [getgt (h + 1) (by omega) (by rw [hlen]; omega) (by omega)]
          simp only [Nat.add_sub_cancel]
        -- gap at h: `newPart.value - A[h].value < 3`.
        have hgaph := vgap h (by rw [hlen]; omega)
        rw [hgeth, hgeth1] at hgaph
        -- descending `A[h].value ≤ newPart.value`.
        have hdesch : (A[h]'(by omega)).value ≤ newPart.value := by
          have := vle h (h + 1) (by rw [hlen]; omega) (by rw [hlen]; omega) (by omega)
          rwa [hgeth, hgeth1] at this
        -- `result[h-1].value = A[h-1].value + 3`.
        obtain ⟨hvh1, _⟩ := getlt (h - 1) (by omega) (by omega)
        -- gap at `h-1`: `result[h-1].value - result[h].value < 3`.
        have hgaph1 := vgap (h - 1) (by rw [hlen]; omega)
        have hgeth' : ((raised.insertIdx h newPart)[h - 1 + 1]'(by rw [hlen]; omega)).value
            = newPart.value := by
          rw [List.getElem_insertIdx]
          simp [show ¬ (h - 1 + 1 < h) by omega, show h - 1 + 1 = h by omega]
        rw [hvh1, hgeth'] at hgaph1
        -- descending in A: `A[h].value ≤ A[h-1].value`.
        have hAdesc := forget_threeFlat_value_le hflatA
          (x := h - 1) (y := h) (by omega) (by omega) (by omega)
        omega

private lemma findHardInsertionLabeled_preserves_HardLowerGap
    {A : List Labeled} {p h₀ : ℕ} {result : List Labeled}
    (hflatA : IsThreeFlat (forget A))
    (hmod3A : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (hfind : findHardInsertionLabeled A p h₀ = some result)
    (hA : HardLowerGap A) :
    HardLowerGap result := by
  have hmotive : ∀ h, findHardInsertionLabeled A p h = some result → HardLowerGap result :=
    findHardInsertionLabeled.induct A p
      (motive := fun h => findHardInsertionLabeled A p h = some result → HardLowerGap result)
      (fun h hguard hfind => by simp [findHardInsertionLabeled, hguard] at hfind)
      (fun h hguard rr htry hfind => by
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry] at hfind
        subst hfind
        exact tryHardInsertionLabeled_preserves_HardLowerGap hflatA hmod3A htry hA)
      (fun h hguard htry_fail ih hfind => by
        unfold findHardInsertionLabeled at hfind
        simp [hguard, htry_fail] at hfind
        exact ih hfind)
  exact hmotive h₀ hfind

private lemma performInsertionLabeled_preserves_HardLowerGap
    {A : List Labeled} {p : ℕ}
    (hflatA : IsThreeFlat (forget A))
    (hmod3A : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (hA : HardLowerGap A) :
    HardLowerGap (performInsertionLabeled A p) := by
  -- The easy-insertion seam-preservation only needs the hard-mod3 specialization.
  have hmod3hard : ∀ (i : ℕ) (hi : i < A.length) (q : ℕ),
      (A[i]'hi).origin = some (q, InsertionKind.hard) → (A[i]'hi).value % 3 = 0 := by
    intro i hi q hq
    exact hmod3A i hi (by rw [hq]; simp)
  unfold performInsertionLabeled
  cases hfind : findHardInsertionLabeled A p with
  | some rr =>
    simp only [hfind]
    exact findHardInsertionLabeled_preserves_HardLowerGap hflatA hmod3A hfind hA
  | none =>
    simp only [hfind]
    cases heasy : tryEasyInsertionLabeled A p with
    | some rr =>
      simp only [heasy]
      exact tryEasyInsertionLabeled_preserves_HardLowerGap hmod3hard heasy hA
    | none => simp only [heasy]; exact hA

private lemma processInsertionsLabeled_HardLowerGap
    (ν : List ℕ) (A : List Labeled)
    (hflatA : IsThreeFlat (forget A))
    (hmod3A : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin ≠ none → (A[i]'hi).value % 3 = 0)
    (hA : HardLowerGap A) :
    HardLowerGap (processInsertionsLabeled ν A) := by
  induction ν generalizing A with
  | nil => simpa [processInsertionsLabeled] using hA
  | cons p rest ih =>
    simp only [processInsertionsLabeled]
    refine ih (performInsertionLabeled A p) ?_ ?_
      (performInsertionLabeled_preserves_HardLowerGap hflatA hmod3A hA)
    · have hf : IsThreeFlat (performInsertion (forget A) p) :=
        performInsertion_preserves_flat' (forget A) p hflatA
      rwa [← forget_performInsertionLabeled] at hf
    · exact performInsertionLabeled_preserves_value_mod3 A p hmod3A

/-! ### NoHardAtZero invariant for processInsertionsLabeled. -/

/-- Position 0 of `A` is never hard-labeled. -/
private def NoHardAtZero (A : List Labeled) : Prop :=
  ∀ (h : 0 < A.length),
    (A[0]'h).origin.map Prod.snd ≠ some InsertionKind.hard

/-- A successful `tryHardInsertionLabeled` on a 3-flat input has `1 ≤ h`.
Mirrors the closed sub-proof inside
`tryHardInsertionLabeled_preserves_HardHasSupportingEasy` at L5283-L5313. -/
private lemma tryHardInsertionLabeled_h_pos
    {A r : List Labeled} {q h : ℕ}
    (hflat : IsThreeFlat (forget A))
    (htry : tryHardInsertionLabeled A q h = some r) :
    1 ≤ h := by
  rcases Nat.eq_zero_or_pos h with hh0 | hh
  swap
  · exact hh
  -- h = 0: derive contradiction.
  subst hh0
  exfalso
  have htry_orig := htry
  have hadm := tryHardInsertionLabeled_admissibility_at_h htry_orig
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf hadm_check
  push_neg at hf
  set newPart : Labeled := ⟨3 * (q - 0), some (q, InsertionKind.hard)⟩ with hnewPart_def
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < 0 then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised_def
  have hres : raised.insertIdx 0 newPart = r := Option.some.inj htry
  have hraised_eq_A : raised = A := by
    apply List.ext_getElem
    · simp [hraised_def]
    · intro k hk1 hk2
      simp [hraised_def, List.getElem_map, List.getElem_zipIdx]
  have hr_eq : r = newPart :: A := by
    rw [← hres, hraised_eq_A, List.insertIdx_zero]
  have hforget_r : forget r = 3 * q :: forget A := by
    rw [hr_eq]; simp [forget, hnewPart_def]
  have hFR : isFlatRemovableBool (forget r) 0 = true := by
    unfold isFlatRemovableBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hforget_r]; simp
    · rw [hforget_r]
      rw [getElem!_pos _ 0 (by simp)]
      simp
    · rw [hforget_r]
      show isThreeFlatBool ((3 * q :: forget A).eraseIdx 0) = true
      simp only [List.eraseIdx_cons_zero]
      exact Hints.isThreeFlatBool_of_IsThreeFlat hflat
  rw [hFR] at hadm
  cases hadm

/-- Position 0 of a `tryHardInsertionLabeled` result (with `h ≥ 1`) preserves
the origin of position 0 of the input. -/
private lemma tryHardInsertionLabeled_pos_zero_origin
    {A r : List Labeled} {q h : ℕ}
    (hh : 1 ≤ h)
    (hA_lt : 0 < A.length)
    (htry : tryHardInsertionLabeled A q h = some r) :
    ∃ hr : 0 < r.length, (r[0]'hr).origin = (A[0]'hA_lt).origin := by
  unfold tryHardInsertionLabeled at htry
  simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
  split_ifs at htry with hf hadm_check
  push_neg at hf
  set newPart : Labeled := ⟨3 * (q - h), some (q, InsertionKind.hard)⟩ with hnewPart_def
  set raised : List Labeled :=
    A.zipIdx.map (fun x : Labeled × ℕ =>
      if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
    with hraised_def
  have hres : raised.insertIdx h newPart = r := Option.some.inj htry
  have hlen_raised : raised.length = A.length := by simp [hraised_def]
  have hlen_r : r.length = A.length + 1 := by
    rw [← hres, List.length_insertIdx, hlen_raised]; simp [hf.2]
  refine ⟨by omega, ?_⟩
  have h0_lt_ins : 0 < (raised.insertIdx h newPart).length := by
    rw [List.length_insertIdx]; split <;> omega
  have hget : r[0]'(by omega) = (raised.insertIdx h newPart)[0]'h0_lt_ins := by
    congr 1; exact hres.symm
  rw [hget, List.getElem_insertIdx]
  simp only [show 0 < h from hh, dite_true]
  simp [hraised_def, List.getElem_map, List.getElem_zipIdx, show 0 < h from hh]

/-- Position 0 of any `tryEasyInsertionLabeled` result is not hard. -/
private lemma tryEasyInsertionLabeled_pos_zero_not_hard
    {A r : List Labeled} {q : ℕ}
    (hA : NoHardAtZero A)
    (htry : tryEasyInsertionLabeled A q = some r) :
    ∀ (hr : 0 < r.length),
      (r[0]'hr).origin.map Prod.snd ≠ some InsertionKind.hard := by
  unfold tryEasyInsertionLabeled at htry
  simp only at htry
  split at htry
  swap
  · simp at htry
  -- success branch
  intro hr
  have hres := Option.some.inj htry
  subst hres
  set newPart : Labeled := ⟨3 * q, some (q, .easy)⟩ with hnewPart_def
  set pos := (A.takeWhile (·.value ≥ 3 * q)).length with hpos_def
  have hpos_le : pos ≤ A.length := List.IsPrefix.length_le (List.takeWhile_prefix _)
  by_cases hpos_pos : 0 < pos
  · -- pos > 0: r[0] = A[0] (origin preserved)
    have hA_pos : 0 < A.length := by omega
    have hr_eq : (List.insertIdx A pos newPart)[0]'hr = A[0]'hA_pos := by
      rw [List.getElem_insertIdx, dif_pos hpos_pos]
    rw [hr_eq]
    exact hA hA_pos
  · -- pos = 0: r[0] = newPart (easy)
    push_neg at hpos_pos
    have hpos_zero : pos = 0 := Nat.le_zero.mp hpos_pos
    have hr_eq : (List.insertIdx A pos newPart)[0]'hr = newPart := by
      rw [List.getElem_insertIdx,
          dif_neg (show ¬(0 < pos) from by omega),
          dif_pos (show (0 : ℕ) = pos from hpos_zero.symm)]
    rw [hr_eq, hnewPart_def]
    simp

/-- `findHardInsertionLabeled` success: extract a witness `h` with `1 ≤ h`. -/
private lemma findHardInsertionLabeled_some_h_pos
    {A : List Labeled} {q : ℕ} {r : List Labeled}
    (hflat : IsThreeFlat (forget A))
    (hfind : findHardInsertionLabeled A q 0 = some r) :
    ∃ h, 1 ≤ h ∧ tryHardInsertionLabeled A q h = some r := by
  suffices hgen : ∀ (h₀ : ℕ),
      findHardInsertionLabeled A q h₀ = some r →
      ∃ h, h₀ ≤ h ∧ tryHardInsertionLabeled A q h = some r by
    obtain ⟨h, _, htry⟩ := hgen 0 hfind
    exact ⟨h, tryHardInsertionLabeled_h_pos hflat htry, htry⟩
  intro h₀
  induction h₀ using findHardInsertionLabeled.induct A q with
  | case1 h hguard =>
      intro hfind
      unfold findHardInsertionLabeled at hfind
      simp [hguard] at hfind
  | case2 h hguard r_h htry =>
      intro hfind
      unfold findHardInsertionLabeled at hfind
      simp [hguard, htry] at hfind
      subst hfind
      exact ⟨h, le_refl h, htry⟩
  | case3 h hguard htry_fail ih =>
      intro hfind
      unfold findHardInsertionLabeled at hfind
      simp [hguard, htry_fail] at hfind
      obtain ⟨h', hh', htry'⟩ := ih hfind
      exact ⟨h', by omega, htry'⟩

/-- `performInsertionLabeled` preserves `NoHardAtZero`. -/
private lemma performInsertionLabeled_preserves_NoHardAtZero
    {A : List Labeled} {p : ℕ}
    (hflat : IsThreeFlat (forget A))
    (hA : NoHardAtZero A) :
    NoHardAtZero (performInsertionLabeled A p) := by
  unfold performInsertionLabeled
  cases hf : findHardInsertionLabeled A p with
  | some r =>
      intro hr
      obtain ⟨h, hh, htry⟩ := findHardInsertionLabeled_some_h_pos hflat hf
      have h_le_A : h ≤ A.length := by
        unfold tryHardInsertionLabeled at htry
        simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
        split_ifs at htry with hf'
        push_neg at hf'
        exact hf'.2
      have hA_lt : 0 < A.length := by omega
      obtain ⟨_, h_origin_eq⟩ := tryHardInsertionLabeled_pos_zero_origin hh hA_lt htry
      rw [h_origin_eq]
      exact hA hA_lt
  | none =>
      cases hte : tryEasyInsertionLabeled A p with
      | some r =>
          exact tryEasyInsertionLabeled_pos_zero_not_hard hA hte
      | none =>
          exact hA

/-- `processInsertionsLabeled` preserves `NoHardAtZero` along the ν-induction. -/
private lemma processInsertionsLabeled_NoHardAtZero
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none) :
    NoHardAtZero (processInsertionsLabeled ν A_init) := by
  suffices hgen : ∀ (ν' : List ℕ) (A : List Labeled),
      IsThreeFlat (forget A) →
      NoHardAtZero A →
      NoHardAtZero (processInsertionsLabeled ν' A) by
    apply hgen ν A_init hA_flat
    intro hpos
    have hmem : A_init[0]'hpos ∈ A_init := List.getElem_mem hpos
    rw [hA_clean _ hmem]; simp
  intro ν' A hAflat hAzero
  induction ν' generalizing A with
  | nil =>
      simp only [processInsertionsLabeled]
      exact hAzero
  | cons p rest ih =>
      simp only [processInsertionsLabeled]
      apply ih
      · rw [forget_performInsertionLabeled]
        exact performInsertion_preserves_flat' (forget A) p hAflat
      · exact performInsertionLabeled_preserves_NoHardAtZero hAflat hAzero

/-! `NoHardAtZero` is NOT preserved under arbitrary `S2Reach` erasures: -/

/-- Pre-to-post FR transfer in the non-adjacent case.  The reverse direction
of `isFlatRemovableBool_transfer_left`: if `j` and `actualIdx` are both FR
in `L` and they are not adjacent (`j + 1 < actualIdx`), then `j` remains FR
in `L.eraseIdx actualIdx`. Used to close the non-boundary case of
`AllRemainingEasyFR` post-erase. -/
private lemma isFlatRemovableBool_post_erase_non_adjacent
    (L : List ℕ) (j actualIdx : ℕ)
    (hj_lt : j + 1 < actualIdx) (hact_lt : actualIdx < L.length)
    (h_fr_act : isFlatRemovableBool L actualIdx = true)
    (h_fr_j : isFlatRemovableBool L j = true) :
    isFlatRemovableBool (L.eraseIdx actualIdx) j = true := by
  unfold isFlatRemovableBool at h_fr_act h_fr_j ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h_fr_act h_fr_j ⊢
  obtain ⟨⟨hj_lt_L, hmod_j⟩, hflat_erase_j⟩ := h_fr_j
  obtain ⟨⟨_, _⟩, hflat_erase_act⟩ := h_fr_act
  have hlen_erase_act : (L.eraseIdx actualIdx).length = L.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hj_lt_erase : j < (L.eraseIdx actualIdx).length := by
    rw [hlen_erase_act]; omega
  refine ⟨⟨hj_lt_erase, ?_⟩, ?_⟩
  · -- (L.eraseIdx actualIdx)[j]! % 3 = 0
    rw [getElem!_pos (L.eraseIdx actualIdx) j hj_lt_erase]
    have heq : (L.eraseIdx actualIdx)[j]'hj_lt_erase = L[j]'hj_lt_L := by
      rw [List.getElem_eraseIdx]; simp [show j < actualIdx from by omega]
    rw [heq]
    rw [getElem!_pos L j hj_lt_L] at hmod_j
    exact hmod_j
  · -- isThreeFlatBool ((L.eraseIdx actualIdx).eraseIdx j) = true
    apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap _ j hj_lt_erase hflat_erase_act
    · -- gap < 3
      intro hj_pos hj1_in_erase
      have hj1_lt_actual : j + 1 < actualIdx := hj_lt
      have hjm1_lt_actual : j - 1 < actualIdx := by omega
      have heq_jm1 : (L.eraseIdx actualIdx)[j - 1]'(by rw [hlen_erase_act]; omega) =
          L[j - 1]'(by omega) := by
        rw [List.getElem_eraseIdx]; simp [hjm1_lt_actual]
      have heq_j1 : (L.eraseIdx actualIdx)[j + 1]'hj1_in_erase = L[j + 1]'(by omega) := by
        rw [List.getElem_eraseIdx]; simp [hj1_lt_actual]
      rw [heq_jm1, heq_j1]
      -- Now: L[j-1] - L[j+1] < 3 from seam of erase at j in L (3-flatness of L.eraseIdx j).
      have hflat_erase_j' := isThreeFlatBool_implies' _ hflat_erase_j
      obtain ⟨_, hgaps_j, _⟩ := hflat_erase_j'
      have hlen_erase_j : (L.eraseIdx j).length = L.length - 1 :=
        List.length_eraseIdx_of_lt hj_lt_L
      have hjm1_in_erase_j : (j - 1) + 1 < (L.eraseIdx j).length := by
        rw [hlen_erase_j]; omega
      have hgap_j := hgaps_j (j - 1) hjm1_in_erase_j
      have he_jm1 : (L.eraseIdx j)[j - 1]'(by rw [hlen_erase_j]; omega) = L[j - 1]'(by omega) := by
        rw [List.getElem_eraseIdx]; simp [show j - 1 < j from by omega]
      have he_j : (L.eraseIdx j)[(j - 1) + 1]'hjm1_in_erase_j = L[j + 1]'(by omega) := by
        rw [List.getElem_eraseIdx]
        simp [show ¬((j - 1) + 1 < j) from by omega]
        congr 1; omega
      rw [he_jm1, he_j] at hgap_j
      exact hgap_j
    · -- last bound is vacuous: j + 1 < actualIdx ≤ L.length - 1 + 1, so j + 1 < L.length,
      -- and (L.eraseIdx actualIdx).length = L.length - 1, so j + 1 = (L.eraseIdx actualIdx).length
      -- iff j + 1 = L.length - 1, but we have j + 1 < actualIdx ≤ L.length - 1, so j + 1 < L.length - 1.
      intro hj1_eq _
      rw [hlen_erase_act] at hj1_eq
      exfalso; omega

/-- While the S2 frontier is not at the bottom, position 0 is not hard.

`NoHardAtZero` is not preserved after erasing index 0, but such an erase
terminates the bottom-up scan (`idx` becomes the new length).  The strictly
pre-terminal form below is the preserved fact needed by the hard/support
boundary case with frontier index 1. -/
private def NoHardAtZeroBeforeLast (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (hidx : idx + 1 < B.length) (h0 : 0 < B.length),
    (B[0]'h0).origin.map Prod.snd ≠ some InsertionKind.hard

/-- `NoHardAtZeroBeforeLast` holds throughout the S2 scan.

The only S2 erase that can shift position 1 to position 0 is erasing
`actualIdx = 0`; after that erase, `idx` is the new length, so the
pre-terminal premise `idx + 1 < length` is false. -/
private lemma S2Reach_NoHardAtZeroBeforeLast
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Reach labeled B idx rec → NoHardAtZeroBeforeLast B idx := by
  intro labeled B idx rec hreach
  refine S2Reach.rec (motive := fun B idx _ _ => NoHardAtZeroBeforeLast B idx)
    ?init ?eraseCase ?skipCase hreach
  · show NoHardAtZeroBeforeLast (processInsertionsLabeled ν A_init) 0
    intro _ h0
    exact processInsertionsLabeled_NoHardAtZero
      A_init ν hA_flat hA_clean h0
  · intro B' idx' actualIdx' rec' hidx hactual hfr hprev ih
    intro hidx_pre h0_post
    have hact_lt : actualIdx' < B'.length := by omega
    have hlen_post : (B'.eraseIdx actualIdx').length = B'.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    have hact_ge_two : 2 ≤ actualIdx' := by
      rw [hactual]
      rw [hlen_post] at hidx_pre
      omega
    have h0_B' : 0 < B'.length := by omega
    have h0_eq :
        (B'.eraseIdx actualIdx')[0]'h0_post = B'[0]'h0_B' := by
      rw [List.getElem_eraseIdx]
      simp [show (0 : ℕ) < actualIdx' from by omega]
    rw [h0_eq]
    exact ih (by rw [hactual] at hact_ge_two; omega) h0_B'
  · intro B' idx' actualIdx' rec' hidx hactual hnfr hprev ih
    intro hidx_pre h0
    exact ih (by omega) h0

private def S2EasyBoundarySeamGuarded (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (j : ℕ) (hj : j < B.length),
    0 < j →
    (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy →
    isFlatRemovableBool (forget B) j = true →
    isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
    j < B.length - 1 - idx →
    j + 1 = B.length - 1 - idx →
      ∀ (hj1_lt : j + 1 < ((forget B).eraseIdx (B.length - 1 - idx)).length),
        ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) -
          ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt < 3

/-- Guarded form of `S2HardBoundarySeam`, matching exactly the interior
history fact needed by `s2reach_hardSupport_boundary_contradicts_FR`.

The contradiction proof separately extracts the post-delete `< 3` seam from
`hfr_post`; this predicate supplies only the construction-history `≥ 3` lower
bound, under the hard/support/frontier hypotheses present at that call site. -/
private def S2HardBoundarySeamGuarded (B : List Labeled) (idx : ℕ) : Prop :=
  ∀ (i p : ℕ) (hi : i < B.length),
    (B[i]'hi).origin = some (p, InsertionKind.hard) →
    (hi1 : i + 1 < B.length) →
    (B[i + 1]'hi1).origin.map Prod.snd = some InsertionKind.easy →
    isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
    i + 1 = B.length - 1 - idx →
    0 < i →
    ∀ (him1 : i - 1 < B.length) (hi2 : i + 2 < B.length),
      (B[i - 1]'him1).value ≥ (B[i + 2]'hi2).value + 3

private lemma no_last_FR_of_threeFlat
    {B : List Labeled} (hflat : IsThreeFlat (forget B))
    (hB : 0 < B.length) :
    isFlatRemovableBool (forget B) (B.length - 1) = true → False := by
  intro hfr
  have hne : forget B ≠ [] := by
    exact List.ne_nil_of_length_pos (by simpa [length_forget] using hB)
  have hlast_lt3 := hflat.2.2 hne
  have hlast_eq :
      (forget B).getLast hne = (B[B.length - 1]'(by omega)).value := by
    rw [List.getLast_eq_getElem]
    simp [forget, List.getElem_map, length_forget]
  rw [hlast_eq] at hlast_lt3
  have hpos : 0 < (B[B.length - 1]'(by omega)).value := by
    have hmem : (B[B.length - 1]'(by omega)).value ∈ forget B := by
      simp [forget, List.mem_map]
      exact ⟨_, List.getElem_mem _, rfl⟩
    exact hflat.1.2 _ hmem
  have hmod : (B[B.length - 1]'(by omega)).value % 3 = 0 := by
    unfold isFlatRemovableBool at hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
    have hval_eq :
        (B[B.length - 1]'(by omega)).value = (forget B)[B.length - 1]! := by
      have hlt : B.length - 1 < (forget B).length := by
        simpa [length_forget] using (by omega : B.length - 1 < B.length)
      rw [getElem!_pos (forget B) (B.length - 1) hlt]
      simp [forget, List.getElem_map]
    rw [hval_eq]
    exact hfr.1.2
  omega

/-- At scan index `0`, the guarded easy seam predicate is vacuous because its
frontier-FR guard is impossible on the last element of a 3-flat list. -/
private lemma S2EasyBoundarySeamGuarded.zero_of_threeFlat
    {B : List Labeled} (hflat : IsThreeFlat (forget B)) :
    S2EasyBoundarySeamGuarded B 0 := by
  intro j hj hj_pos heasy hfr_j hfr_act hj_lt_act hjp1_eq hj1_lt
  exact False.elim
    (no_last_FR_of_threeFlat hflat (by omega) (by simpa using hfr_act))

private lemma S2HardBoundarySeamGuarded.zero_of_threeFlat
    {B : List Labeled} (hflat : IsThreeFlat (forget B)) :
    S2HardBoundarySeamGuarded B 0 := by
  intro i p hi hhard hi1 heasy hfr_act hi1_eq hi_pos him1 hi2
  exact False.elim
    (no_last_FR_of_threeFlat hflat (by omega) (by simpa using hfr_act))

private structure S2ReachInv (B : List Labeled) (idx : ℕ) : Prop where
  flat            : IsThreeFlat (forget B)
  hardSupport     : HardHasSupportingEasy B
  remainingEasyFR : AllRemainingEasyFR B idx
  noEasyChecked   : NoEasyInCheckedSuffix B idx
  noHardZeroBeforeLast : NoHardAtZeroBeforeLast B idx
  coreNotDiv : ∀ (j : ℕ) (hj : j < B.length),
    (B[j]'hj).origin = none → (B[j]'hj).value % 3 ≠ 0
  easyValue : ∀ (j : ℕ) (hj : j < B.length) (p : ℕ),
    (B[j]'hj).origin = some (p, InsertionKind.easy) → (B[j]'hj).value = 3 * p

private lemma origin_map_snd_eq_easy_exists {x : Labeled}
    (h : x.origin.map Prod.snd = some InsertionKind.easy) :
    ∃ p, x.origin = some (p, InsertionKind.easy) := by
  rcases x with ⟨value, origin⟩
  cases origin with
  | none => simp at h
  | some pr =>
      cases pr with
      | mk p k =>
          cases k <;> simp at h
          exact ⟨p, rfl⟩

private lemma Labeled.origin_none_or_easy_or_hard (x : Labeled) :
    x.origin = none ∨
      (∃ p, x.origin = some (p, InsertionKind.easy)) ∨
      (∃ p, x.origin = some (p, InsertionKind.hard)) := by
  rcases x with ⟨value, origin⟩
  cases origin with
  | none =>
      left
      rfl
  | some pr =>
      cases pr with
      | mk p k =>
          cases k with
          | easy =>
              right
              left
              exact ⟨p, rfl⟩
          | hard =>
              right
              right
              exact ⟨p, rfl⟩

private lemma adjacent_eq_of_threeFlat_and_mod3
    {L : List ℕ} {i : ℕ}
    (hflat : IsThreeFlat L)
    (hi1 : i + 1 < L.length)
    (hmod_i : L[i]'(by omega) % 3 = 0)
    (hmod_i1 : L[i + 1]'hi1 % 3 = 0) :
    L[i]'(by omega) = L[i + 1]'hi1 := by
  have hge : L[i]'(by omega) ≥ L[i + 1]'hi1 :=
    List.pairwise_iff_getElem.mp hflat.1.1 i (i + 1) (by omega) hi1 (by omega)
  have hlt : L[i]'(by omega) - L[i + 1]'hi1 < 3 :=
    hflat.2.1 i hi1
  omega

/-- Labeled version of `adjacent_eq_of_threeFlat_and_mod3`. -/
private lemma labeled_adjacent_value_eq_of_threeFlat_and_mod3
    {B : List Labeled} {i : ℕ}
    (hflat : IsThreeFlat (forget B))
    (hi1 : i + 1 < B.length)
    (hmod_i : (B[i]'(by omega)).value % 3 = 0)
    (hmod_i1 : (B[i + 1]'hi1).value % 3 = 0) :
    (B[i]'(by omega)).value = (B[i + 1]'hi1).value := by
  have hmod_i_forget :
      (forget B)[i]'(by rw [length_forget]; omega) % 3 = 0 := by
    simpa [forget, List.getElem_map] using hmod_i
  have hmod_i1_forget :
      (forget B)[i + 1]'(by rw [length_forget]; exact hi1) % 3 = 0 := by
    simpa [forget, List.getElem_map] using hmod_i1
  have h :=
    adjacent_eq_of_threeFlat_and_mod3 (L := forget B) (i := i) hflat
      (by rw [length_forget]; exact hi1) hmod_i_forget hmod_i1_forget
  simpa [forget, List.getElem_map] using h

private lemma isFlatRemovableBool_post_erase_adjacent_of_mod_gap
    (L : List ℕ) (j actualIdx : ℕ)
    (hactual_eq : j + 1 = actualIdx)
    (hact_lt : actualIdx < L.length)
    (hmod_j : L[j]'(by omega) % 3 = 0)
    (h_fr_act : isFlatRemovableBool L actualIdx = true)
    (hgap : ∀ (hj_pos : 0 < j)
        (hj1_lt : j + 1 < (L.eraseIdx actualIdx).length),
      (L.eraseIdx actualIdx)[j - 1]'(by omega) -
        (L.eraseIdx actualIdx)[j + 1]'hj1_lt < 3) :
    isFlatRemovableBool (L.eraseIdx actualIdx) j = true := by
  unfold isFlatRemovableBool at h_fr_act ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h_fr_act ⊢
  obtain ⟨⟨_, _⟩, hflat_erase_act⟩ := h_fr_act
  have hlen_post : (L.eraseIdx actualIdx).length = L.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hj_lt_post : j < (L.eraseIdx actualIdx).length := by
    rw [hlen_post]
    omega
  have hj_lt_L : j < L.length := by omega
  refine ⟨⟨hj_lt_post, ?_⟩, ?_⟩
  · rw [getElem!_pos (L.eraseIdx actualIdx) j hj_lt_post]
    have heq : (L.eraseIdx actualIdx)[j]'hj_lt_post = L[j]'hj_lt_L := by
      rw [List.getElem_eraseIdx]
      simp [show j < actualIdx from by omega]
    rw [heq]
    exact hmod_j
  · apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap
      (L.eraseIdx actualIdx) j hj_lt_post hflat_erase_act
    · intro hj_pos hj1_lt
      exact hgap hj_pos hj1_lt
    · intro hlast_eq hj_pos
      exfalso
      have hflat_post_prop := isThreeFlatBool_implies' _ hflat_erase_act
      have hpost_ne : L.eraseIdx actualIdx ≠ [] :=
        List.ne_nil_of_length_pos (by rw [hlen_post]; omega)
      have hlast_lt := hflat_post_prop.2.2 hpost_ne
      have hlast_get :
          (L.eraseIdx actualIdx).getLast hpost_ne =
            (L.eraseIdx actualIdx)[j]'hj_lt_post := by
        rw [List.getLast_eq_getElem]
        congr 1
        omega
      have hmem_j_post :
          (L.eraseIdx actualIdx)[j]'hj_lt_post ∈ L.eraseIdx actualIdx :=
        List.getElem_mem hj_lt_post
      have hpos_j_post : 0 < (L.eraseIdx actualIdx)[j]'hj_lt_post :=
        hflat_post_prop.1.2 _ hmem_j_post
      have hmod_post : (L.eraseIdx actualIdx)[j]'hj_lt_post % 3 = 0 := by
        have heq : (L.eraseIdx actualIdx)[j]'hj_lt_post = L[j]'hj_lt_L := by
          rw [List.getElem_eraseIdx]
          simp [show j < actualIdx from by omega]
        rw [heq]
        exact hmod_j
      rw [hlast_get] at hlast_lt
      omega

private lemma s2reach_hardSupport_boundary_lower_bound_of_guarded_seam
    {B : List Labeled} {idx i p : ℕ}
    (hseamG : S2HardBoundarySeamGuarded B idx)
    (hi_lt : i < B.length)
    (h_hard_i : (B[i]'hi_lt).origin = some (p, InsertionKind.hard))
    (hi1_lt : i + 1 < B.length)
    (h_easy_i1 : (B[i + 1]'hi1_lt).origin.map Prod.snd = some InsertionKind.easy)
    (hfr_act : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hi1_eq : i + 1 = B.length - 1 - idx)
    (hi_pos : 0 < i)
    (him1 : i - 1 < B.length) (hi2 : i + 2 < B.length) :
    (B[i - 1]'him1).value ≥ (B[i + 2]'hi2).value + 3 :=
  hseamG i p hi_lt h_hard_i hi1_lt h_easy_i1 hfr_act hi1_eq hi_pos him1 hi2

private lemma s2_easy_boundary_gap_of_post_FR
    {B : List Labeled} {idx j : ℕ}
    (hj_pos : 0 < j)
    (hact_lt : B.length - 1 - idx < B.length)
    (hjp1_eq : j + 1 = B.length - 1 - idx)
    (hfr_post :
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) j = true)
    (hj1_lt : j + 1 < ((forget B).eraseIdx (B.length - 1 - idx)).length) :
    ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) -
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt < 3 := by
  have h_fe :
      forget (B.eraseIdx (B.length - 1 - idx)) =
        (forget B).eraseIdx (B.length - 1 - idx) := by
    simp [forget, List.eraseIdx_map]
  unfold isFlatRemovableBool at hfr_post
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_post
  have hflat_de := isThreeFlatBool_implies' _ hfr_post.2
  have hlen_post_forget :
      ((forget B).eraseIdx (B.length - 1 - idx)).length = B.length - 1 := by
    rw [List.length_eraseIdx_of_lt]
    · simp [length_forget]
    · rw [length_forget]
      exact hact_lt
  have hj_lt_post : j < ((forget B).eraseIdx (B.length - 1 - idx)).length := by
    rw [hlen_post_forget]
    omega
  have hlen_de :
      (((forget B).eraseIdx (B.length - 1 - idx)).eraseIdx j).length =
        B.length - 2 := by
    rw [List.length_eraseIdx_of_lt hj_lt_post, hlen_post_forget]
    omega
  have hgap_bound :
      (j - 1) + 1 <
        (((forget B).eraseIdx (B.length - 1 - idx)).eraseIdx j).length := by
    rw [hlen_de]
    omega
  have hflat_de_norm :
      IsThreeFlat (((forget B).eraseIdx (B.length - 1 - idx)).eraseIdx j) := by
    simpa only [h_fe] using hflat_de
  have hgap := hflat_de_norm.2.1 (j - 1) hgap_bound
  have hjm1_bound :
      j - 1 <
        (((forget B).eraseIdx (B.length - 1 - idx)).eraseIdx j).length := by
    rw [hlen_de]
    omega
  have hleft :
      (((forget B).eraseIdx (B.length - 1 - idx)).eraseIdx j)[j - 1]'hjm1_bound =
        ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) := by
    rw [List.getElem_eraseIdx]
    simp [show j - 1 < j from by omega]
  have hright :
      (((forget B).eraseIdx (B.length - 1 - idx)).eraseIdx j)[(j - 1) + 1]'
          (by rw [hlen_de]; omega) =
        ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt := by
    rw [List.getElem_eraseIdx]
    simp [show ¬((j - 1) + 1 < j) from by omega]
    congr 1
    omega
  rw [← hleft, ← hright]
  exact hgap

/-- The live easy-boundary seam follows from the delete-bridge invariant.

If deleting the current frontier preserves flat-removability of the adjacent
upper easy, the post-delete FR check supplies exactly the `< 3` gap consumed by
the local adjacent-delete adapter. -/
private lemma S2EasyBoundarySeamGuarded.of_delete_bridge
    {B : List Labeled} {idx : ℕ}
    (hbridge : EasyFRPreservedUnderFrontierDelete B idx) :
    S2EasyBoundarySeamGuarded B idx := by
  intro j hj hj_pos heasy _hfr_j _hfr_act hj_lt_act hjp1_eq hj1_lt
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hlen_post : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hj_post : j < (B.eraseIdx (B.length - 1 - idx)).length := by
    rw [hlen_post]
    omega
  have hj_unchecked : j < (B.eraseIdx (B.length - 1 - idx)).length - idx := by
    rw [hlen_post]
    omega
  have heasy_post :
      ((B.eraseIdx (B.length - 1 - idx))[j]'hj_post).origin.map Prod.snd =
        some InsertionKind.easy := by
    have heq :
        (B.eraseIdx (B.length - 1 - idx))[j]'hj_post = B[j]'hj := by
      rw [List.getElem_eraseIdx]
      simp [hj_lt_act]
    rw [heq]
    exact heasy
  have hfr_post :
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) j = true :=
    hbridge j hj_post hj_unchecked heasy_post
  exact
    s2_easy_boundary_gap_of_post_FR hj_pos hact_lt hjp1_eq hfr_post hj1_lt

/-- Post-delete hard FR contradicts a supplied hard/easy boundary lower seam.

This packages the local double-erasure arithmetic in the interior hard boundary
case.  The construction-history work is now isolated to providing
`B[i-1].value >= B[i+2].value + 3`; post-delete flat-removability supplies the
opposite `< 3` seam. -/
private lemma s2_hard_boundary_post_FR_contradicts_lower_bound
    {B : List Labeled} {idx i : ℕ}
    (_hi_lt : i < B.length)
    (hi_pos : 0 < i)
    (hi2 : i + 2 < B.length)
    (hi1_eq : i + 1 = B.length - 1 - idx)
    (hfr_post :
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) i = true)
    (hge : (B[i - 1]'(by omega)).value ≥ (B[i + 2]'hi2).value + 3) :
    False := by
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hlen_post : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hlt :
        (B[i - 1]'(by omega)).value - (B[i + 2]'hi2).value < 3 := by
    unfold isFlatRemovableBool at hfr_post
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_post
    have hflat_de := isThreeFlatBool_implies' _ hfr_post.2
    have hi_lt_forget_post :
        i < (forget (B.eraseIdx (B.length - 1 - idx))).length := by
      rw [length_forget, hlen_post]
      omega
    have hlen_de :
        ((forget (B.eraseIdx (B.length - 1 - idx))).eraseIdx i).length =
          B.length - 2 := by
      rw [List.length_eraseIdx_of_lt hi_lt_forget_post, length_forget, hlen_post]
      omega
    have hgap_bound :
        (i - 1) + 1 <
          ((forget (B.eraseIdx (B.length - 1 - idx))).eraseIdx i).length := by
      rw [hlen_de]
      omega
    have hgap := hflat_de.2.1 (i - 1) hgap_bound
    have hleft :
        ((forget (B.eraseIdx (B.length - 1 - idx))).eraseIdx i)[i - 1]'
            (by rw [hlen_de]; omega) =
          (B[i - 1]'(by omega)).value := by
      rw [List.getElem_eraseIdx]
      simp [show i - 1 < i from by omega]
      change ((B.eraseIdx (B.length - 1 - idx))[i - 1]'(by
        rw [hlen_post]; omega)).value = (B[i - 1]'(by omega)).value
      congr 1
      rw [List.getElem_eraseIdx]
      simp [show i - 1 < B.length - 1 - idx from by omega]
    have hright :
        ((forget (B.eraseIdx (B.length - 1 - idx))).eraseIdx i)[(i - 1) + 1]'
            hgap_bound =
          (B[i + 2]'hi2).value := by
      rw [List.getElem_eraseIdx]
      simp [show ¬((i - 1) + 1 < i) from by omega]
      change ((B.eraseIdx (B.length - 1 - idx))[(i - 1) + 1 + 1]'(by
        rw [hlen_post]; omega)).value = (B[i + 2]'hi2).value
      congr 1
      rw [List.getElem_eraseIdx]
      simp [show ¬((i - 1) + 1 + 1 < B.length - 1 - idx) from by omega]
      congr 1 <;> omega
    rw [← hleft, ← hright]
    exact hgap
  omega

/-- Full hard-boundary contradiction assuming the guarded hard/easy seam field.

This is the checked adapter that `S2ReachInv.hardBoundarySeam` should feed
once the seam field is threaded into the invariant: the zero case comes from
`NoHardAtZeroBeforeLast`, the interior case from the guarded seam lower bound,
and the right-edge case from post-delete 3-flatness. -/
private lemma hardSupport_boundary_contradicts_FR_of_guarded_seam
    {B : List Labeled} {idx i p : ℕ}
    (hnoZero : NoHardAtZeroBeforeLast B idx)
    (hseamG : S2HardBoundarySeamGuarded B idx)
    (hi_lt : i < B.length)
    (h_hard_i : (B[i]'hi_lt).origin = some (p, InsertionKind.hard))
    (hi1_lt : i + 1 < B.length)
    (h_easy_i1 : (B[i + 1]'hi1_lt).origin.map Prod.snd = some InsertionKind.easy)
    (hfr_act : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hi1_eq : i + 1 = B.length - 1 - idx)
    (hfr_post : isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) i = true) :
    False := by
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hlen_post : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hflat_post : IsThreeFlat (forget (B.eraseIdx (B.length - 1 - idx))) := by
    have h_fe :
        forget (B.eraseIdx (B.length - 1 - idx)) =
          (forget B).eraseIdx (B.length - 1 - idx) := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    unfold isFlatRemovableBool at hfr_act
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_act
    exact isThreeFlatBool_implies' _ hfr_act.2
  by_cases hi_zero : i = 0
  · subst hi_zero
    have hnot_hard :=
      hnoZero (by omega : idx + 1 < B.length) (by omega : 0 < B.length)
    rw [h_hard_i] at hnot_hard
    simp at hnot_hard
  · have hi_pos : 0 < i := by omega
    by_cases hi2 : i + 2 < B.length
    · have hge :
          (B[i - 1]'(by omega)).value ≥ (B[i + 2]'hi2).value + 3 :=
        s2reach_hardSupport_boundary_lower_bound_of_guarded_seam hseamG
          hi_lt h_hard_i hi1_lt h_easy_i1 hfr_act hi1_eq hi_pos
          (by omega) hi2
      exact
        s2_hard_boundary_post_FR_contradicts_lower_bound
          hi_lt hi_pos hi2 hi1_eq hfr_post hge
    · have hpost_ne : forget (B.eraseIdx (B.length - 1 - idx)) ≠ [] := by
        have hlen_forget :
            (forget (B.eraseIdx (B.length - 1 - idx))).length = i + 1 := by
          rw [length_forget, hlen_post]
          omega
        exact List.ne_nil_of_length_pos (by rw [hlen_forget]; omega)
      have hlast_lt := hflat_post.2.2 hpost_ne
      have hi_lt_post : i < (B.eraseIdx (B.length - 1 - idx)).length := by
        rw [hlen_post]
        omega
      have hi_lt_forget_post :
          i < (forget (B.eraseIdx (B.length - 1 - idx))).length := by
        rw [length_forget]
        exact hi_lt_post
      have hlast_eq :
          (forget (B.eraseIdx (B.length - 1 - idx))).getLast hpost_ne =
            (forget (B.eraseIdx (B.length - 1 - idx)))[i]'hi_lt_forget_post := by
        rw [List.getLast_eq_getElem]
        congr 1
        rw [length_forget, hlen_post]
        omega
      have hpos_last :
          0 < (forget (B.eraseIdx (B.length - 1 - idx)))[i]'hi_lt_forget_post := by
        exact hflat_post.1.2 _
          (List.getElem_mem hi_lt_forget_post)
      have hmod_last :
          (forget (B.eraseIdx (B.length - 1 - idx)))[i]'hi_lt_forget_post % 3 = 0 := by
        unfold isFlatRemovableBool at hfr_post
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_post
        rw [getElem!_pos _ i hi_lt_forget_post] at hfr_post
        exact hfr_post.1.2
      rw [hlast_eq] at hlast_lt
      omega

private def S2BoundaryLiveSeams (B : List Labeled) (idx : ℕ) : Prop :=
  S2EasyBoundarySeamGuarded B idx ∧
  S2HardBoundarySeamGuarded B idx

private lemma S2BoundaryLiveSeams.zero_of_threeFlat
    {B : List Labeled} (hflat : IsThreeFlat (forget B)) :
    S2BoundaryLiveSeams B 0 :=
  ⟨S2EasyBoundarySeamGuarded.zero_of_threeFlat hflat,
    S2HardBoundarySeamGuarded.zero_of_threeFlat hflat⟩

private lemma processInsertionsLabeled_flat
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init)) :
    IsThreeFlat (forget (processInsertionsLabeled ν A_init)) := by
  rw [forget_processInsertionsLabeled]
  suffices h : ∀ (parts : List ℕ) (B₀ : List ℕ), IsThreeFlat B₀ →
      IsThreeFlat (processInsertions parts B₀) from h ν _ hA_flat
  intro parts
  induction parts with
  | nil => intro B₀ hB; exact hB
  | cons p rest ih =>
      intro B₀ hB
      simp only [processInsertions]
      exact ih _ (performInsertion_preserves_flat' B₀ p hB)

private def S2ReachEasyBoundaryLiveHistory
    (A_init : List Labeled) (ν : List ℕ) : Prop :=
  ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
    S2Reach (processInsertionsLabeled ν A_init) B idx rec →
      S2EasyBoundarySeamGuarded B idx

/-- Reachable-state hard/easy live-boundary history.

This is the corrected hard-side target for the nonempty insertion branch.  It
records only the numeric lower seam at the actual S2 frontier, avoiding the
unreachable future-index failures of a global hard/easy suffix seam. -/
private def S2ReachHardBoundaryLiveHistory
    (A_init : List Labeled) (ν : List ℕ) : Prop :=
  ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
    S2Reach (processInsertionsLabeled ν A_init) B idx rec →
      S2HardBoundarySeamGuarded B idx

/-- Reachable-state guarded easy delete bridge.

This is the non-circular shape actually needed for the easy live seam: only
when the current frontier is flat-removable do we need deletion of that
frontier to preserve flat-removability of unchecked easy entries. -/
private def S2ReachGuardedEasyDeleteBridgeHistory
    (A_init : List Labeled) (ν : List ℕ) : Prop :=
  ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
    S2Reach (processInsertionsLabeled ν A_init) B idx rec →
    idx < B.length →
    isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
      EasyFRPreservedUnderFrontierDelete B idx

private lemma S2ReachEasyBoundaryLiveHistory.of_guarded_delete_bridge
    {A_init : List Labeled} {ν : List ℕ}
    (hbridge : S2ReachGuardedEasyDeleteBridgeHistory A_init ν) :
    S2ReachEasyBoundaryLiveHistory A_init ν := by
  intro B idx rec hreach
  intro j hj hj_pos heasy hfr_j hfr_act hj_lt_act hjp1_eq hj1_lt
  have hidx : idx < B.length := by omega
  have hbridge_here : EasyFRPreservedUnderFrontierDelete B idx :=
    hbridge hreach hidx hfr_act
  exact
    S2EasyBoundarySeamGuarded.of_delete_bridge hbridge_here
      j hj hj_pos heasy hfr_j hfr_act hj_lt_act hjp1_eq hj1_lt

private lemma S2HardBoundarySeamGuarded.of_post_noHard
    {B : List Labeled} {idx : ℕ}
    (hhard_mod : ∀ (i p : ℕ) (hi : i < B.length),
      (B[i]'hi).origin = some (p, InsertionKind.hard) →
        (B[i]'hi).value % 3 = 0)
    (hpost_noHard :
      isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
      ∀ (hidx_post : idx < (B.eraseIdx (B.length - 1 - idx)).length)
        (_hfr_post : isFlatRemovableBool
          (forget (B.eraseIdx (B.length - 1 - idx)))
          ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true)
        (p : ℕ),
        ((B.eraseIdx (B.length - 1 - idx))[
          (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
            some (p, InsertionKind.hard) → False) :
    S2HardBoundarySeamGuarded B idx := by
  intro i p hi hhard hi1 heasy hfr_act hi1_eq hi_pos him1 hi2
  by_contra hnot
  push_neg at hnot
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hlen_post : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hfront_post_eq :
      (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx = i := by
    rw [hlen_post]
    omega
  have hi_post : i < (B.eraseIdx (B.length - 1 - idx)).length := by
    rw [hlen_post]
    omega
  have hi_forget_post :
      i < (forget (B.eraseIdx (B.length - 1 - idx))).length := by
    rw [length_forget]
    exact hi_post
  have hpost_i_origin :
      ((B.eraseIdx (B.length - 1 - idx))[i]'hi_post).origin =
        some (p, InsertionKind.hard) := by
    have heq :
        (B.eraseIdx (B.length - 1 - idx))[i]'hi_post = B[i]'hi := by
      rw [List.getElem_eraseIdx]
      simp [show i < B.length - 1 - idx from by omega]
    rw [heq]
    exact hhard
  have hpost_i_mod :
      (forget (B.eraseIdx (B.length - 1 - idx)))[i]! % 3 = 0 := by
    rw [getElem!_pos _ i hi_forget_post]
    have hval :
        (forget (B.eraseIdx (B.length - 1 - idx)))[i]'hi_forget_post =
          ((B.eraseIdx (B.length - 1 - idx))[i]'hi_post).value := by
      simp [forget, List.getElem_map]
    rw [hval]
    have hpost_val :
        ((B.eraseIdx (B.length - 1 - idx))[i]'hi_post).value =
          (B[i]'hi).value := by
      have heq :
          (B.eraseIdx (B.length - 1 - idx))[i]'hi_post = B[i]'hi := by
        rw [List.getElem_eraseIdx]
        simp [show i < B.length - 1 - idx from by omega]
      rw [heq]
    rw [hpost_val]
    exact hhard_mod i p hi hhard
  have hflat_post_bool :
      isThreeFlatBool (forget (B.eraseIdx (B.length - 1 - idx))) = true := by
    have h_fe :
        forget (B.eraseIdx (B.length - 1 - idx)) =
          (forget B).eraseIdx (B.length - 1 - idx) := by
      simp [forget, List.eraseIdx_map]
    unfold isFlatRemovableBool at hfr_act
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_act
    rw [h_fe]
    exact hfr_act.2
  have hflat_after_hard :
      isThreeFlatBool
        ((forget (B.eraseIdx (B.length - 1 - idx))).eraseIdx i) = true := by
    apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap
      (forget (B.eraseIdx (B.length - 1 - idx))) i hi_forget_post hflat_post_bool
    · intro _hi_pos hi1_post
      have hleft :
          ((B.eraseIdx (B.length - 1 - idx))[i - 1]'(by
              rw [hlen_post]
              omega)).value =
            (B[i - 1]'him1).value := by
        congr 1
        rw [List.getElem_eraseIdx]
        simp [show i - 1 < B.length - 1 - idx from by omega]
      have hright :
          ((B.eraseIdx (B.length - 1 - idx))[i + 1]'(by
              rw [hlen_post]
              omega)).value =
            (B[i + 2]'hi2).value := by
        congr 1
        rw [List.getElem_eraseIdx]
        simp [show ¬ i + 1 < B.length - 1 - idx from by omega]
      have hgap_nat :
          (B[i - 1]'him1).value - (B[i + 2]'hi2).value < 3 := by
        omega
      simpa [forget, List.getElem_map, hleft, hright] using hgap_nat
    · intro hlast_eq _hi_pos
      rw [length_forget, hlen_post] at hlast_eq
      omega
  have hfr_post_at_i :
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) i = true := by
    unfold isFlatRemovableBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨hi_forget_post, hpost_i_mod⟩, hflat_after_hard⟩
  have hidx_post : idx < (B.eraseIdx (B.length - 1 - idx)).length := by
    rw [hlen_post]
    omega
  have hfr_front :
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx)))
        ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true := by
    rwa [hfront_post_eq]
  exact
    hpost_noHard hfr_act hidx_post hfr_front p
      (by
        simpa [hfront_post_eq] using hpost_i_origin)

/-- Reachable hard live seam from a post-delete hard-frontier exclusion.

This is the reachable-state wrapper around
`S2HardBoundarySeamGuarded.of_post_noHard`; hard-label divisibility is supplied
by the construction output and preserved by S2 erasures. -/
private lemma S2ReachHardBoundaryLiveHistory.of_post_noHard
    {A_init : List Labeled} {ν : List ℕ}
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hpost_noHard : ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
      S2Reach (processInsertionsLabeled ν A_init) B idx rec →
      isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
      ∀ (hidx_post : idx < (B.eraseIdx (B.length - 1 - idx)).length)
        (hfr_post : isFlatRemovableBool
          (forget (B.eraseIdx (B.length - 1 - idx)))
          ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true)
        (p : ℕ),
        ((B.eraseIdx (B.length - 1 - idx))[
          (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
            some (p, InsertionKind.hard) → False) :
    S2ReachHardBoundaryLiveHistory A_init ν := by
  intro B idx rec hreach
  exact
    S2HardBoundarySeamGuarded.of_post_noHard
      (by
        intro i p hi hhard
        exact S2Reach_hard_value_mod3 A_init ν hA_clean hreach i hi p hhard)
      (by
        intro hfr_act hidx_post hfr_post p hhard
        exact hpost_noHard hreach hfr_act hidx_post hfr_post p hhard)

/-- Post-erase `AllRemainingEasyFR` is exactly the guarded easy-delete bridge
needed at the pre-erase state. -/
private lemma EasyFRPreservedUnderFrontierDelete.of_post_remaining
    {B : List Labeled} {idx : ℕ}
    (hremaining :
      AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx) :
    EasyFRPreservedUnderFrontierDelete B idx := by
  intro j hj hjlt hkind
  exact hremaining j hj hjlt hkind

private def S2ReachPostEraseLiveProvider
    (A_init : List Labeled) (ν : List ℕ) : Prop :=
  ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
    S2Reach (processInsertionsLabeled ν A_init) B idx rec →
    idx < B.length →
    isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
      AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
      ∀ (hidx_post : idx < (B.eraseIdx (B.length - 1 - idx)).length)
        (hfr_post : isFlatRemovableBool
          (forget (B.eraseIdx (B.length - 1 - idx)))
          ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true)
        (p : ℕ),
        ((B.eraseIdx (B.length - 1 - idx))[
          (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
            some (p, InsertionKind.hard) → False

private structure S2ReachPostEraseProviderComponents
    (A_init : List Labeled) (ν : List ℕ) : Prop where
  bridge : ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
    S2Reach (processInsertionsLabeled ν A_init) B idx rec →
    idx < B.length →
    isFlatRemovableBool (forget B) (B.length - 1 - idx) = true →
      EasyFRPreservedUnderFrontierDelete B idx
  frontier : ∀ {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ},
    idx < B.length →
    actualIdx = B.length - 1 - idx →
    isFlatRemovableBool (forget B) actualIdx = true →
    S2Reach (processInsertionsLabeled ν A_init) B idx rec →
      FrontierFRImpliesEasy (B.eraseIdx actualIdx) idx

private lemma S2ReachPostEraseProviderComponents.to_live_provider
    {A_init : List Labeled} {ν : List ℕ}
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν) :
    S2ReachPostEraseLiveProvider A_init ν := by
  intro B idx rec hreach hidx hfr
  constructor
  · exact hcomponents.bridge hreach hidx hfr
  · intro hidx_post hfr_post p hhard
    have hfrontier :
        FrontierFRImpliesEasy
          (B.eraseIdx (B.length - 1 - idx)) idx :=
      hcomponents.frontier hidx rfl hfr hreach
    have heasy := hfrontier hidx_post hfr_post
    rw [hhard] at heasy
    simp at heasy

private lemma S2ReachPostEraseLiveProvider.to_live_histories
    {A_init : List Labeled} {ν : List ℕ}
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hpost : S2ReachPostEraseLiveProvider A_init ν) :
    S2ReachGuardedEasyDeleteBridgeHistory A_init ν ∧
      S2ReachHardBoundaryLiveHistory A_init ν := by
  constructor
  · intro B idx rec hreach hidx hfr
    exact
      EasyFRPreservedUnderFrontierDelete.of_post_remaining
        (hpost hreach hidx hfr).1
  · apply S2ReachHardBoundaryLiveHistory.of_post_noHard hA_clean
    intro B idx rec hreach hfront_old_fr hidx_post hfr_post p hhard
    have hidx : idx < B.length := by
      unfold isFlatRemovableBool at hfront_old_fr
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfront_old_fr
      have hact_lt_forget : B.length - 1 - idx < (forget B).length :=
        hfront_old_fr.1.1
      rw [length_forget] at hact_lt_forget
      have hlen_post :
          (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
        List.length_eraseIdx_of_lt hact_lt_forget
      rw [hlen_post] at hidx_post
      omega
    exact
      (hpost hreach hidx hfront_old_fr).2 hidx_post hfr_post p hhard

/-- Bundle the two corrected live-history components into the central S2
boundary payload. -/
private lemma S2BoundaryLiveSeams.of_reachable_live_history
    {A_init B : List Labeled} {ν : List ℕ} {idx : ℕ} {rec : List ℕ}
    (heasy : S2ReachEasyBoundaryLiveHistory A_init ν)
    (hhard : S2ReachHardBoundaryLiveHistory A_init ν)
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2BoundaryLiveSeams B idx :=
  ⟨heasy hreach, hhard hreach⟩

/-- Provider components are the exact non-circular payload needed for the
corrected live-boundary theorem.

This wrapper keeps the final theorem honest: all generic plumbing from the
post-erase component package to the two reachable live histories is checked
here, so the remaining proof obligation is only construction of
`S2ReachPostEraseProviderComponents`. -/
private lemma s2reach_boundary_live_seams_of_provider_components
    (A_init : List Labeled) (ν : List ℕ)
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2BoundaryLiveSeams B idx := by
  have hpost : S2ReachPostEraseLiveProvider A_init ν :=
    hcomponents.to_live_provider
  have hproviders :
      S2ReachGuardedEasyDeleteBridgeHistory A_init ν ∧
      S2ReachHardBoundaryLiveHistory A_init ν :=
    S2ReachPostEraseLiveProvider.to_live_histories hA_clean hpost
  have hhistories :
      S2ReachEasyBoundaryLiveHistory A_init ν ∧
      S2ReachHardBoundaryLiveHistory A_init ν :=
    ⟨S2ReachEasyBoundaryLiveHistory.of_guarded_delete_bridge hproviders.1,
      hproviders.2⟩
  exact
    S2BoundaryLiveSeams.of_reachable_live_history
      hhistories.1 hhistories.2 hreach

/-- Method form of `s2reach_boundary_live_seams_of_provider_components`.

This is the exact non-circular handoff we want the final S2 proof to use:
once the path-sensitive post-erase component provider is available, live
boundary seams are available at every reachable S2 state. -/
private lemma S2ReachPostEraseProviderComponents.boundary_live
    {A_init : List Labeled} {ν : List ℕ}
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν)
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2BoundaryLiveSeams B idx :=
  s2reach_boundary_live_seams_of_provider_components
    A_init ν hA_clean hcomponents hreach

/-- Method form exposing the two post-erase component fields at the current
reachable state. -/
private lemma S2ReachPostEraseProviderComponents.current_components
    {A_init : List Labeled} {ν : List ℕ}
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (hidx : idx < B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true) :
    AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
    FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx :=
  ⟨hcomponents.bridge hreach hidx hfr,
    hcomponents.frontier hidx rfl hfr hreach⟩

/-- Provider-form handoff for the erase successor.

This is the exact replacement for the bad erase branch in
`S2Reach_S2ReachInv_and_live`: once the path-sensitive post-erase provider is
available, the erased state's live seams come from reachability of the erased
state itself, not from reusing the pre-erase live seam. -/
private lemma S2ReachPostEraseProviderComponents.live_after_erase
    {A_init : List Labeled} {ν : List ℕ}
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν)
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ}
    (hidx : idx < B.length)
    (hactual : actualIdx = B.length - 1 - idx)
    (hfr : isFlatRemovableBool (forget B) actualIdx = true)
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2BoundaryLiveSeams (B.eraseIdx actualIdx) idx := by
  exact
    hcomponents.boundary_live hA_clean
      (S2Reach.erase (start := processInsertionsLabeled ν A_init)
        (B := B) (idx := idx) (actualIdx := actualIdx) (rec := rec)
        hidx hactual hfr hreach)

/-- Provider-form handoff for the skip successor.

This packages the second failing branch: after a skip, the live seam at
`idx + 1` is a property of the newly reachable skipped state, not a consequence
of the old frontier being non-flat-removable. -/
private lemma S2ReachPostEraseProviderComponents.live_after_skip
    {A_init : List Labeled} {ν : List ℕ}
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν)
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ}
    (hidx : idx < B.length)
    (hactual : actualIdx = B.length - 1 - idx)
    (hnfr : isFlatRemovableBool (forget B) actualIdx = false)
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2BoundaryLiveSeams B (idx + 1) := by
  exact
    hcomponents.boundary_live hA_clean
      (S2Reach.skip (start := processInsertionsLabeled ν A_init)
        (B := B) (idx := idx) (actualIdx := actualIdx) (rec := rec)
        hidx hactual hnfr hreach)

/-- Provider-form erase step for the bundled `S2ReachInv`.

This extracts the large erase branch from the central reachability induction,
but replaces the circular call to `s2reach_boundary_live_seams` with the
path-sensitive post-erase component provider. -/
private lemma S2ReachInv.erase_of_provider_components
    {A_init : List Labeled} {ν : List ℕ}
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν)
    {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ}
    (hidx : idx < B.length)
    (hactual : actualIdx = B.length - 1 - idx)
    (hfr : isFlatRemovableBool (forget B) actualIdx = true)
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (hInv : S2ReachInv B idx) :
    S2ReachInv (B.eraseIdx actualIdx) idx := by
  have hflat_post : IsThreeFlat (forget (B.eraseIdx actualIdx)) := by
    have h_fe : forget (B.eraseIdx actualIdx) = (forget B).eraseIdx actualIdx := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    unfold isFlatRemovableBool at hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
    exact isThreeFlatBool_implies' _ hfr.2
  have hfr_norm :
      isFlatRemovableBool (forget B) (B.length - 1 - idx) = true := by
    simpa [hactual] using hfr
  have hpost_components :
      AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
      FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx :=
    hcomponents.current_components hreach hidx hfr_norm
  refine
    { flat := hflat_post
      hardSupport := ?_
      remainingEasyFR := ?_
      noEasyChecked := ?_
      noHardZeroBeforeLast := ?_
      coreNotDiv := ?_
      easyValue := ?_ }
  · intro i hi p hhard hfr_post
    have hact_lt : actualIdx < B.length := by omega
    have hlen_post : (B.eraseIdx actualIdx).length = B.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    have h_fe : forget (B.eraseIdx actualIdx) = (forget B).eraseIdx actualIdx := by
      simp [forget, List.eraseIdx_map]
    have hfr_forget : isFlatRemovableBool ((forget B).eraseIdx actualIdx) i = true := by
      rw [← h_fe]; exact hfr_post
    have hact_fr_forget : isFlatRemovableBool (forget B) actualIdx = true := hfr
    have hact_lt_forget : actualIdx < (forget B).length := by
      rw [length_forget]; exact hact_lt
    by_cases hilt : i < actualIdx
    · have hi_lt_B : i < B.length := by omega
      have horg_i : (B[i]'hi_lt_B).origin = some (p, .hard) := by
        have heq : (B.eraseIdx actualIdx)[i]'hi = B[i]'hi_lt_B := by
          rw [List.getElem_eraseIdx]; simp [hilt]
        rw [heq] at hhard; exact hhard
      have hfr_B : isFlatRemovableBool (forget B) i = true :=
        isFlatRemovableBool_transfer_left (forget B) i actualIdx hilt
          hact_lt_forget hInv.flat hact_fr_forget hfr_forget
      have ⟨hi1_B, heasy_B⟩ := hInv.hardSupport i hi_lt_B p horg_i hfr_B
      by_cases hi1_lt_k : i + 1 < actualIdx
      · have hi1_lt_post : i + 1 < (B.eraseIdx actualIdx).length := by
          rw [hlen_post]; omega
        refine ⟨hi1_lt_post, ?_⟩
        have heq : (B.eraseIdx actualIdx)[i+1]'hi1_lt_post = B[i+1]'hi1_B := by
          rw [List.getElem_eraseIdx]; simp [hi1_lt_k]
        rw [heq]; exact heasy_B
      · push_neg at hi1_lt_k
        have hi1_eq_norm : i + 1 = B.length - 1 - idx := by omega
        have hfr_post_norm :
            isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) i = true := by
          simpa [hactual] using hfr_post
        have hact_norm_lt : B.length - 1 - idx < B.length := by omega
        have hlen_norm_post :
            (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
          List.length_eraseIdx_of_lt hact_norm_lt
        have hi_post_norm : i < (B.eraseIdx (B.length - 1 - idx)).length := by
          rw [hlen_norm_post]
          omega
        have hfront_eq_norm :
            (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx = i := by
          rw [hlen_norm_post]
          omega
        have hhard_post_norm :
            ((B.eraseIdx (B.length - 1 - idx))[i]'hi_post_norm).origin =
              some (p, InsertionKind.hard) := by
          have heq :
              (B.eraseIdx (B.length - 1 - idx))[i]'hi_post_norm = B[i]'hi_lt_B := by
            rw [List.getElem_eraseIdx]
            simp [show i < B.length - 1 - idx from by omega]
          rw [heq]
          exact horg_i
        have hidx_post_norm : idx < (B.eraseIdx (B.length - 1 - idx)).length := by
          rw [hlen_norm_post]
          omega
        have hhard_front_norm :
            ((B.eraseIdx (B.length - 1 - idx))[
              (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
              some (p, InsertionKind.hard) := by
          simpa [hfront_eq_norm] using hhard_post_norm
        have heasy_front_norm := hpost_components.2
          hidx_post_norm
          (by simpa [hfront_eq_norm] using hfr_post_norm)
        rw [hhard_front_norm] at heasy_front_norm
        simp at heasy_front_norm
    · push_neg at hilt
      have hi1_lt_B : i + 1 < B.length := by
        have hlen_post : (B.eraseIdx actualIdx).length = B.length - 1 :=
          List.length_eraseIdx_of_lt hact_lt
        rw [hlen_post] at hi
        omega
      have horg_i1 : (B[i+1]'hi1_lt_B).origin = some (p, .hard) := by
        have heq : (B.eraseIdx actualIdx)[i]'hi = B[i+1]'hi1_lt_B := by
          rw [List.getElem_eraseIdx]
          simp [show ¬(i < actualIdx) from by omega]
        rw [heq] at hhard; exact hhard
      have hfr_B_i1 : isFlatRemovableBool (forget B) (i + 1) = true :=
        isFlatRemovableBool_transfer_right (forget B) i actualIdx
          (by omega : ¬(i < actualIdx))
          (by rw [length_forget]; omega)
          hact_lt_forget hInv.flat hact_fr_forget hfr_forget
      have ⟨hi2_B, heasy_B⟩ :=
        hInv.hardSupport (i+1) hi1_lt_B p horg_i1 hfr_B_i1
      have hi1_lt_post : i + 1 < (B.eraseIdx actualIdx).length := by
        rw [hlen_post]; omega
      refine ⟨hi1_lt_post, ?_⟩
      have heq : (B.eraseIdx actualIdx)[i+1]'hi1_lt_post = B[i+2]'hi2_B := by
        rw [List.getElem_eraseIdx]
        simp [show ¬(i + 1 < actualIdx) from by omega]
      rw [heq]; exact heasy_B
  · simpa [hactual] using hpost_components.1
  · rw [hactual]
    exact noEasyInCheckedSuffix_delete hInv.noEasyChecked (by omega)
  · intro hidx_pre h0_post
    have hact_lt : actualIdx < B.length := by omega
    have hlen_post : (B.eraseIdx actualIdx).length = B.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    have hact_ge_two : 2 ≤ actualIdx := by
      rw [hactual]
      rw [hlen_post] at hidx_pre
      omega
    have h0_B : 0 < B.length := by omega
    have h0_eq :
        (B.eraseIdx actualIdx)[0]'h0_post = B[0]'h0_B := by
      rw [List.getElem_eraseIdx]
      simp [show (0 : ℕ) < actualIdx from by omega]
    rw [h0_eq]
    exact hInv.noHardZeroBeforeLast (by rw [hactual] at hact_ge_two; omega) h0_B
  · intro j hj hcore
    have hact_lt : actualIdx < B.length := by omega
    have hlen_post : (B.eraseIdx actualIdx).length = B.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    rw [List.getElem_eraseIdx] at hcore ⊢
    by_cases hjlt : j < actualIdx
    · simp only [hjlt, ↓reduceDIte] at hcore ⊢
      exact hInv.coreNotDiv j (by omega) hcore
    · simp only [hjlt, ↓reduceDIte] at hcore ⊢
      exact hInv.coreNotDiv (j + 1) (by rw [hlen_post] at hj; omega) hcore
  · intro j hj p heasy
    have hact_lt : actualIdx < B.length := by omega
    have hlen_post : (B.eraseIdx actualIdx).length = B.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    rw [List.getElem_eraseIdx] at heasy ⊢
    by_cases hjlt : j < actualIdx
    · simp only [hjlt, ↓reduceDIte] at heasy ⊢
      exact hInv.easyValue j (by omega) p heasy
    · simp only [hjlt, ↓reduceDIte] at heasy ⊢
      exact hInv.easyValue (j + 1) (by rw [hlen_post] at hj; omega) p heasy

/-- Provider-form skip step for the bundled `S2ReachInv`. -/
private lemma S2ReachInv.skip
    {B : List Labeled} {idx actualIdx : ℕ}
    (hidx : idx < B.length)
    (hactual : actualIdx = B.length - 1 - idx)
    (hnfr : isFlatRemovableBool (forget B) actualIdx = false)
    (hInv : S2ReachInv B idx) :
    S2ReachInv B (idx + 1) :=
  { flat := hInv.flat
    hardSupport := hInv.hardSupport
    remainingEasyFR := allRemainingEasyFR_skip hInv.remainingEasyFR
    noEasyChecked :=
      noEasyInCheckedSuffix_skip hInv.remainingEasyFR hInv.noEasyChecked
        (by omega) (hactual ▸ hnfr)
    noHardZeroBeforeLast := by
      intro hidx_pre h0
      exact hInv.noHardZeroBeforeLast (by omega) h0
    coreNotDiv := hInv.coreNotDiv
    easyValue := hInv.easyValue }

private lemma S2Reach_easy_FR_before_frontier_nonadjacent
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    ∀ (j : ℕ) (hj : j < B.length),
      (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy →
      j + 1 < B.length - 1 - idx →
        isFlatRemovableBool (forget B) j = true := by
  refine S2Reach.rec
    (motive := fun B idx _rec _ =>
      ∀ (j : ℕ) (hj : j < B.length),
        (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy →
        j + 1 < B.length - 1 - idx →
          isFlatRemovableBool (forget B) j = true)
    ?init ?erase ?skip hreach
  · intro j hj heasy _hj_sep
    exact
      easy_parts_are_flat_removable
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos j hj heasy
  · intro B' idx' actualIdx' rec' hidx hactual hfr hprev ih
    intro j hj heasy hj_sep
    have hact_lt : actualIdx' < B'.length := by omega
    have hlen_post : (B'.eraseIdx actualIdx').length = B'.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    have hj_lt_actual : j < actualIdx' := by
      omega
    have hj_pre : j < B'.length := by
      rw [hlen_post] at hj
      omega
    have heasy_pre :
        (B'[j]'hj_pre).origin.map Prod.snd = some InsertionKind.easy := by
      have heq :
          (B'.eraseIdx actualIdx')[j]'hj = B'[j]'hj_pre := by
        rw [List.getElem_eraseIdx]
        simp [hj_lt_actual]
      rwa [heq] at heasy
    have hj_sep_pre : j + 1 < B'.length - 1 - idx' := by
      omega
    have hfr_pre : isFlatRemovableBool (forget B') j = true :=
      ih j hj_pre heasy_pre hj_sep_pre
    have h_fe :
        forget (B'.eraseIdx actualIdx') = (forget B').eraseIdx actualIdx' := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    exact
      isFlatRemovableBool_post_erase_non_adjacent
        (forget B') j actualIdx' (by omega)
        (by rw [length_forget]; exact hact_lt) hfr hfr_pre
  · intro B' idx' actualIdx' rec' hidx hactual hnfr hprev ih
    intro j hj heasy hj_sep
    exact ih j hj heasy (by omega)

/-- The adjacent easy just above a flat-removable S2 frontier is itself
flat-removable.

This is local 3-flat arithmetic plus the reachability fact that easy labels
have values divisible by `3`: the frontier's FR check gives divisibility of the
lower adjacent value, so 3-flatness forces the two adjacent values equal, and
the delete-at-`j` gap is inherited from the old gap above `j`. -/
private lemma S2Reach_easy_FR_immediately_before_frontier
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    {B : List Labeled} {idx j : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (hj : j < B.length)
    (heasy_j : (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy)
    (hfr_act : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hboundary : j + 1 = B.length - 1 - idx) :
    isFlatRemovableBool (forget B) j = true := by
  have hflat_start : IsThreeFlat (forget (processInsertionsLabeled ν A_init)) :=
    processInsertionsLabeled_flat A_init ν hA_flat
  have hflat_B : IsThreeFlat (forget B) :=
    S2Reach_flat hreach hflat_start
  have hj1 : j + 1 < B.length := by omega
  have hmod_j : (B[j]'hj).value % 3 = 0 := by
    obtain ⟨p, hp⟩ := origin_map_snd_eq_easy_exists heasy_j
    have hval :=
      S2Reach_easy_value_eq A_init ν hA_flat hA_clean hν_sort
        hreach j hj p hp
    rw [hval]
    exact Nat.mul_mod_right 3 p
  have hmod_act : (B[j + 1]'hj1).value % 3 = 0 := by
    have hfr_parts := hfr_act
    unfold isFlatRemovableBool at hfr_parts
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_parts
    have hact_lt : B.length - 1 - idx < B.length := by omega
    have hval_eq :
        (forget B)[B.length - 1 - idx]! = (B[j + 1]'hj1).value := by
      rw [getElem!_pos (forget B) (B.length - 1 - idx)
        (by rw [length_forget]; exact hact_lt)]
      simp [forget, List.getElem_map, hboundary]
    rw [hval_eq] at hfr_parts
    exact hfr_parts.1.2
  have heq_adj :
      (B[j]'hj).value = (B[j + 1]'hj1).value :=
    labeled_adjacent_value_eq_of_threeFlat_and_mod3
      (B := B) (i := j) hflat_B hj1
      (by simpa only using hmod_j)
      (by simpa only using hmod_act)
  unfold isFlatRemovableBool
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hj_forget : j < (forget B).length := by
    rw [length_forget]
    exact hj
  refine ⟨⟨hj_forget, ?_⟩, ?_⟩
  · rw [getElem!_pos (forget B) j hj_forget]
    simpa [forget, List.getElem_map] using hmod_j
  · apply isThreeFlatBool_eraseIdx_of_threeFlat_and_gap
      (forget B) j hj_forget (Hints.isThreeFlatBool_of_IsThreeFlat hflat_B)
    · intro hj_pos _hj1_lt
      have habove_gap :
          (B[j - 1]'(by omega)).value - (B[j]'hj).value < 3 := by
        have hgap := hflat_B.2.1 (j - 1)
          (by
            rw [length_forget]
            simpa [show (j - 1) + 1 = j from by omega] using hj)
        simpa [forget, List.getElem_map, show (j - 1) + 1 = j from by omega]
          using hgap
      have hleft_get :
          (forget B)[j - 1]'(by rw [length_forget]; omega) =
            (B[j - 1]'(by omega)).value := by
        simp [forget, List.getElem_map]
      have hright_get :
          (forget B)[j + 1]'(by rw [length_forget]; exact hj1) =
            (B[j + 1]'hj1).value := by
        simp [forget, List.getElem_map]
      rw [hleft_get, hright_get, ← heq_adj]
      exact habove_gap
    · intro hlast hj_pos
      rw [length_forget] at hlast
      omega

/-- Reachability plus the easy live seam gives the current-frontier
easy-delete bridge, without using the bundled `S2ReachInv`.

The non-adjacent cases use the existing reachable FR-transfer theorem.  In the
adjacent case, `S2Reach_easy_FR_immediately_before_frontier` supplies the
upper easy's pre-delete FR fact needed to invoke the guarded easy seam. -/
private lemma S2Reach_EasyFRPreservedUnderFrontierDelete_of_easy_live
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (hlive : S2EasyBoundarySeamGuarded B idx)
    (hidx : idx < B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true) :
    EasyFRPreservedUnderFrontierDelete B idx := by
  intro j hj hjlt hkind
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hlen_post : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact_lt
  have hj_lt_act : j < B.length - 1 - idx := by
    rw [hlen_post] at hjlt
    exact hjlt
  have hj_B : j < B.length := by omega
  have hkind_B :
      (B[j]'hj_B).origin.map Prod.snd = some InsertionKind.easy := by
    have heq :
        (B.eraseIdx (B.length - 1 - idx))[j]'hj = B[j]'hj_B := by
      rw [List.getElem_eraseIdx]
      simp [hj_lt_act]
    rwa [heq] at hkind
  have hmod_j : (B[j]'hj_B).value % 3 = 0 := by
    obtain ⟨p, hp⟩ := origin_map_snd_eq_easy_exists hkind_B
    have hval :=
      S2Reach_easy_value_eq A_init ν hA_flat hA_clean hν_sort
        hreach j hj_B p hp
    rw [hval]
    exact Nat.mul_mod_right 3 p
  have hmod_j_forget :
      (forget B)[j]'(by rw [length_forget]; exact hj_B) % 3 = 0 := by
    simpa [forget, List.getElem_map] using hmod_j
  by_cases hboundary : j + 1 = B.length - 1 - idx
  · have hfr_j : isFlatRemovableBool (forget B) j = true :=
      S2Reach_easy_FR_immediately_before_frontier
        A_init ν hA_flat hA_clean hν_sort hreach hj_B hkind_B hfr hboundary
    have h_fe :
        forget (B.eraseIdx (B.length - 1 - idx)) =
          (forget B).eraseIdx (B.length - 1 - idx) := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    apply isFlatRemovableBool_post_erase_adjacent_of_mod_gap
      (forget B) j (B.length - 1 - idx) hboundary
      (by rw [length_forget]; exact hact_lt)
      hmod_j_forget hfr
    intro hj_pos hj1_lt
    exact
      hlive j hj_B hj_pos hkind_B hfr_j hfr hj_lt_act hboundary hj1_lt
  · have hj1_lt_actual : j + 1 < B.length - 1 - idx := by omega
    have hfr_j : isFlatRemovableBool (forget B) j = true :=
      S2Reach_easy_FR_before_frontier_nonadjacent
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
        hreach j hj_B hkind_B hj1_lt_actual
    have h_fe :
        forget (B.eraseIdx (B.length - 1 - idx)) =
          (forget B).eraseIdx (B.length - 1 - idx) := by
      simp [forget, List.eraseIdx_map]
    rw [h_fe]
    exact
      isFlatRemovableBool_post_erase_non_adjacent
        (forget B) j (B.length - 1 - idx) hj1_lt_actual
        (by rw [length_forget]; exact hact_lt) hfr hfr_j

private lemma S2ReachPostEraseProviderComponents.of_easy_live_and_post_frontier
    {A_init : List Labeled} {ν : List ℕ}
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    (heasy_live : ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
      S2Reach (processInsertionsLabeled ν A_init) B idx rec →
        S2EasyBoundarySeamGuarded B idx)
    (hfrontier : ∀ {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ},
      idx < B.length →
      actualIdx = B.length - 1 - idx →
      isFlatRemovableBool (forget B) actualIdx = true →
      S2Reach (processInsertionsLabeled ν A_init) B idx rec →
        FrontierFRImpliesEasy (B.eraseIdx actualIdx) idx) :
    S2ReachPostEraseProviderComponents A_init ν where
  bridge := by
    intro B idx rec hreach hidx hfr
    exact
      S2Reach_EasyFRPreservedUnderFrontierDelete_of_easy_live
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
        hreach (heasy_live hreach) hidx hfr
  frontier := by
    intro B idx actualIdx rec hidx hactual hfr hreach
    exact hfrontier hidx hactual hfr hreach

/-- Adjacent easy/easy gap when the upper easy has a labeled left neighbor.

This is a purely local part of the duplicate-easy boundary case.  If the element
just above the upper easy is itself labeled, then its value is divisible by `3`
(easy labels by construction, hard labels by the hard-rank/mod invariant
preserved along S2).  3-flatness then forces equality across the labeled/upper
easy pair and across the upper/lower easy pair; the remaining adjacent 3-flat gap
below the lower easy is exactly the post-delete gap we need. -/
private lemma S2Reach_easy_adjacent_gap_of_left_labeled
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    {j : ℕ}
    (hj_pos : 0 < j)
    (hj : j < B.length)
    (heasy_j : (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy)
    (hfr_act : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hboundary : j + 1 = B.length - 1 - idx)
    (hj1_lt : j + 1 < ((forget B).eraseIdx (B.length - 1 - idx)).length)
    (hleft_labeled : (B[j - 1]'(by omega)).origin ≠ none) :
    ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) -
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt < 3 := by
  have hflat_start : IsThreeFlat (forget (processInsertionsLabeled ν A_init)) :=
    processInsertionsLabeled_flat A_init ν hA_flat
  have hflat_B : IsThreeFlat (forget B) :=
    S2Reach_flat hreach hflat_start
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hj1_B : j + 1 < B.length := by omega
  have hj2_B : j + 2 < B.length := by
    rw [List.length_eraseIdx_of_lt] at hj1_lt
    · rw [length_forget] at hj1_lt
      omega
    · rw [length_forget]
      exact hact_lt
  have hmod_left : (B[j - 1]'(by omega)).value % 3 = 0 := by
    rcases Labeled.origin_none_or_easy_or_hard (B[j - 1]'(by omega)) with
      hnone | heasy_or_hard
    · exact False.elim (hleft_labeled hnone)
    · rcases heasy_or_hard with heasy | hhard
      · rcases heasy with ⟨q, hq⟩
        have hval :=
          S2Reach_easy_value_eq A_init ν hA_flat hA_clean hν_sort
            hreach (j - 1) (by omega) q hq
        rw [hval]
        exact Nat.mul_mod_right 3 q
      · rcases hhard with ⟨q, hq⟩
        exact
          S2Reach_hard_value_mod3 A_init ν hA_clean hreach
            (j - 1) (by omega) q hq
  have hmod_j : (B[j]'hj).value % 3 = 0 := by
    obtain ⟨q, hq⟩ := origin_map_snd_eq_easy_exists heasy_j
    have hval :=
      S2Reach_easy_value_eq A_init ν hA_flat hA_clean hν_sort
        hreach j hj q hq
    rw [hval]
    exact Nat.mul_mod_right 3 q
  have hmod_act : (B[j + 1]'hj1_B).value % 3 = 0 := by
    unfold isFlatRemovableBool at hfr_act
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_act
    have hval_eq :
        (forget B)[B.length - 1 - idx]! = (B[j + 1]'hj1_B).value := by
      rw [getElem!_pos (forget B) (B.length - 1 - idx)
        (by rw [length_forget]; exact hact_lt)]
      simp [forget, List.getElem_map, hboundary]
    rw [← hval_eq]
    exact hfr_act.1.2
  have hleft_eq_j :
      (B[j - 1]'(by omega)).value = (B[j]'hj).value := by
    have heq :=
      labeled_adjacent_value_eq_of_threeFlat_and_mod3
        (B := B) (i := j - 1) hflat_B
        (by simpa [show (j - 1) + 1 = j from by omega] using hj)
        (by simpa only using hmod_left)
        (by simpa [show (j - 1) + 1 = j from by omega] using hmod_j)
    simpa [show (j - 1) + 1 = j from by omega] using heq
  have hj_eq_act :
      (B[j]'hj).value = (B[j + 1]'hj1_B).value := by
    exact
      labeled_adjacent_value_eq_of_threeFlat_and_mod3
        (B := B) (i := j) hflat_B hj1_B
        (by simpa only using hmod_j)
        (by simpa only using hmod_act)
  have hbelow_gap :
      (B[j + 1]'hj1_B).value - (B[j + 2]'hj2_B).value < 3 := by
    have hgap := hflat_B.2.1 (j + 1) (by rw [length_forget]; exact hj2_B)
    simpa [forget, List.getElem_map] using hgap
  have hleft_get :
      ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) =
        (B[j - 1]'(by omega)).value := by
    rw [List.getElem_eraseIdx]
    simp [show j - 1 < B.length - 1 - idx from by omega, forget, List.getElem_map]
  have hright_get :
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt =
        (B[j + 2]'hj2_B).value := by
    rw [List.getElem_eraseIdx]
    simp [show ¬ j + 1 < B.length - 1 - idx from by omega, forget, List.getElem_map]
  rw [hleft_get, hright_get, hleft_eq_j, hj_eq_act]
  exact hbelow_gap

/-- Adjacent easy/easy gap when the lower easy has a labeled right neighbor.

This is the symmetric local case to
`S2Reach_easy_adjacent_gap_of_left_labeled`: if the element immediately below the
erased lower easy is labeled, then it is also divisible by `3`.  The upper easy,
the lower easy, and this right neighbor are all adjacent in a 3-flat list and
divisible by `3`, hence have the same value.  The post-delete gap is therefore
the original 3-flat gap from the left endpoint to the upper easy. -/
private lemma S2Reach_easy_adjacent_gap_of_right_labeled
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    {j : ℕ}
    (hj_pos : 0 < j)
    (hj : j < B.length)
    (heasy_j : (B[j]'hj).origin.map Prod.snd = some InsertionKind.easy)
    (hfr_act : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hboundary : j + 1 = B.length - 1 - idx)
    (hj1_lt : j + 1 < ((forget B).eraseIdx (B.length - 1 - idx)).length)
    (hright_labeled : (B[j + 2]'(by
      rw [List.length_eraseIdx_of_lt] at hj1_lt
      · rw [length_forget] at hj1_lt
        omega
      · rw [length_forget]
        omega)).origin ≠ none) :
    ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) -
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt < 3 := by
  have hflat_start : IsThreeFlat (forget (processInsertionsLabeled ν A_init)) :=
    processInsertionsLabeled_flat A_init ν hA_flat
  have hflat_B : IsThreeFlat (forget B) :=
    S2Reach_flat hreach hflat_start
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hj1_B : j + 1 < B.length := by omega
  have hj2_B : j + 2 < B.length := by
    rw [List.length_eraseIdx_of_lt] at hj1_lt
    · rw [length_forget] at hj1_lt
      omega
    · rw [length_forget]
      exact hact_lt
  have hmod_j : (B[j]'hj).value % 3 = 0 := by
    obtain ⟨q, hq⟩ := origin_map_snd_eq_easy_exists heasy_j
    have hval :=
      S2Reach_easy_value_eq A_init ν hA_flat hA_clean hν_sort
        hreach j hj q hq
    rw [hval]
    exact Nat.mul_mod_right 3 q
  have hmod_act : (B[j + 1]'hj1_B).value % 3 = 0 := by
    unfold isFlatRemovableBool at hfr_act
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr_act
    have hval_eq :
        (forget B)[B.length - 1 - idx]! = (B[j + 1]'hj1_B).value := by
      rw [getElem!_pos (forget B) (B.length - 1 - idx)
        (by rw [length_forget]; exact hact_lt)]
      simp [forget, List.getElem_map, hboundary]
    rw [← hval_eq]
    exact hfr_act.1.2
  have hmod_right : (B[j + 2]'hj2_B).value % 3 = 0 := by
    rcases Labeled.origin_none_or_easy_or_hard (B[j + 2]'hj2_B) with
      hnone | heasy_or_hard
    · exact False.elim (hright_labeled (by simpa using hnone))
    · rcases heasy_or_hard with heasy | hhard
      · rcases heasy with ⟨q, hq⟩
        have hval :=
          S2Reach_easy_value_eq A_init ν hA_flat hA_clean hν_sort
            hreach (j + 2) hj2_B q hq
        rw [hval]
        exact Nat.mul_mod_right 3 q
      · rcases hhard with ⟨q, hq⟩
        exact
          S2Reach_hard_value_mod3 A_init ν hA_clean hreach
            (j + 2) hj2_B q hq
  have hj_eq_act :
      (B[j]'hj).value = (B[j + 1]'hj1_B).value :=
    labeled_adjacent_value_eq_of_threeFlat_and_mod3
      (B := B) (i := j) hflat_B hj1_B
      (by simpa only using hmod_j)
      (by simpa only using hmod_act)
  have hact_eq_right :
      (B[j + 1]'hj1_B).value = (B[j + 2]'hj2_B).value :=
    labeled_adjacent_value_eq_of_threeFlat_and_mod3
      (B := B) (i := j + 1) hflat_B hj2_B
      (by simpa only using hmod_act)
      (by simpa only using hmod_right)
  have habove_gap :
      (B[j - 1]'(by omega)).value - (B[j]'hj).value < 3 := by
    have hgap := hflat_B.2.1 (j - 1)
      (by
        rw [length_forget]
        simpa [show (j - 1) + 1 = j from by omega] using hj)
    simpa [forget, List.getElem_map, show (j - 1) + 1 = j from by omega]
      using hgap
  have hleft_get :
      ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) =
        (B[j - 1]'(by omega)).value := by
    rw [List.getElem_eraseIdx]
    simp [show j - 1 < B.length - 1 - idx from by omega, forget, List.getElem_map]
  have hright_get :
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt =
        (B[j + 2]'hj2_B).value := by
    rw [List.getElem_eraseIdx]
    simp [show ¬ j + 1 < B.length - 1 - idx from by omega, forget, List.getElem_map]
  rw [hleft_get, hright_get, ← hact_eq_right, ← hj_eq_act]
  exact habove_gap

/-- Adjacent easy/easy gap once construction history supplies the core endpoint
gap.

This is the arithmetic/list-indexing tail of the core/core duplicate-easy case:
after erasing the lower easy at `j + 1`, the two positions compared are exactly
the old endpoints `j - 1` and `j + 2`. -/
private lemma S2Reach_easy_adjacent_gap_of_core_gap
    {B : List Labeled} {idx j : ℕ}
    (hboundary : j + 1 = B.length - 1 - idx)
    (hj1_lt : j + 1 < ((forget B).eraseIdx (B.length - 1 - idx)).length)
    (hcore_gap :
      (B[j - 1]'(by omega)).value - (B[j + 2]'(by
        rw [List.length_eraseIdx_of_lt] at hj1_lt
        · rw [length_forget] at hj1_lt
          omega
        · rw [length_forget]
          omega)).value < 3) :
    ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) -
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt < 3 := by
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hj2_B : j + 2 < B.length := by
    rw [List.length_eraseIdx_of_lt] at hj1_lt
    · rw [length_forget] at hj1_lt
      omega
    · rw [length_forget]
      exact hact_lt
  have hleft_get :
      ((forget B).eraseIdx (B.length - 1 - idx))[j - 1]'(by omega) =
        (B[j - 1]'(by omega)).value := by
    rw [List.getElem_eraseIdx]
    simp [show j - 1 < B.length - 1 - idx from by omega, forget, List.getElem_map]
  have hright_get :
      ((forget B).eraseIdx (B.length - 1 - idx))[j + 1]'hj1_lt =
        (B[j + 2]'hj2_B).value := by
    rw [List.getElem_eraseIdx]
    simp [show ¬ j + 1 < B.length - 1 - idx from by omega, forget, List.getElem_map]
  rw [hleft_get, hright_get]
  simpa using hcore_gap

private lemma S2Reach_S2ReachInv_and_live_of_provider_components
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    (hcomponents : S2ReachPostEraseProviderComponents A_init ν) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Reach labeled B idx rec → S2ReachInv B idx ∧ S2BoundaryLiveSeams B idx := by
  intro labeled B idx rec hreach
  refine S2Reach.rec
    (motive := fun B idx _ _ => S2ReachInv B idx ∧ S2BoundaryLiveSeams B idx)
    ?init ?eraseCase ?skipCase hreach
  · have hflat_labeled : IsThreeFlat (forget labeled) := by
      show IsThreeFlat (forget (processInsertionsLabeled ν A_init))
      rw [forget_processInsertionsLabeled]
      suffices h : ∀ (parts : List ℕ) (B : List ℕ), IsThreeFlat B →
          IsThreeFlat (processInsertions parts B) from h ν _ hA_flat
      intro parts
      induction parts with
      | nil => intro B hB; exact hB
      | cons p rest ih =>
          intro B hB
          simp only [processInsertions]
          exact ih _ (performInsertion_preserves_flat' B p hB)
    have hInv : S2ReachInv labeled 0 :=
      { flat := hflat_labeled
        hardSupport :=
          processInsertionsLabeled_HardHasSupportingEasy
            A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
        remainingEasyFR :=
          allRemainingEasyFR_zero_processInsertionsLabeled
            A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
        noEasyChecked := noEasyInCheckedSuffix_zero labeled
        noHardZeroBeforeLast := by
          show NoHardAtZeroBeforeLast (processInsertionsLabeled ν A_init) 0
          intro _ h0
          exact processInsertionsLabeled_NoHardAtZero
            A_init ν hA_flat hA_clean h0
        coreNotDiv := by
          intro j hj hcore
          exact processInsertionsLabeled_origin_none_not_div3
            A_init ν hA_reg hA_clean j hj hcore
        easyValue := by
          intro j hj p heasy
          exact processInsertionsLabeled_easy_value_eq
            A_init ν hA_flat hA_clean hν_sort j hj p heasy }
    exact ⟨hInv, S2BoundaryLiveSeams.zero_of_threeFlat hflat_labeled⟩
  · intro B' idx' actualIdx' rec' hidx hactual hfr hprev ih
    have hInvPost : S2ReachInv (B'.eraseIdx actualIdx') idx' :=
      S2ReachInv.erase_of_provider_components
        (A_init := A_init) (ν := ν) hcomponents
        hidx hactual hfr hprev ih.1
    have hLivePost : S2BoundaryLiveSeams (B'.eraseIdx actualIdx') idx' :=
      hcomponents.live_after_erase hA_clean hidx hactual hfr hprev
    exact ⟨hInvPost, hLivePost⟩
  · intro B' idx' actualIdx' rec' hidx hactual hnfr hprev ih
    have hInvSkip : S2ReachInv B' (idx' + 1) :=
      S2ReachInv.skip hidx hactual hnfr ih.1
    have hLiveSkip : S2BoundaryLiveSeams B' (idx' + 1) :=
      hcomponents.live_after_skip hA_clean hidx hactual hnfr hprev
    exact ⟨hInvSkip, hLiveSkip⟩

private lemma S2Reach_S2ReachInv_and_live_of_easy_live_and_post_frontier
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    (heasy_live : ∀ {B : List Labeled} {idx : ℕ} {rec : List ℕ},
      S2Reach (processInsertionsLabeled ν A_init) B idx rec →
        S2EasyBoundarySeamGuarded B idx)
    (hfrontier : ∀ {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ},
      idx < B.length →
      actualIdx = B.length - 1 - idx →
      isFlatRemovableBool (forget B) actualIdx = true →
      S2Reach (processInsertionsLabeled ν A_init) B idx rec →
        FrontierFRImpliesEasy (B.eraseIdx actualIdx) idx) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Reach labeled B idx rec → S2ReachInv B idx ∧ S2BoundaryLiveSeams B idx := by
  intro labeled B idx rec hreach
  exact
    S2Reach_S2ReachInv_and_live_of_provider_components
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
      (S2ReachPostEraseProviderComponents.of_easy_live_and_post_frontier
        hA_flat hA_reg hA_clean hν_sort hν_pos heasy_live hfrontier)
      B idx rec hreach

/-! ### Non-circular live-seam construction. -/

/-- Erasing an **easy** element preserves `CoreEasyGap`.

`CoreEasyGap` is stated purely on origins and values, both of which are
preserved on every surviving element.  A core/core window in `B.eraseIdx k`
maps to the same core/core window in `B`; its strictly-between positions are
either between positions of `B.eraseIdx k` (easy by hypothesis) or the erased
position `k` itself (easy by `hk_easy`). -/
private lemma CoreEasyGap_eraseIdx
    {B : List Labeled} {k : ℕ}
    (hceg : CoreEasyGap B) (hk_lt : k < B.length)
    (hk_easy : (B[k]'hk_lt).origin.map Prod.snd = some InsertionKind.easy) :
    CoreEasyGap (B.eraseIdx k) := by
  have hlen : (B.eraseIdx k).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hk_lt
  intro a b hab ha hb hca hcb hbet
  -- forward map of an eraseIdx index to its B preimage, element equality
  -- stated with an existential witness to dodge `motive` issues.
  have hmapL : ∀ (m : ℕ) (hm : m < (B.eraseIdx k).length) (hmk : m < k),
      (B.eraseIdx k)[m]'hm = B[m]'(by rw [hlen] at hm; omega) := by
    intro m hm hmk; rw [List.getElem_eraseIdx]; simp [hmk]
  have hmapR : ∀ (m : ℕ) (hm : m < (B.eraseIdx k).length) (hmk : ¬ m < k),
      (B.eraseIdx k)[m]'hm = B[m + 1]'(by rw [hlen] at hm; omega) := by
    intro m hm hmk; rw [List.getElem_eraseIdx]; simp [hmk]
  -- B-preimages of `a`, `b`.
  by_cases hak : a < k <;> by_cases hbk : b < k
  -- case a<k, b<k
  · rw [hmapL a ha hak] at hca ⊢
    rw [hmapL b hb hbk] at hcb ⊢
    refine hceg a b hab (by rw [hlen] at ha; omega) (by rw [hlen] at hb; omega) hca hcb ?_
    intro w hw haw hwb
    have hwlt : w < (B.eraseIdx k).length := by rw [hlen]; omega
    have hbw := hbet w hwlt haw hwb
    rwa [hmapL w hwlt (by omega)] at hbw
  -- case a<k, ¬b<k  (so b ≥ k); B window (a, b+1), the erased k may be inside.
  · rw [hmapL a ha hak] at hca ⊢
    rw [hmapR b hb hbk] at hcb ⊢
    refine hceg a (b + 1) (by omega) (by rw [hlen] at ha; omega)
      (by rw [hlen] at hb; omega) hca hcb ?_
    intro w hw haw hwb
    by_cases hwk : w = k
    · subst hwk; exact hk_easy
    · by_cases hwk' : w < k
      · have hwlt : w < (B.eraseIdx k).length := by rw [hlen]; omega
        have hbw := hbet w hwlt (by omega) (by omega)
        rwa [hmapL w hwlt hwk'] at hbw
      · obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
        have hmlt : m < (B.eraseIdx k).length := by rw [hlen]; omega
        have hbw := hbet m hmlt (by omega) (by omega)
        rwa [hmapR m hmlt (by omega)] at hbw
  -- case ¬a<k, b<k : impossible (a<b but a≥k>b).
  · omega
  -- case ¬a<k, ¬b<k : B window (a+1, b+1), entirely above k.
  · rw [hmapR a ha hak] at hca ⊢
    rw [hmapR b hb hbk] at hcb ⊢
    refine hceg (a + 1) (b + 1) (by omega) (by rw [hlen] at ha; omega)
      (by rw [hlen] at hb; omega) hca hcb ?_
    intro w hw haw hwb
    obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
    have hmlt : m < (B.eraseIdx k).length := by rw [hlen]; omega
    have hbw := hbet m hmlt (by omega) (by omega)
    rwa [hmapR m hmlt (by omega)] at hbw

/-- Erasing an **easy** element preserves `HardLowerGap`.

Like `CoreEasyGap`, the predicate only inspects origins and values, which are
preserved.  A hard at `i` with its easy run down to a non-easy `b` in
`B.eraseIdx k` maps to the same configuration in `B`: the run stays a run of
easies (the erased index, if it falls inside, was itself an easy), and the
non-easy lower endpoint stays non-easy.  We additionally need that the element
just above the hard is the same — true since `i - 1 < i` survives. -/
private lemma HardLowerGap_eraseIdx
    {B : List Labeled} {k : ℕ}
    (hhlg : HardLowerGap B)
    (hflat : IsThreeFlat (forget B))
    (hk_lt : k < B.length)
    (hk_easy : (B[k]'hk_lt).origin.map Prod.snd = some InsertionKind.easy) :
    HardLowerGap (B.eraseIdx k) := by
  have hlen : (B.eraseIdx k).length = B.length - 1 :=
    List.length_eraseIdx_of_lt hk_lt
  have hmapL : ∀ (m : ℕ) (hm : m < (B.eraseIdx k).length) (hmk : m < k),
      (B.eraseIdx k)[m]'hm = B[m]'(by rw [hlen] at hm; omega) := by
    intro m hm hmk; rw [List.getElem_eraseIdx]; simp [hmk]
  have hmapR : ∀ (m : ℕ) (hm : m < (B.eraseIdx k).length) (hmk : ¬ m < k),
      (B.eraseIdx k)[m]'hm = B[m + 1]'(by rw [hlen] at hm; omega) := by
    intro m hm hmk; rw [List.getElem_eraseIdx]; simp [hmk]
  intro i b hib hi hb hipos hhard hbet hbne
  -- We split the whole proof on the position of `i` relative to `k`.
  by_cases hik : i < k
  · -- hard preimage `i`, above element is `B[i-1]`, `i - 1 < k`.
    rw [hmapL i hi hik] at hhard
    by_cases hbk : b < k
    · rw [hmapL b hb hbk] at hbne ⊢
      rw [hmapL (i-1) (by rw [hlen]; omega) (by omega)]
      refine hhlg i b (by omega) (by rw [hlen] at hi; omega) (by rw [hlen] at hb; omega)
        hipos hhard ?_ hbne
      intro w hw hiw hwb
      have hwlt : w < (B.eraseIdx k).length := by rw [hlen]; omega
      have hbw := hbet w hwlt (by omega) (by omega)
      rwa [hmapL w hwlt (by omega)] at hbw
    · rw [hmapR b hb hbk] at hbne ⊢
      rw [hmapL (i-1) (by rw [hlen]; omega) (by omega)]
      refine hhlg i (b+1) (by omega) (by rw [hlen] at hi; omega) (by rw [hlen] at hb; omega)
        hipos hhard ?_ hbne
      intro w hw hiw hwb
      by_cases hwk : w = k
      · subst hwk; exact hk_easy
      · by_cases hwk' : w < k
        · have hwlt : w < (B.eraseIdx k).length := by rw [hlen]; omega
          have hbw := hbet w hwlt (by omega) (by omega)
          rwa [hmapL w hwlt hwk'] at hbw
        · obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
          have hmlt : m < (B.eraseIdx k).length := by rw [hlen]; omega
          have hbw := hbet m hmlt (by omega) (by omega)
          rwa [hmapR m hmlt (by omega)] at hbw
  · push_neg at hik
    -- in both remaining cases `i ≥ k`, write `i = t + 1` so `i - 1 = t`.
    obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
    by_cases hik' : t + 1 = k
    · -- hard sits exactly above the erased slot: preimage `t + 2 = k + 1`.
      rw [hmapR (t+1) hi (by omega)] at hhard
      have hb_gt : ¬ b < k := by omega
      rw [hmapR b hb hb_gt] at hbne ⊢
      have habove : (B.eraseIdx k)[(t+1)-1]'(by omega) = B[t]'(by omega) :=
        hmapL t (by rw [hlen]; omega) (by omega)
      rw [habove]
      -- HardLowerGap at (t+2, b+1) bounds against `B[t+1]` (= B[k], the erased
      -- easy); then `B[k] ≤ B[k-1] = B[t]` by descending 3-flatness.
      have hgap : (B[b+1]'(by rw [hlen] at hb; omega)).value + 3 ≤
          (B[t+1]'(by omega)).value := by
        have := hhlg (t+1+1) (b+1) (by omega) (by rw [hlen] at hi; omega)
          (by rw [hlen] at hb; omega) (by omega) hhard ?_ hbne
        · simpa [show t + 1 + 1 - 1 = t + 1 from by omega] using this
        · intro w hw hiw hwb
          by_cases hwk : w = k
          · subst hwk; omega
          · obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
            have hmlt : m < (B.eraseIdx k).length := by rw [hlen]; omega
            have hbw := hbet m hmlt (by omega) (by omega)
            rwa [hmapR m hmlt (by omega)] at hbw
      have hmono := forget_threeFlat_value_le hflat (x := t) (y := t + 1)
        (by omega) (by omega) (by omega)
      omega
    · -- `t + 1 > k`: preimage `t + 2`; post `[i-1] = post[t] = B[t+1]`.
      have hik2 : k < t + 1 := by omega
      rw [hmapR (t+1) hi (by omega)] at hhard
      have hb_gt : ¬ b < k := by omega
      rw [hmapR b hb hb_gt] at hbne ⊢
      have habove : (B.eraseIdx k)[(t+1)-1]'(by omega) = B[t+1]'(by omega) :=
        hmapR t (by rw [hlen]; omega) (by omega)
      rw [habove]
      have hgap := hhlg (t+1+1) (b+1) (by omega) (by rw [hlen] at hi; omega)
        (by rw [hlen] at hb; omega) (by omega) hhard ?_ hbne
      · simpa [show t + 1 + 1 - 1 = t + 1 from by omega] using hgap
      · intro w hw hiw hwb
        by_cases hwk : w = k
        · subst hwk; omega
        · obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
          have hmlt : m < (B.eraseIdx k).length := by rw [hlen]; omega
          have hbw := hbet m hmlt (by omega) (by omega)
          rwa [hmapR m hmlt (by omega)] at hbw

/-- Piece 6: the guarded hard-boundary seam from `HardLowerGap`.

If a hard at `i` has its easy supporter at `i + 1 = frontier`, then `i + 2`
sits in the checked suffix (it equals `B.length - idx`), hence is non-easy by
`NoEasyInCheckedSuffix`.  The single intervening position `i + 1` is the easy
supporter, so `HardLowerGap` at `(i, i + 2)` yields the `≥ 3` lower seam. -/
private lemma hardSeam_of_HardLowerGap
    {B : List Labeled} {idx : ℕ}
    (hgap : HardLowerGap B)
    (hchecked : NoEasyInCheckedSuffix B idx) :
    S2HardBoundarySeamGuarded B idx := by
  intro i p hi hhard hi1 heasy hfr_act hi1_eq hi_pos him1 hi2
  -- `i + 2 = B.length - idx`, hence in the checked suffix.
  have hb_noteasy :
      (B[i + 2]'hi2).origin.map Prod.snd ≠ some InsertionKind.easy :=
    hchecked (i + 2) hi2 (by omega)
  have hrun :
      ∀ (w : ℕ) (hw : w < B.length), i < w → w < i + 2 →
        (B[w]'hw).origin.map Prod.snd = some InsertionKind.easy := by
    intro w hw hiw hwi
    have hw_eq : w = i + 1 := by omega
    subst hw_eq
    exact heasy
  have hhard' : (B[i]'hi).origin.map Prod.snd = some InsertionKind.hard := by
    rw [hhard]; rfl
  exact hgap i (i + 2) (by omega) hi hi2 hi_pos hhard' hrun hb_noteasy

/-- Piece 4: `FrontierFRImpliesEasy` from the same-state core invariants.

The FR frontier is `≡ 0 mod 3`, hence (cores are never divisible by 3) easy or
hard.  A hard frontier would have an easy supporter at `frontier + 1`, which
lies in the checked suffix `B.length - idx ≤ frontier + 1`, contradicting
`NoEasyInCheckedSuffix`. -/
private lemma frontierFRImpliesEasy_of_invariants
    {B : List Labeled} {idx : ℕ}
    (hcore : ∀ (j : ℕ) (hj : j < B.length),
      (B[j]'hj).origin = none → (B[j]'hj).value % 3 ≠ 0)
    (hhardSupport : HardHasSupportingEasy B)
    (hchecked : NoEasyInCheckedSuffix B idx) :
    FrontierFRImpliesEasy B idx := by
  apply frontierFRImpliesEasy_of_noHard hcore
  intro hidx hfr q hhard
  -- `hhard : B[frontier].origin = some (q, hard)`, `hfr : FR frontier`.
  have hact : B.length - 1 - idx < B.length := by omega
  obtain ⟨hi1, heasy_supp⟩ :=
    hhardSupport (B.length - 1 - idx) hact q hhard hfr
  -- supporter at frontier + 1 is in the checked suffix.
  exact hchecked (B.length - 1 - idx + 1) hi1 (by omega) heasy_supp

/-- Piece 5: the guarded easy-boundary seam from `CoreEasyGap`.

The duplicate-easy post-delete gap is reduced (via the three adjacent-gap
helpers) to: a labeled left neighbor, a labeled right neighbor, or two core
endpoints sandwiching the two adjacent easies `j` and `j + 1 = frontier`
(the latter being easy by `FrontierFRImpliesEasy`).  The core/core case is
exactly `CoreEasyGap` at `(j - 1, j + 2)`. -/
private lemma S2Reach_easySeam
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec)
    (hcoreGap : CoreEasyGap B)
    (hfrontierEasy : FrontierFRImpliesEasy B idx) :
    S2EasyBoundarySeamGuarded B idx := by
  intro j hj hj_pos heasy_j hfr_j hfr_act hj_lt_act hboundary hj1_lt
  have hact_lt : B.length - 1 - idx < B.length := by omega
  have hj2_B : j + 2 < B.length := by
    rw [List.length_eraseIdx_of_lt (by rw [length_forget]; exact hact_lt)] at hj1_lt
    rw [length_forget] at hj1_lt
    omega
  by_cases hleft : (B[j - 1]'(by omega)).origin ≠ none
  · exact
      S2Reach_easy_adjacent_gap_of_left_labeled
        A_init ν hA_flat hA_clean hν_sort hreach hj_pos hj heasy_j
        hfr_act hboundary hj1_lt hleft
  · by_cases hright : (B[j + 2]'hj2_B).origin ≠ none
    · exact
        S2Reach_easy_adjacent_gap_of_right_labeled
          A_init ν hA_flat hA_clean hν_sort hreach hj_pos hj heasy_j
          hfr_act hboundary hj1_lt (by simpa using hright)
    · -- both endpoints are cores; use `CoreEasyGap` at `(j - 1, j + 2)`.
      push_neg at hleft hright
      have hidx_lt : idx < B.length := by omega
      -- `j + 1 = frontier` is FR (= frontier) hence easy.
      have hj1_B : j + 1 < B.length := by omega
      have heasy_j1 :
          (B[j + 1]'hj1_B).origin.map Prod.snd = some InsertionKind.easy := by
        have := hfrontierEasy hidx_lt hfr_act
        simpa [hboundary] using this
      have hcore_gap :
          (B[j - 1]'(by omega)).value < (B[j + 2]'hj2_B).value + 3 := by
        refine hcoreGap (j - 1) (j + 2) (by omega) (by omega) hj2_B hleft hright ?_
        intro w hw hak hkb
        rcases (by omega : w = j ∨ w = j + 1) with hw_eq | hw_eq
        · subst hw_eq; exact heasy_j
        · subst hw_eq; exact heasy_j1
      exact
        S2Reach_easy_adjacent_gap_of_core_gap hboundary hj1_lt
          (by omega)

/-- Piece 3: the bundle of reachable-state invariants, proved by a single
`S2Reach.rec` over the construction-history seams `CoreEasyGap`/`HardLowerGap`.

The fields, in order, are:
`flat`, `coreNotDiv`, `NoEasyInCheckedSuffix`, `AllRemainingEasyFR`,
`HardHasSupportingEasy`, `CoreEasyGap`, `HardLowerGap`.  The first four together
with `HardHasSupportingEasy` reconstruct `FrontierFRImpliesEasy` (Piece 4) at
every state; `AllRemainingEasyFR` after an erase is the easy-delete bridge,
discharged from the predecessor easy seam (Piece 5), which itself is built from
`CoreEasyGap` + `FrontierFRImpliesEasy`.  The hard erase-boundary subcase of
`HardHasSupportingEasy` is closed by the predecessor hard seam (Piece 6) built
from `HardLowerGap`. -/
private lemma S2Reach_invariants
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    IsThreeFlat (forget B) ∧
    (∀ (j : ℕ) (hj : j < B.length),
      (B[j]'hj).origin = none → (B[j]'hj).value % 3 ≠ 0) ∧
    NoEasyInCheckedSuffix B idx ∧
    AllRemainingEasyFR B idx ∧
    HardHasSupportingEasy B ∧
    CoreEasyGap B ∧
    HardLowerGap B := by
  refine S2Reach.rec
    (motive := fun B idx _rec _ =>
      IsThreeFlat (forget B) ∧
      (∀ (j : ℕ) (hj : j < B.length),
        (B[j]'hj).origin = none → (B[j]'hj).value % 3 ≠ 0) ∧
      NoEasyInCheckedSuffix B idx ∧
      AllRemainingEasyFR B idx ∧
      HardHasSupportingEasy B ∧
      CoreEasyGap B ∧
      HardLowerGap B)
    ?init ?eraseCase ?skipCase hreach
  · -- init: B = processInsertionsLabeled ν A_init, idx = 0.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact processInsertionsLabeled_flat A_init ν hA_flat
    · intro j hj hcore
      exact processInsertionsLabeled_origin_none_not_div3
        A_init ν hA_reg hA_clean j hj hcore
    · exact noEasyInCheckedSuffix_zero _
    · exact allRemainingEasyFR_zero_processInsertionsLabeled
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
    · exact processInsertionsLabeled_HardHasSupportingEasy
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
    · exact processInsertionsLabeled_CoreEasyGap ν A_init
        (CoreEasyGap.of_clean hA_clean hA_flat)
    · refine processInsertionsLabeled_HardLowerGap ν A_init hA_flat ?_
        (HardLowerGap.of_clean hA_clean)
      intro i hi hne
      exact absurd (hA_clean _ (List.getElem_mem hi)) hne
  · -- erase: B'.eraseIdx actualIdx', idx' (predecessor B' at idx').
    intro B' idx' actualIdx' rec' hidx hactual hfr hprev ih
    obtain ⟨ihflat, ihcore, ihchecked, ihrem, ihhard, ihceg, ihhlg⟩ := ih
    subst hactual
    set actualIdx' := B'.length - 1 - idx' with hactdef
    have hact_lt : actualIdx' < B'.length := by omega
    have hlen_post : (B'.eraseIdx actualIdx').length = B'.length - 1 :=
      List.length_eraseIdx_of_lt hact_lt
    have h_fe : forget (B'.eraseIdx actualIdx') = (forget B').eraseIdx actualIdx' := by
      simp [forget, List.eraseIdx_map]
    have hreachPost :
        S2Reach (processInsertionsLabeled ν A_init) (B'.eraseIdx actualIdx') idx'
          (rec' ++ [(forget B')[actualIdx']! / 3]) :=
      S2Reach.erase (start := processInsertionsLabeled ν A_init)
        (B := B') (idx := idx') (actualIdx := actualIdx') (rec := rec')
        hidx rfl hfr hprev
    -- post-erase flat:
    have hflat_post : IsThreeFlat (forget (B'.eraseIdx actualIdx')) := by
      rw [h_fe]
      unfold isFlatRemovableBool at hfr
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
      exact isThreeFlatBool_implies' _ hfr.2
    -- predecessor's frontier classifier, easy seam, hard seam.
    have ihfront : FrontierFRImpliesEasy B' idx' :=
      frontierFRImpliesEasy_of_invariants ihcore ihhard ihchecked
    -- the erased frontier is easy.
    have hk_easy :
        (B'[actualIdx']'hact_lt).origin.map Prod.snd = some InsertionKind.easy := by
      have := ihfront hidx hfr
      simpa [hactdef] using this
    have iheasySeam : S2EasyBoundarySeamGuarded B' idx' :=
      S2Reach_easySeam A_init ν hA_flat hA_clean hν_sort hprev ihceg ihfront
    have ihhardSeam : S2HardBoundarySeamGuarded B' idx' :=
      hardSeam_of_HardLowerGap ihhlg ihchecked
    have ihnoZero : NoHardAtZeroBeforeLast B' idx' :=
      S2Reach_NoHardAtZeroBeforeLast A_init ν hA_flat hA_clean B' idx' rec' hprev
    refine ⟨hflat_post, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- coreNotDiv survives erase.
      intro j hj hcore
      rw [List.getElem_eraseIdx] at hcore ⊢
      by_cases hjlt : j < actualIdx'
      · simp only [hjlt, ↓reduceDIte] at hcore ⊢
        exact ihcore j (by omega) hcore
      · simp only [hjlt, ↓reduceDIte] at hcore ⊢
        exact ihcore (j + 1) (by rw [hlen_post] at hj; omega) hcore
    · -- NoEasyInCheckedSuffix survives erase (mechanical).
      exact noEasyInCheckedSuffix_delete ihchecked (by omega)
    · -- AllRemainingEasyFR after erase = easy-delete bridge from predecessor seam.
      have hbridge : EasyFRPreservedUnderFrontierDelete B' idx' :=
        S2Reach_EasyFRPreservedUnderFrontierDelete_of_easy_live
          A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
          hprev iheasySeam hidx hfr
      intro j hj hjlt hkind
      exact hbridge j hj hjlt hkind
    · -- HardHasSupportingEasy survives erase.
      intro i hi p hhard hfr_post
      have hfr_forget : isFlatRemovableBool ((forget B').eraseIdx actualIdx') i = true := by
        rw [← h_fe]; exact hfr_post
      have hact_lt_forget : actualIdx' < (forget B').length := by
        rw [length_forget]; exact hact_lt
      by_cases hilt : i < actualIdx'
      · -- hard at `i` in `B'` (left of erased frontier).
        have hi_lt_B' : i < B'.length := by omega
        have horg_i : (B'[i]'hi_lt_B').origin = some (p, .hard) := by
          have heq : (B'.eraseIdx actualIdx')[i]'hi = B'[i]'hi_lt_B' := by
            rw [List.getElem_eraseIdx]; simp [hilt]
          rw [heq] at hhard; exact hhard
        have hfr_B' : isFlatRemovableBool (forget B') i = true :=
          isFlatRemovableBool_transfer_left (forget B') i actualIdx' hilt
            hact_lt_forget ihflat hfr hfr_forget
        obtain ⟨hi1_B', heasy_B'⟩ := ihhard i hi_lt_B' p horg_i hfr_B'
        by_cases hi1_lt_k : i + 1 < actualIdx'
        · have hi1_lt_post : i + 1 < (B'.eraseIdx actualIdx').length := by
            rw [hlen_post]; omega
          refine ⟨hi1_lt_post, ?_⟩
          have heq : (B'.eraseIdx actualIdx')[i+1]'hi1_lt_post = B'[i+1]'hi1_B' := by
            rw [List.getElem_eraseIdx]; simp [hi1_lt_k]
          rw [heq]; exact heasy_B'
        · -- boundary: supporter `i + 1 = actualIdx'` is the erased frontier.
          push_neg at hi1_lt_k
          have hi1_eq : i + 1 = B'.length - 1 - idx' := by omega
          exact False.elim
            (hardSupport_boundary_contradicts_FR_of_guarded_seam
              ihnoZero ihhardSeam hi_lt_B' horg_i hi1_B' heasy_B' hfr hi1_eq hfr_post)
      · -- hard at `i + 1` in `B'` (right of erased frontier); no boundary issue.
        push_neg at hilt
        have hi_lt_post_eq : i < B'.length - 1 := by rw [← hlen_post]; exact hi
        have hi1_lt_B' : i + 1 < B'.length := by omega
        have horg_i1 : (B'[i+1]'hi1_lt_B').origin = some (p, .hard) := by
          have heq : (B'.eraseIdx actualIdx')[i]'hi = B'[i+1]'hi1_lt_B' := by
            rw [List.getElem_eraseIdx]
            simp [show ¬(i < actualIdx') from by omega]
          rw [heq] at hhard; exact hhard
        have hfr_B'_i1 : isFlatRemovableBool (forget B') (i + 1) = true :=
          isFlatRemovableBool_transfer_right (forget B') i actualIdx'
            (by omega : ¬(i < actualIdx'))
            (by rw [length_forget]; omega)
            hact_lt_forget ihflat hfr hfr_forget
        obtain ⟨hi2_B', heasy_B'⟩ := ihhard (i+1) hi1_lt_B' p horg_i1 hfr_B'_i1
        have hi1_lt_post : i + 1 < (B'.eraseIdx actualIdx').length := by
          rw [hlen_post]; omega
        refine ⟨hi1_lt_post, ?_⟩
        have heq : (B'.eraseIdx actualIdx')[i+1]'hi1_lt_post = B'[i+2]'hi2_B' := by
          rw [List.getElem_eraseIdx]
          simp [show ¬(i + 1 < actualIdx') from by omega]
        rw [heq]; exact heasy_B'
    · -- CoreEasyGap survives erase: values unchanged, only an easy frontier removed.
      exact CoreEasyGap_eraseIdx ihceg hact_lt hk_easy
    · -- HardLowerGap survives erase.
      exact HardLowerGap_eraseIdx ihhlg ihflat hact_lt hk_easy
  · -- skip: B' unchanged, idx' → idx' + 1.
    intro B' idx' actualIdx' rec' hidx hactual hnfr hprev ih
    obtain ⟨ihflat, ihcore, ihchecked, ihrem, ihhard, ihceg, ihhlg⟩ := ih
    refine ⟨ihflat, ihcore, ?_, allRemainingEasyFR_skip ihrem, ihhard, ihceg, ihhlg⟩
    exact noEasyInCheckedSuffix_skip ihrem ihchecked (by omega) (hactual ▸ hnfr)

/-- `FrontierFRImpliesEasy` (Piece 4) holds at every S2-reachable state. -/
private lemma S2Reach_frontierFRImpliesEasy
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    FrontierFRImpliesEasy B idx := by
  obtain ⟨_, hcore, hchecked, _, hhard, _, _⟩ :=
    S2Reach_invariants A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos hreach
  exact frontierFRImpliesEasy_of_invariants hcore hhard hchecked

/-- `heasy_live` (Piece 5): the guarded easy-boundary seam at every reachable
state. -/
private lemma S2Reach_heasy_live
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2EasyBoundarySeamGuarded B idx := by
  obtain ⟨_, hcore, hchecked, _, hhard, hceg, _⟩ :=
    S2Reach_invariants A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos hreach
  have hfront := frontierFRImpliesEasy_of_invariants hcore hhard hchecked
  exact S2Reach_easySeam A_init ν hA_flat hA_clean hν_sort hreach hceg hfront

/-- `hfrontier` (Piece 7): the post-erase frontier classifier at every reachable
state, obtained by applying Piece 4 to the (also reachable) post-erase state. -/
private lemma S2Reach_hfrontier
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx actualIdx : ℕ} {rec : List ℕ}
    (hidx : idx < B.length)
    (hactual : actualIdx = B.length - 1 - idx)
    (hfr : isFlatRemovableBool (forget B) actualIdx = true)
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    FrontierFRImpliesEasy (B.eraseIdx actualIdx) idx := by
  have hreachPost :
      S2Reach (processInsertionsLabeled ν A_init) (B.eraseIdx actualIdx) idx
        (rec ++ [(forget B)[actualIdx]! / 3]) :=
    S2Reach.erase (start := processInsertionsLabeled ν A_init)
      (B := B) (idx := idx) (actualIdx := actualIdx) (rec := rec)
      hidx hactual hfr hreach
  exact
    S2Reach_frontierFRImpliesEasy A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
      hreachPost

private lemma S2Reach_S2ReachInv_and_live
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    {B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hreach : S2Reach (processInsertionsLabeled ν A_init) B idx rec) :
    S2ReachInv B idx ∧ S2BoundaryLiveSeams B idx :=
  -- Non-circular: route through the easy-live seam (Piece 5) and the post-erase
  -- frontier classifier (Piece 7), both built from `CoreEasyGap`/`HardLowerGap`.
  S2Reach_S2ReachInv_and_live_of_easy_live_and_post_frontier
    A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
    (fun {B idx rec} hr =>
      S2Reach_heasy_live A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos hr)
    (fun {B idx actualIdx rec} hidx hactual hfr hr =>
      S2Reach_hfrontier A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
        hidx hactual hfr hr)
    B idx rec hreach

private lemma S2Reach_S2ReachInv
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Reach labeled B idx rec → S2ReachInv B idx := by
  -- Non-circular re-export: the bundled invariant comes from the easy-live /
  -- post-frontier provider route (see `S2Reach_S2ReachInv_and_live`).
  intro labeled B idx rec hreach
  exact
    (S2Reach_S2ReachInv_and_live
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos hreach).1

/-- HardHasSupportingEasy holds at every S2Reach-reachable state.
Re-exported via the bundled invariant `S2Reach_S2ReachInv`. -/
private lemma S2Reach_HardHasSupportingEasy
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Reach labeled B idx rec → HardHasSupportingEasy B := by
  intro labeled B idx rec hreach
  exact
    (S2Reach_S2ReachInv A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
      B idx rec hreach).hardSupport

private lemma S2Reach_EasyFRPreservedUnderFrontierDelete
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Reach labeled B idx rec →
      ∀ (_hidx : ¬ idx ≥ B.length)
        (_hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        EasyFRPreservedUnderFrontierDelete B idx := by
  intro labeled B idx rec hreach hidx hfr
  -- The post-erase state is also S2Reach-reachable.  Its `remainingEasyFR`
  -- component is exactly the predicate body of
  -- `EasyFRPreservedUnderFrontierDelete B idx`.
  have hreach' :
      S2Reach labeled (B.eraseIdx (B.length - 1 - idx)) idx
        (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) :=
    S2Reach.erase (start := labeled) (B := B) (idx := idx)
      (actualIdx := B.length - 1 - idx) (rec := rec) (by omega) rfl hfr hreach
  intro j hj hjlt hkind
  exact
    (S2Reach_S2ReachInv A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
      (B.eraseIdx (B.length - 1 - idx)) idx _ hreach').remainingEasyFR
      j hj hjlt hkind

/-- P2: post-delete frontier is not hard.

From `HardHasSupportingEasy` on the erased list `B'`: if `B'[L'-1-idx]` were
hard FR, there'd be an easy at the next position.  But by `noEasyInCheckedSuffix`
that position has no easy.  The boundary case `idx = 0` is handled separately
via 3-flatness (last element < 3, but hard values ≥ 3). -/
private lemma s2_no_hard_FR_after_easy_delete
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (_hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hsupp_post : HardHasSupportingEasy (B.eraseIdx (B.length - 1 - idx))) :
    ∀ (hidx_erased : idx < (B.eraseIdx (B.length - 1 - idx)).length)
      (_hfr_erased : isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx)))
        ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true)
      (p : ℕ),
      ((B.eraseIdx (B.length - 1 - idx))[
        (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
          some (p, InsertionKind.hard) → False := by
  intro hidx_erased hfr_erased p hhard
  set B' := B.eraseIdx (B.length - 1 - idx) with hB'_def
  have hact : B.length - 1 - idx < B.length := by omega
  have hlen_B' : B'.length = B.length - 1 :=
    List.length_eraseIdx_of_lt hact
  -- Apply HardHasSupportingEasy at position B'.length - 1 - idx in B'.
  have hpos_lt : B'.length - 1 - idx < B'.length := by
    rw [hlen_B']; omega
  have hhard' : (B'[B'.length - 1 - idx]'hpos_lt).origin =
      some (p, InsertionKind.hard) := by
    convert hhard using 2
  have ⟨hi1, heasy_succ⟩ :=
    hsupp_post (B'.length - 1 - idx) hpos_lt p hhard' hfr_erased
  -- The supporting easy is at B'.length - 1 - idx + 1, which equals B'.length - idx.
  -- In B' at idx, the checked suffix is positions ≥ B'.length - idx.
  have hchecked_B' : NoEasyInCheckedSuffix B' idx :=
    noEasyInCheckedSuffix_delete hgood.noEasyChecked hidx
  -- Apply directly at position (B'.length - 1 - idx) + 1.
  have hge : B'.length - idx ≤ (B'.length - 1 - idx) + 1 := by
    rw [hlen_B']; omega
  exact hchecked_B' ((B'.length - 1 - idx) + 1) hi1 hge heasy_succ

private lemma s2_no_hard_FR_at_next_after_skip
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (_hidx : ¬ idx ≥ B.length)
    (hfr_pre : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false)
    (hsupp : HardHasSupportingEasy B) :
    ∀ (hidx_next : idx + 1 < B.length)
      (_hfr_next : isFlatRemovableBool (forget B) (B.length - 1 - (idx + 1)) = true)
      (p : ℕ),
      (B[B.length - 1 - (idx + 1)]'(by omega)).origin =
        some (p, InsertionKind.hard) → False := by
  intro hidx_next _hfr_next p hhard
  -- Apply HardHasSupportingEasy at position B.length - 1 - (idx + 1).
  have hi_lt : B.length - 1 - (idx + 1) < B.length := by omega
  have ⟨hi1, heasy⟩ :=
    hsupp (B.length - 1 - (idx + 1)) hi_lt p hhard _hfr_next
  -- Supporting easy is at B.length - 1 - (idx + 1) + 1, which equals B.length - 1 - idx.
  -- Apply remainingEasyFR directly at that position.
  have hunchecked : (B.length - 1 - (idx + 1)) + 1 < B.length - idx := by omega
  have hfr_easy := hgood.remainingEasyFR ((B.length - 1 - (idx + 1)) + 1) hi1
    hunchecked heasy
  -- The position (B.length - 1 - (idx + 1)) + 1 equals B.length - 1 - idx, so the
  -- FR claim is on the current frontier, which by hfr_pre is NOT FR.
  have hpos_eq : (B.length - 1 - (idx + 1)) + 1 = B.length - 1 - idx := by omega
  rw [hpos_eq] at hfr_easy
  rw [hfr_pre] at hfr_easy
  cases hfr_easy

private lemma S2Good_at_terminal_of_S2Good_geometric
    {target : Multiset ℕ} {start : List Labeled}
    (hdelete_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
        S2Good target start B idx rec →
          NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx ∧
          AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
          FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx)
    (hskip_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ B.length)
        (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
        S2Good target start B idx rec →
          FrontierFRImpliesEasy B (idx + 1)) :
    ∀ (fuel : ℕ) (B : List Labeled) (idx : ℕ) (rec : List ℕ),
      S2Good target start B idx rec →
      fuel ≥ B.length - idx →
        let pair := scanFromSmallestLabeled fuel B idx rec
        ∃ (idx_final : ℕ),
          S2Good target start pair.1 idx_final pair.2 ∧
          idx_final ≥ pair.1.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro B idx rec hgood hfuel
    have hterminal : idx ≥ B.length := by omega
    refine ⟨idx, ?_, ?_⟩
    · simp [scanFromSmallestLabeled]
      exact hgood
    · simp [scanFromSmallestLabeled]
      exact hterminal
  | succ fuel' ih =>
    intro B idx rec hgood hfuel
    by_cases hidx_ge : idx ≥ B.length
    · refine ⟨idx, ?_, ?_⟩
      · simp [scanFromSmallestLabeled, hidx_ge]
        exact hgood
      · simp [scanFromSmallestLabeled, hidx_ge]
    · by_cases hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true
      · obtain ⟨hchecked, hremaining, hfrontier⟩ :=
          hdelete_geom B idx rec hidx_ge hfr hgood
        have hgood' := s2Good_delete_from_preservation hgood hidx_ge hfr
          hchecked hremaining hfrontier
        have hact : B.length - 1 - idx < B.length := by omega
        have hlen_erase : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
          List.length_eraseIdx_of_lt hact
        have hpair_eq :
            scanFromSmallestLabeled (fuel' + 1) B idx rec =
              scanFromSmallestLabeled fuel' (B.eraseIdx (B.length - 1 - idx)) idx
                (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) := by
          simp only [scanFromSmallestLabeled]
          rw [if_neg hidx_ge, if_pos hfr]
        rw [hpair_eq]
        apply ih
        · exact hgood'
        · rw [hlen_erase]; omega
      · have hfr_false : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false := by
          cases hc : isFlatRemovableBool (forget B) (B.length - 1 - idx) with
          | false => rfl
          | true => exact False.elim (hfr hc)
        have hgood' := s2Good_skip hgood hidx_ge hfr_false
          (hskip_geom B idx rec hidx_ge hfr_false hgood)
        have hpair_eq :
            scanFromSmallestLabeled (fuel' + 1) B idx rec =
              scanFromSmallestLabeled fuel' B (idx + 1) rec := by
          simp only [scanFromSmallestLabeled]
          rw [if_neg hidx_ge, if_neg (by simpa [hfr_false])]
        rw [hpair_eq]
        apply ih
        · exact hgood'
        · omega

/-- P1: post-delete unchecked easies are FR. Direct from
`EasyFRPreservedUnderFrontierDelete`. -/
private lemma s2_post_delete_easy_FR
    {target : Multiset ℕ} {start B : List Labeled} {idx : ℕ} {rec : List ℕ}
    (hgood : S2Good target start B idx rec)
    (hidx : ¬ idx ≥ B.length)
    (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true)
    (hbridge : EasyFRPreservedUnderFrontierDelete B idx) :
    ∀ (j : ℕ) (hj : j < (B.eraseIdx (B.length - 1 - idx)).length),
      j < (B.eraseIdx (B.length - 1 - idx)).length - idx →
      ((B.eraseIdx (B.length - 1 - idx))[j]'hj).origin.map Prod.snd =
        some InsertionKind.easy →
      isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) j = true :=
  fun j hj hjlt hkind => hbridge j hj hjlt hkind

private lemma s2_process_history_safe
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    (∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        (∀ (j : ℕ) (hj : j < (B.eraseIdx (B.length - 1 - idx)).length),
          j < (B.eraseIdx (B.length - 1 - idx)).length - idx →
          ((B.eraseIdx (B.length - 1 - idx))[j]'hj).origin.map Prod.snd =
            some InsertionKind.easy →
          isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) j = true) ∧
        (∀ (hidx_erased : idx < (B.eraseIdx (B.length - 1 - idx)).length)
          (hfr_erased : isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx)))
            ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true)
          (p : ℕ),
          ((B.eraseIdx (B.length - 1 - idx))[
            (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
              some (p, InsertionKind.hard) → False)) ∧
    (∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
      S2Good (easyMS labeled) labeled B idx rec →
        ∀ (hidx_next : idx + 1 < B.length)
          (hfr_next : isFlatRemovableBool (forget B) (B.length - 1 - (idx + 1)) = true)
          (p : ℕ),
          (B[B.length - 1 - (idx + 1)]'(by omega)).origin =
            some (p, InsertionKind.hard) → False) ∧
    (let unl := forget labeled
     let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
     let afterS2L := s2L_pair.1
     easyLabels afterS2L = []) := by
  -- Refactored: the combined claim is built from the focused trajectory
  -- invariants `S2Reach_HardHasSupportingEasy` and
  -- `S2Reach_EasyFRPreservedUnderFrontierDelete`.
  intro labeled
  have htraj := S2Reach_HardHasSupportingEasy A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hbridge_traj :=
    S2Reach_EasyFRPreservedUnderFrontierDelete A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  -- Build the geometric inputs to the scan-preservation engine
  have hdelete_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx ∧
        AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
        FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx := by
    intro B idx rec hidx hfr hgood
    refine ⟨noEasyInCheckedSuffix_delete hgood.noEasyChecked hidx, ?_, ?_⟩
    · exact s2_post_delete_easy_FR hgood hidx hfr
        (hbridge_traj B idx rec hgood.reach hidx hfr)
    · -- FrontierFRImpliesEasy (post-delete) idx via "no hard frontier + cores not div"
      apply frontierFRImpliesEasy_of_noHard
      · intro j hj hnone
        have hact : B.length - 1 - idx < B.length := by omega
        have hlen_erase : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
          List.length_eraseIdx_of_lt hact
        have heq := List.getElem_eraseIdx (l := B) (i := B.length - 1 - idx) (j := j) hj
        by_cases hjlt : j < B.length - 1 - idx
        · simp only [heq, hjlt, ↓reduceDIte] at hnone ⊢
          exact hgood.coreNotDiv j (by omega) hnone
        · simp only [heq, hjlt, ↓reduceDIte] at hnone ⊢
          exact hgood.coreNotDiv (j + 1) (by rw [hlen_erase] at hj; omega) hnone
      · intro hidx_next hfr_next p hhard
        have hreach_post : S2Reach labeled (B.eraseIdx (B.length - 1 - idx)) idx
            (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) :=
          S2Reach.erase (start := labeled) (B := B) (idx := idx)
            (actualIdx := B.length - 1 - idx) (rec := rec) (by omega) rfl hfr hgood.reach
        have hsupp_post := htraj _ _ _ hreach_post
        exact s2_no_hard_FR_after_easy_delete hgood hidx hfr hsupp_post
          hidx_next hfr_next p hhard
  have hskip_geom : ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
      S2Good (easyMS labeled) labeled B idx rec →
        FrontierFRImpliesEasy B (idx + 1) := by
    intro B idx rec hidx hfr hgood
    apply frontierFRImpliesEasy_of_noHard
    · exact hgood.coreNotDiv
    · intro hidx_next hfr_next p hhard
      have hsupp_B := htraj B idx rec hgood.reach
      exact s2_no_hard_FR_at_next_after_skip hgood hidx hfr hsupp_B
        hidx_next hfr_next p hhard
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: delete branch P1 ∧ P2
    intro B idx rec hidx hfr hgood
    refine ⟨?_, ?_⟩
    · exact s2_post_delete_easy_FR hgood hidx hfr
        (hbridge_traj B idx rec hgood.reach hidx hfr)
    · intro hidx_erased hfr_erased p hhard
      have hreach_post : S2Reach labeled (B.eraseIdx (B.length - 1 - idx)) idx
          (rec ++ [(forget B)[B.length - 1 - idx]! / 3]) :=
        S2Reach.erase (start := labeled) (B := B) (idx := idx)
          (actualIdx := B.length - 1 - idx) (rec := rec) (by omega) rfl hfr hgood.reach
      have hsupp_post := htraj _ _ _ hreach_post
      exact s2_no_hard_FR_after_easy_delete hgood hidx hfr hsupp_post
        hidx_erased hfr_erased p hhard
  · -- Part 2: skip branch P3
    intro B idx rec hidx hfr hgood
    have hsupp_B := htraj B idx rec hgood.reach
    exact s2_no_hard_FR_at_next_after_skip hgood hidx hfr hsupp_B
  · -- Part 3: terminal — easyLabels afterS2L = []
    have hgood0 : S2Good (easyMS labeled) labeled labeled 0 [] :=
      s2Good_initial_processInsertionsLabeled A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
    have hfuel : (forget labeled).length + 1 ≥ labeled.length - 0 := by
      simp [length_forget]
    obtain ⟨idx_final, hgood_terminal, hidx_final⟩ :=
      S2Good_at_terminal_of_S2Good_geometric hdelete_geom hskip_geom
        ((forget labeled).length + 1) labeled 0 [] hgood0 hfuel
    exact easyLabels_eq_nil_of_noEasyInCheckedSuffix
      hgood_terminal.noEasyChecked hidx_final

private lemma process_no_bad_easy_bridge
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        ∀ (j : ℕ) (hj : j < (B.eraseIdx (B.length - 1 - idx)).length),
          j < (B.eraseIdx (B.length - 1 - idx)).length - idx →
          ((B.eraseIdx (B.length - 1 - idx))[j]'hj).origin.map Prod.snd =
            some InsertionKind.easy →
          isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx))) j = true := by
  -- Process-specific bridge invariant. It rules out configurations like
  -- `[5,3,3,2]` where deleting a lower flat-removable multiple destroys
  -- flat-removability of an upper one. Such configurations satisfy local
  -- FR facts but do not arise along the valid Andrews-Dhar insertion/S2
  -- trajectory.
  intro labeled B idx rec hidx hfr hgood
  exact (s2_process_history_safe A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos).1
    B idx rec hidx hfr hgood |>.1

private lemma allRemainingEasyFR_delete_process
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx := by
  intro labeled B idx rec hidx hfr hgood
  exact process_no_bad_easy_bridge A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
    B idx rec hidx hfr hgood

private lemma s2Good_noHard_frontier_process
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    (∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        ∀ (hidx_erased : idx < (B.eraseIdx (B.length - 1 - idx)).length)
          (hfr_erased : isFlatRemovableBool (forget (B.eraseIdx (B.length - 1 - idx)))
            ((B.eraseIdx (B.length - 1 - idx)).length - 1 - idx) = true)
          (p : ℕ),
          ((B.eraseIdx (B.length - 1 - idx))[
            (B.eraseIdx (B.length - 1 - idx)).length - 1 - idx]'(by omega)).origin =
              some (p, InsertionKind.hard) → False) ∧
    (∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
      S2Good (easyMS labeled) labeled B idx rec →
        ∀ (hidx_next : idx + 1 < B.length)
          (hfr_next : isFlatRemovableBool (forget B) (B.length - 1 - (idx + 1)) = true)
          (p : ℕ),
          (B[B.length - 1 - (idx + 1)]'(by omega)).origin =
            some (p, InsertionKind.hard) → False) := by
  -- The hard case of S2 geometry: a valid S2 trajectory cannot expose a
  -- hard-labeled flat-removable frontier after delete or skip.
  intro labeled
  constructor
  · intro B idx rec hidx hfr hgood
    exact (s2_process_history_safe A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos).1
      B idx rec hidx hfr hgood |>.2
  · intro B idx rec hidx hfr hgood
    exact (s2_process_history_safe A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos).2.1
      B idx rec hidx hfr hgood

private lemma frontierFRImpliesEasy_delete_process
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx := by
  intro labeled B idx rec hidx hfr hgood
  apply frontierFRImpliesEasy_of_noHard
  · intro j hj hnone
    have hact : B.length - 1 - idx < B.length := by omega
    have hlen_erase : (B.eraseIdx (B.length - 1 - idx)).length = B.length - 1 :=
      List.length_eraseIdx_of_lt hact
    have heq := List.getElem_eraseIdx (l := B) (i := B.length - 1 - idx) (j := j) hj
    by_cases hjlt : j < B.length - 1 - idx
    · simp only [heq, hjlt, ↓reduceDIte] at hnone ⊢
      exact hgood.coreNotDiv j (by omega) hnone
    · simp only [heq, hjlt, ↓reduceDIte] at hnone ⊢
      exact hgood.coreNotDiv (j + 1) (by rw [hlen_erase] at hj; omega) hnone
  · exact (s2Good_noHard_frontier_process
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos).1 B idx rec hidx hfr hgood

private lemma frontierFRImpliesEasy_skip_process
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    ∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
      S2Good (easyMS labeled) labeled B idx rec →
        FrontierFRImpliesEasy B (idx + 1) := by
  intro labeled B idx rec hidx hfr hgood
  apply frontierFRImpliesEasy_of_noHard
  · exact hgood.coreNotDiv
  · exact (s2Good_noHard_frontier_process
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos).2 B idx rec hidx hfr hgood

private lemma s2Good_geometric_transitions_process
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    (∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = true),
      S2Good (easyMS labeled) labeled B idx rec →
        NoEasyInCheckedSuffix (B.eraseIdx (B.length - 1 - idx)) idx ∧
        AllRemainingEasyFR (B.eraseIdx (B.length - 1 - idx)) idx ∧
        FrontierFRImpliesEasy (B.eraseIdx (B.length - 1 - idx)) idx) ∧
    (∀ (B : List Labeled) (idx : ℕ) (rec : List ℕ)
      (hidx : ¬ idx ≥ B.length)
      (hfr : isFlatRemovableBool (forget B) (B.length - 1 - idx) = false),
      S2Good (easyMS labeled) labeled B idx rec →
        FrontierFRImpliesEasy B (idx + 1)) := by
  intro labeled
  constructor
  · intro B idx rec hidx hfr hgood
    refine ⟨noEasyInCheckedSuffix_delete hgood.noEasyChecked hidx, ?_, ?_⟩
    · exact allRemainingEasyFR_delete_process
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos B idx rec hidx hfr hgood
    · exact frontierFRImpliesEasy_delete_process
        A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos B idx rec hidx hfr hgood
  · intro B idx rec hidx hfr hgood
    exact frontierFRImpliesEasy_skip_process
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos B idx rec hidx hfr hgood

private lemma hardLabels_scanFromSmallestLabeled_eq_process
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    hardLabels (scanFromSmallestLabeled (forget labeled).length.succ labeled 0 []).1 =
      hardLabels labeled := by
  intro labeled
  have hgeom := s2Good_geometric_transitions_process
    A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hgood0 : S2Good (easyMS labeled) labeled labeled 0 [] :=
    s2Good_initial_processInsertionsLabeled A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  exact hardLabels_scanFromSmallestLabeled_eq_of_S2Good_geometric
    hgeom.1 hgeom.2 (forget labeled).length.succ labeled 0 [] hgood0

lemma s2_labeled_scan_records_perm_easyLabels
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat   : IsThreeFlat (forget A_init))
    (hA_reg    : IsThreeRegular (forget A_init))
    (hA_clean  : ∀ x ∈ A_init, x.origin = none)
    (hν_sort   : ν.Pairwise (· ≥ ·))
    (hν_pos    : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    (scanFromSmallestLabeled (forget labeled).length.succ labeled 0 []).2.Perm
      (easyLabels labeled) := by
  have hgeom := s2Good_geometric_transitions_process
    A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  exact s2_labeled_scan_records_perm_easyLabels_of_geometric
    A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos hgeom.1 hgeom.2
lemma s2_extracts_easy_labels
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat   : IsThreeFlat (forget A_init))
    (hA_reg    : IsThreeRegular (forget A_init))
    (hA_clean  : ∀ x ∈ A_init, x.origin = none)
    (hν_sort   : ν.Pairwise (· ≥ ·))
    (hν_pos    : ∀ x ∈ ν, 0 < x) :
    let labeled  := processInsertionsLabeled ν A_init
    let unl      := forget labeled
    (scanFromSmallest (unl.length + 1) unl 0 []).2.mergeSort (· ≥ ·) =
      (easyLabels labeled).mergeSort (· ≥ ·) := by
  -- Step 1: Use forget_scanFromSmallestLabeled to relate unlabeled to labeled scan
  set labeled := processInsertionsLabeled ν A_init with labeled_def
  set unl := forget labeled with unl_def
  -- Step 2: The labeled scan records are a permutation of easyLabels
  have hperm := s2_labeled_scan_records_perm_easyLabels A_init ν
    hA_flat hA_reg hA_clean hν_sort hν_pos
  -- hperm : (scanFromSmallestLabeled (forget labeled).length.succ labeled 0 []).2.Perm (easyLabels labeled)
  -- Step 3: Connect labeled scan record to unlabeled scan record
  have hcomm := forget_scanFromSmallestLabeled (forget labeled).length.succ labeled 0 []
  have hrec_eq : (scanFromSmallestLabeled (forget labeled).length.succ labeled 0 []).2 =
      (scanFromSmallest (forget labeled).length.succ (forget labeled) 0 []).2 := by
    exact hcomm.2
  -- Step 4: Show (unl.length + 1) = (forget labeled).length.succ
  have hlen_eq : unl.length + 1 = (forget labeled).length.succ := by simp [unl_def]
  -- Step 5: Combine to get the permutation for unlabeled scan
  have hperm_unl : (scanFromSmallest (unl.length + 1) unl 0 []).2.Perm (easyLabels labeled) := by
    rw [hlen_eq, unl_def]
    exact hrec_eq ▸ hperm
  -- Step 6: mergeSort of permutations are equal
  have htrans : ∀ (a b c : ℕ), decide (a ≥ b) = true → decide (b ≥ c) = true →
      decide (a ≥ c) = true := by simp; omega
  have htotal : ∀ (a b : ℕ), (decide (a ≥ b) || decide (b ≥ a)) = true := by simp; omega
  have h1 := List.pairwise_mergeSort htrans htotal
    (scanFromSmallest (unl.length + 1) unl 0 []).2
  have h2 := List.pairwise_mergeSort htrans htotal (easyLabels labeled)
  have hperm' : ((scanFromSmallest (unl.length + 1) unl 0 []).2.mergeSort (· ≥ ·)).Perm
      ((easyLabels labeled).mergeSort (· ≥ ·)) :=
    (List.mergeSort_perm _ _).trans (hperm_unl.trans (List.mergeSort_perm _ _).symm)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by simp at *; omega) h1 h2 hperm'

/-! S3 rank invariant interface. -/

/-- `corePrefixAbove A (k+1) = corePrefixAbove A k` when `A[k]` is not core. -/

private lemma corePrefixAbove_succ_of_prefixCore
    {A : List Labeled} {idx : ℕ}
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none)
    (hi : idx + 1 < A.length)
    (hidx_core : (A[idx]'(by omega)).origin = none) :
    corePrefixAbove A (idx + 1) = idx + 1 := by
  unfold corePrefixAbove
  have hall : ∀ x ∈ A.take (idx + 1), (fun y : Labeled => decide (y.origin = none)) x = true := by
    intro x hx
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
    have hlen_take : (A.take (idx + 1)).length = idx + 1 := by
      rw [List.length_take]
      simp [Nat.min_eq_left (by omega : idx + 1 ≤ A.length)]
    have hj_bound : j < idx + 1 := by omega
    have hA_j : j < A.length := by
      rw [hlen_take] at hj
      omega
    have hgetA : (A.take (idx + 1))[j]'hj = A[j]'hA_j := by
      rw [List.getElem_take]
    have hx_eq : x = A[j]'hA_j := by
      rw [← hget, hgetA]
    rw [hx_eq]
    by_cases hjidx : j < idx
    · simp [hprefix j hA_j hjidx]
    · have hjeq : j = idx := by omega
      subst hjeq
      simp [hidx_core]
  rw [countP_eq_length_of_all (fun y : Labeled => decide (y.origin = none)) (A.take (idx + 1)) hall]
  rw [List.length_take]
  omega

/-- Pure structural fact: `scanFromSmallestLabeled` produces a sublist of its
input.  The scan only ever erases elements (when the bottom-up frontier is
flat-removable), never inserts or modifies them. -/
private lemma scanFromSmallestLabeled_sublist (fuel : ℕ) (A : List Labeled)
    (idx : ℕ) (rec : List ℕ) :
    List.Sublist (scanFromSmallestLabeled fuel A idx rec).1 A := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromSmallestLabeled]
  | succ fuel' ih =>
    simp only [scanFromSmallestLabeled]
    split
    · exact List.Sublist.refl A
    · split
      · exact (ih (A.eraseIdx (A.length - 1 - idx)) idx _).trans
          (List.eraseIdx_sublist A _)
      · exact ih A (idx + 1) rec

private lemma origin_none_not_div3_afterS2
    (A_init : List Labeled) (ν : List ℕ)
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    ∀ (i' : ℕ) (hi' : i' < afterS2L.length),
      (afterS2L[i']'hi').origin = none →
      (afterS2L[i']'hi').value % 3 ≠ 0 := by
  intro labeled unl s2L_pair afterS2L i' hi' hnone
  have hsub : List.Sublist afterS2L labeled :=
    scanFromSmallestLabeled_sublist _ labeled 0 []
  have hmem_after : (afterS2L[i']'hi') ∈ afterS2L := List.getElem_mem hi'
  have hmem_lab : (afterS2L[i']'hi') ∈ labeled := hsub.mem hmem_after
  obtain ⟨j, hj, hjeq⟩ : ∃ j, ∃ hj : j < labeled.length,
      labeled[j] = (afterS2L[i']'hi') := by
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem_lab
    exact ⟨j, hj, hjeq⟩
  have hnone_lab : (labeled[j]'hj).origin = none := by
    rw [hjeq]
    exact hnone
  have hnot := processInsertionsLabeled_origin_none_not_div3
    A_init ν hA_reg hA_clean j hj hnone_lab
  intro hmod
  apply hnot
  have hval_eq : (labeled[j]'hj).value = (afterS2L[i']'hi').value := by
    rw [hjeq]
  rw [hval_eq]
  exact hmod

private lemma hard_origin_positive_afterS2
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    ∀ (i' : ℕ) (hi' : i' < afterS2L.length) p,
      (afterS2L[i']'hi').origin = some (p, .hard) →
      0 < (afterS2L[i']'hi').value := by
  intro labeled unl s2L_pair afterS2L i' hi' p hhard
  have hsub : List.Sublist afterS2L labeled :=
    scanFromSmallestLabeled_sublist _ labeled 0 []
  have hmem_after : (afterS2L[i']'hi') ∈ afterS2L := List.getElem_mem hi'
  have hmem_lab : (afterS2L[i']'hi') ∈ labeled := hsub.mem hmem_after
  have hflat_labeled : IsThreeFlat (forget labeled) := by
    rw [show labeled = processInsertionsLabeled ν A_init from rfl]
    rw [forget_processInsertionsLabeled]
    suffices h : ∀ (parts : List ℕ) (B : List ℕ), IsThreeFlat B →
        IsThreeFlat (processInsertions parts B) from h ν _ hA_flat
    intro parts
    induction parts with
    | nil => intro B hB; exact hB
    | cons p rest ih =>
      intro B hB
      simp only [processInsertions]
      exact ih _ (performInsertion_preserves_flat' B p hB)
  have hmem_value : (afterS2L[i']'hi').value ∈ forget labeled := by
    simpa [forget, List.mem_map] using ⟨afterS2L[i']'hi', hmem_lab, rfl⟩
  exact hflat_labeled.1.2 _ hmem_value

/-- The trajectory rank invariant on `processInsertionsLabeled ν A_init`.
By induction on ν, every hard label in the result has a `HardRankAtS3` witness.
The strengthened induction also carries `easyValue` and `sizeBound`. -/
private lemma processInsertionsLabeled_hardRankS3Inv
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    ProcessHardRankS3Inv (processInsertionsLabeled ν A_init) := by
  suffices hsuff : ∀ (A : List Labeled) (ν' : List ℕ)
      (hflat : IsThreeFlat (forget A))
      (_hνsort : ν'.Pairwise (· ≥ ·))
      (hRank : ProcessHardRankS3Inv A)
      (hEasy : ∀ (i : ℕ) (hi : i < A.length) (r : ℕ),
        (A[i]'hi).origin = some (r, InsertionKind.easy) → (A[i]'hi).value = 3 * r)
      (hBound : ∀ (i : ℕ) (hi : i < A.length) (r : ℕ) (k : InsertionKind),
        (A[i]'hi).origin = some (r, k) → ∀ s ∈ ν', r ≥ s),
      ProcessHardRankS3Inv (processInsertionsLabeled ν' A) by
    apply hsuff A_init ν hA_flat hν_sort
    · -- hRank: A_init is all-core, vacuous.
      intro i hi p hhard
      have hmem := List.getElem_mem hi
      exact absurd hhard (by rw [hA_clean _ hmem]; simp)
    · -- hEasy: vacuous.
      intro i hi r hr
      have hmem := List.getElem_mem hi
      exact absurd hr (by rw [hA_clean _ hmem]; simp)
    · -- hBound: vacuous.
      intro i hi r k hr s _hs
      have hmem := List.getElem_mem hi
      exact absurd hr (by rw [hA_clean _ hmem]; simp)
  intro A ν' hflat hνsort hRank hEasy hBound
  induction ν' generalizing A with
  | nil =>
    simp only [processInsertionsLabeled]
    exact hRank
  | cons q rest ih =>
    simp only [processInsertionsLabeled]
    have hν_rest : rest.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hνsort).2
    have hq_ge_rest : ∀ s ∈ rest, q ≥ s := (List.pairwise_cons.mp hνsort).1
    have hflat' : IsThreeFlat (forget (performInsertionLabeled A q)) := by
      rw [forget_performInsertionLabeled]
      exact performInsertion_preserves_flat' (forget A) q hflat
    -- The three preservation sub-goals.
    have hBound_q : ∀ (i : ℕ) (hi : i < A.length) (r : ℕ) (k : InsertionKind),
        (A[i]'hi).origin = some (r, k) → r ≥ q := by
      intro i hi r k hr; exact hBound i hi r k hr q (List.mem_cons_self)
    have hRank' : ProcessHardRankS3Inv (performInsertionLabeled A q) := by
      unfold performInsertionLabeled
      cases hf : findHardInsertionLabeled A q with
      | some r_hard =>
        -- Hard insertion: use the findHardInsertion.induct + tryHardInsertionLabeled_preserves
        have hpreserve_hard : ∀ (h₀ : ℕ) (result : List Labeled),
            findHardInsertionLabeled A q h₀ = some result →
            ProcessHardRankS3Inv result := by
          intro h₀
          induction h₀ using findHardInsertionLabeled.induct A q with
          | case1 h hguard =>
            intro result hfind
            unfold findHardInsertionLabeled at hfind
            simp [hguard] at hfind
          | case2 h hguard r_h htry =>
            intro result hfind
            unfold findHardInsertionLabeled at hfind
            simp [hguard, htry] at hfind
            subst hfind
            exact tryHardInsertionLabeled_preserves_hardRankS3Inv hflat hRank hEasy hBound_q htry
          | case3 h hguard htry_fail ih =>
            intro result hfind
            unfold findHardInsertionLabeled at hfind
            simp [hguard, htry_fail] at hfind
            exact ih result hfind
        exact hpreserve_hard 0 r_hard hf
      | none =>
        cases he : tryEasyInsertionLabeled A q with
        | some r_easy => exact tryEasyInsertionLabeled_preserves_hardRankS3Inv hRank he
        | none => exact hRank
    have hEasy' : ∀ (i : ℕ) (hi : i < (performInsertionLabeled A q).length) (r : ℕ),
        ((performInsertionLabeled A q)[i]'hi).origin = some (r, InsertionKind.easy) →
        ((performInsertionLabeled A q)[i]'hi).value = 3 * r := by
      -- Adapts processInsertionsLabeled_easy_value_eq's hinv'_hard_aux + hinv'_easy_aux
      -- combined per-step preservation logic for value = 3*r.
      have hinv'_hard_aux : ∀ (h₀ : ℕ) (result : List Labeled),
          findHardInsertionLabeled A q h₀ = some result →
          ∀ (i : ℕ) (hi : i < result.length) (r : ℕ),
            (result[i]'hi).origin = some (r, InsertionKind.easy) →
            (result[i]'hi).value = 3 * r := by
        intro h₀
        induction h₀ using findHardInsertionLabeled.induct A q with
        | case1 h hguard =>
          intro result hfind i hi r horg_i
          unfold findHardInsertionLabeled at hfind
          simp [hguard] at hfind
        | case2 h hguard r_h htry =>
          intro result hfind i hi r horg_i
          unfold findHardInsertionLabeled at hfind
          simp [hguard, htry] at hfind
          subst hfind
          have horg_easy : (r_h[i]'hi).origin.map Prod.snd =
              some InsertionKind.easy := by rw [horg_i]; rfl
          obtain ⟨j, hj, hi_eq, h_origin⟩ :=
            tryHardInsertionLabeled_easy_pos_pullback A q h r_h htry i hi horg_easy
          have horg_A : (A[j]'hj).origin = some (r, InsertionKind.easy) := by
            rw [h_origin]; exact horg_i
          have hval_A : (A[j]'hj).value = 3 * r := hEasy j hj r horg_A
          have hr_ge_q : r ≥ q := hBound j hj r .easy horg_A q (List.mem_cons_self)
          have htry_orig : tryHardInsertionLabeled A q h = some r_h := htry
          unfold tryHardInsertionLabeled at htry
          simp only [ge_iff_le, Bool.and_eq_true, Bool.not_eq_true'] at htry
          split_ifs at htry with hfail hadm
          push_neg at hfail
          obtain ⟨hh_q, hh_A⟩ := hfail
          set newPart : Labeled := ⟨3 * (q - h), some (q, .hard)⟩ with hnewPart_def
          set raised : List Labeled :=
            A.zipIdx.map (fun x : Labeled × ℕ =>
              if x.2 < h then { value := x.1.value + 3, origin := x.1.origin } else x.1)
            with hraised_def
          have hres : raised.insertIdx h newPart = r_h := Option.some.inj htry
          have hlen_raised : raised.length = A.length := by simp [hraised_def]
          have hraised_get : ∀ k (hk : k < A.length),
              raised[k]'(hlen_raised.symm ▸ hk) =
                if k < h then { value := (A[k]'hk).value + 3, origin := (A[k]'hk).origin }
                else (A[k]'hk) := by
            intro k hk
            simp [hraised_def, List.getElem_map, List.getElem_zipIdx]
          by_cases hjh : j < h
          · exfalso
            have hh_pos : h ≥ 1 := by omega
            have hforget := forget_tryHardInsertionLabeled A q h
            rw [htry_orig] at hforget
            have h_unl_some : tryHardInsertion (forget A) q h = some (forget r_h) := by
              simp only [Option.map_some] at hforget; exact hforget.symm
            have h_unl_isSome : (tryHardInsertion (forget A) q h).isSome := by
              rw [h_unl_some]; rfl
            have hh_le_forget : h ≤ (forget A).length := by
              rw [length_forget]; exact hh_A
            have hub := tryHardInsertion_upper_bound_early h_unl_isSome hh_pos hh_le_forget
            have hh1_lt_A : h - 1 < A.length := by omega
            have hub' : (A[h-1]'hh1_lt_A).value < 3 * q - 3 * h := by
              have hf : (forget A)[h-1]'(by rw [length_forget]; exact hh1_lt_A) =
                  (A[h-1]'hh1_lt_A).value := by simp [forget, List.getElem_map]
              rw [← hf]; exact hub
            have hdesc := threeFlat_descent_bound_early hflat (show j ≤ h - 1 by omega)
              (by rw [length_forget]; exact hh1_lt_A)
            have hdesc' : (A[j]'hj).value ≤ (A[h-1]'hh1_lt_A).value + 2 * (h - 1 - j) := by
              have hf1 : (forget A)[j]'(by rw [length_forget]; exact hj) =
                  (A[j]'hj).value := by simp [forget, List.getElem_map]
              have hf2 : (forget A)[h-1]'(by rw [length_forget]; exact hh1_lt_A) =
                  (A[h-1]'hh1_lt_A).value := by simp [forget, List.getElem_map]
              rw [hf1, hf2] at hdesc; exact hdesc
            omega
          · push_neg at hjh
            have hi_val : i = j + 1 := by
              have hjh_not : ¬ j < h := Nat.not_lt.mpr hjh
              simp [hjh_not] at hi_eq; exact hi_eq
            have hi_ins : i < (raised.insertIdx h newPart).length := by
              rw [List.length_insertIdx]; simp [hlen_raised, hh_A]; omega
            have keyAll : r_h[i]'hi = (raised.insertIdx h newPart)[i]'hi_ins := by
              congr 1; exact hres.symm
            rw [keyAll]
            rw [List.getElem_insertIdx]
            have hnotlt : ¬ (i < h) := by omega
            have hnoteq : i ≠ h := by omega
            rw [dif_neg hnotlt, dif_neg hnoteq]
            have hi_minus_lt : i - 1 < A.length := by rw [hi_val]; omega
            have hi_minus_eq : i - 1 = j := by omega
            have hi_minus_not_lt : ¬ (i - 1 < h) := by omega
            have hri := hraised_get (i - 1) hi_minus_lt
            rw [if_neg hi_minus_not_lt] at hri
            rw [hri]
            have hAget : (A[i - 1]'hi_minus_lt) = (A[j]'hj) := by congr 1
            rw [hAget]; exact hval_A
        | case3 h hguard htry_fail ih =>
          intro result hfind i hi r horg_i
          unfold findHardInsertionLabeled at hfind
          simp [hguard, htry_fail] at hfind
          exact ih result hfind i hi r horg_i
      have hinv'_easy_aux : ∀ (result : List Labeled),
          tryEasyInsertionLabeled A q = some result →
          ∀ (i : ℕ) (hi : i < result.length) (r : ℕ),
            (result[i]'hi).origin = some (r, InsertionKind.easy) →
            (result[i]'hi).value = 3 * r := by
        intro result he i hi r horg_i
        unfold tryEasyInsertionLabeled at he
        simp only at he
        split_ifs at he with hcond
        set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
        set pos := (A.takeWhile (·.value ≥ 3 * q)).length
        have hres : A.insertIdx pos newPart = result := Option.some.inj he
        have hpos_le : pos ≤ A.length :=
          List.IsPrefix.length_le (List.takeWhile_prefix _)
        have hlen_r : result.length = A.length + 1 := by
          rw [← hres, List.length_insertIdx]; simp [hpos_le]
        subst hres
        rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
        · have hpre : i < A.length := by omega
          have horig := Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
          rw [horig] at horg_i
          have hval := hEasy i hpre r horg_i
          rw [List.getElem_insertIdx]; simp [hlt]; exact hval
        · subst heq
          have horig := Hints.origin_insertIdx_at A pos newPart hi
          rw [horig] at horg_i
          simp [newPart] at horg_i
          rw [List.getElem_insertIdx]
          simp [newPart, ← horg_i]
        · have hpre : i - 1 < A.length := by rw [hlen_r] at hi; omega
          have horig := Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
          rw [horig] at horg_i
          have hval := hEasy (i - 1) hpre r horg_i
          rw [List.getElem_insertIdx]
          have hnotlt : ¬ (i < pos) := by omega
          have hnoteq : i ≠ pos := by omega
          simp [hnotlt, hnoteq]; exact hval
      unfold performInsertionLabeled
      split
      · next r_hard hf => exact hinv'_hard_aux 0 r_hard hf
      · split
        · next r_easy he => exact hinv'_easy_aux r_easy he
        · exact hEasy
    have hBound' : ∀ (i : ℕ) (hi : i < (performInsertionLabeled A q).length) (r : ℕ)
        (k : InsertionKind),
        ((performInsertionLabeled A q)[i]'hi).origin = some (r, k) →
        ∀ s ∈ rest, r ≥ s := by
      unfold performInsertionLabeled
      cases hf : findHardInsertionLabeled A q with
      | some r_hard =>
        have hbound_hard : ∀ (h₀ : ℕ) (result : List Labeled),
            findHardInsertionLabeled A q h₀ = some result →
            ∀ (i : ℕ) (hi : i < result.length) (p : ℕ) (k : InsertionKind),
              (result[i]'hi).origin = some (p, k) →
              ∀ s ∈ rest, p ≥ s := by
          intro h₀
          induction h₀ using findHardInsertionLabeled.induct A q with
          | case1 h hguard =>
            intro result hfind i hi p k horg s hs_rest
            unfold findHardInsertionLabeled at hfind
            simp [hguard] at hfind
          | case2 h hguard r_h htry =>
            intro result hfind i hi p k horg s hs_rest
            unfold findHardInsertionLabeled at hfind
            simp [hguard, htry] at hfind
            subst hfind
            cases k with
            | hard =>
              obtain h1 | h2 := tryHardInsertionLabeled_hard_pos_pullback A q h r_h
                htry i hi p horg
              · obtain ⟨_, hp_eq, _⟩ := h1
                rw [hp_eq]; exact hq_ge_rest s hs_rest
              · obtain ⟨j, hj, _, hjorig, _⟩ := h2
                exact hBound j hj p InsertionKind.hard
                  hjorig s (List.mem_cons_of_mem q hs_rest)
            | easy =>
              have horg_easy : (r_h[i]'hi).origin.map Prod.snd =
                  some InsertionKind.easy := by rw [horg]; rfl
              obtain ⟨j, hj, _, h_origin⟩ := tryHardInsertionLabeled_easy_pos_pullback A q h
                r_h htry i hi horg_easy
              have horg_A : (A[j]'hj).origin = some (p, InsertionKind.easy) := by
                rw [h_origin]; exact horg
              exact hBound j hj p InsertionKind.easy
                horg_A s (List.mem_cons_of_mem q hs_rest)
          | case3 h hguard htry_fail ih =>
            intro result hfind i hi p k horg s hs_rest
            unfold findHardInsertionLabeled at hfind
            simp [hguard, htry_fail] at hfind
            exact ih result hfind i hi p k horg s hs_rest
        intro i hi p k horg s hs_rest
        exact hbound_hard 0 r_hard hf i hi p k horg s hs_rest
      | none =>
        cases he : tryEasyInsertionLabeled A q with
        | some r_easy =>
          intro i hi p k horg s hs_rest
          unfold tryEasyInsertionLabeled at he
          simp only at he
          split_ifs at he with hcond
          set newPart : Labeled := ⟨3 * q, some (q, InsertionKind.easy)⟩
          set pos := (A.takeWhile (·.value ≥ 3 * q)).length
          have hres : A.insertIdx pos newPart = r_easy := Option.some.inj he
          have hpos_le : pos ≤ A.length :=
            List.IsPrefix.length_le (List.takeWhile_prefix _)
          have hlen_r : r_easy.length = A.length + 1 := by
            rw [← hres, List.length_insertIdx]; simp [hpos_le]
          subst hres
          rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
          · have hpre : i < A.length := by omega
            have horig :=
              Hints.origin_insertIdx_of_lt A pos i newPart hi hpre hlt
            rw [horig] at horg
            exact hBound i hpre p k horg s (List.mem_cons_of_mem q hs_rest)
          · subst heq
            have horig := Hints.origin_insertIdx_at A pos newPart hi
            rw [horig] at horg
            simp [newPart] at horg
            obtain ⟨hp, _⟩ := horg
            rw [← hp]; exact hq_ge_rest s hs_rest
          · have hpre : i - 1 < A.length := by rw [hlen_r] at hi; omega
            have horig :=
              Hints.origin_insertIdx_of_gt A pos i newPart hi hpre hgt
            rw [horig] at horg
            exact hBound (i - 1) hpre p k horg s (List.mem_cons_of_mem q hs_rest)
        | none =>
          intro i hi p k horg s hs_rest
          exact hBound i hi p k horg s (List.mem_cons_of_mem q hs_rest)
    exact ih _ hflat' hν_rest hRank' hEasy' hBound'

private lemma hard_rank_s3_at_post_s2
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    ∀ (i' : ℕ) (hi' : i' < afterS2L.length) p,
      (afterS2L[i']'hi').origin = some (p, .hard) →
      HardRankAtS3 afterS2L i' p := by
  intro labeled unl s2L_pair afterS2L i' hi' p hhard
  -- Get ProcessHardRankS3Inv on the pre-S2 state.
  have hInv : ProcessHardRankS3Inv labeled :=
    processInsertionsLabeled_hardRankS3Inv A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  -- Get coreNotDiv on the pre-S2 state (already proven).
  have hCore : ∀ (j : ℕ) (hj : j < labeled.length),
      (labeled[j]'hj).origin = none → (labeled[j]'hj).value % 3 ≠ 0 := by
    intro j hj horg
    exact processInsertionsLabeled_origin_none_not_div3
      A_init ν hA_reg hA_clean j hj horg
  -- Transport through the S2 scan via the closed scan-chain lemma.
  exact processHardRankS3Inv_scanFromSmallestLabeled
    (unl.length + 1) labeled 0 [] hInv hCore i' hi' p hhard

/-! Bridge 4 sub-decomposition. -/

/-- Dynamic invariant for the labeled S3 scan.

The `coreNotFire` field is strictly weaker than `value % 3 ≠ 0`: it rules out
the S3 firing condition at core-origin positions.  This is preserved by the
S3 delete-and-lower-prefix transform (in `ℕ`, a value `1` or `2` becomes `0`
after `-3`, where `0 < 0` fails, so the firing conjunction fails).  The
stronger `value % 3 ≠ 0` is **not** preserved by this transform. -/
private structure S3Good
    (start : List Labeled) (rec0 : List ℕ)
    (A : List Labeled) (idx : ℕ) (rec : List ℕ) : Prop where
  rec_prefix : ∃ added, rec = rec0 ++ added
  ms_account : deltaRecMS rec rec0 + hardMS A = hardMS start
  noEasy : easyLabels A = []
  coreNotFire : ∀ (i : ℕ) (hi : i < A.length),
    (A[i]'hi).origin = none →
      ¬ ((A[i]'hi).value % 3 = 0 ∧ 0 < (A[i]'hi).value)
  hardRank : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
    (A[i]'hi).origin = some (p, .hard) → HardRankAtS3 A i p
  hardPositive : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
    (A[i]'hi).origin = some (p, .hard) → 0 < (A[i]'hi).value
  prefixRank : ∀ (hi : idx < A.length), corePrefixAbove A idx = idx
  prefixCore : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none

private lemma hardLabels_eq_nil_of_prefixCore_terminal
    {A : List Labeled} {idx : ℕ}
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none)
    (hidx : idx ≥ A.length) :
    hardLabels A = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro x hx
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
  subst hget
  have hnone := hprefix j hj (by omega)
  simp [hardLabels, hnone]

private lemma no_easy_origin_of_easyLabels_eq_nil
    {A : List Labeled} (hnoEasy : easyLabels A = [])
    {i : ℕ} (hi : i < A.length) :
    (A[i]'hi).origin.map Prod.snd ≠ some InsertionKind.easy := by
  intro heasy
  have hmem : (A[i]'hi) ∈ A := List.getElem_mem hi
  have hsome : Option.isSome
      ((fun x : Labeled => match x.origin with
        | some (p, .easy) => some p
        | _ => none) (A[i]'hi)) := by
    cases horig : (A[i]'hi).origin with
    | none => simp [horig] at heasy
    | some pr =>
        cases pr with
        | mk p kind =>
            cases kind
            · simp [horig]
            · simp [horig] at heasy
  have hnil := List.filterMap_eq_nil_iff.mp (by
    unfold easyLabels at hnoEasy
    exact hnoEasy)
  have := hnil (A[i]'hi) hmem
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨p, hp⟩ := hsome
  change (match (A[i]'hi).origin with
    | some (p, InsertionKind.easy) => some p
    | _ => none) = some p at hp
  rw [hp] at this
  simp at this

private lemma s3Good_terminal_deltaRecMS
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hgood : S3Good start rec0 A idx rec)
    (hidx : idx ≥ A.length) :
    deltaRecMS rec rec0 = hardMS start := by
  have hhard_nil : hardLabels A = [] :=
    hardLabels_eq_nil_of_prefixCore_terminal hgood.prefixCore hidx
  simpa [hardMS, hhard_nil] using hgood.ms_account

private lemma s3Good_initial_of_facts
    (start : List Labeled) (rec0 : List ℕ)
    (hnoEasy : easyLabels start = [])
    (hcore : ∀ (i : ℕ) (hi : i < start.length),
      (start[i]'hi).origin = none → (start[i]'hi).value % 3 ≠ 0)
    (hrank : ∀ (i : ℕ) (hi : i < start.length) (p : ℕ),
      (start[i]'hi).origin = some (p, .hard) → HardRankAtS3 start i p)
    (hhardPos : ∀ (i : ℕ) (hi : i < start.length) (p : ℕ),
      (start[i]'hi).origin = some (p, .hard) → 0 < (start[i]'hi).value) :
    S3Good start rec0 start 0 rec0 := by
  -- `coreNotFire` follows trivially from the stronger `value % 3 ≠ 0` (hcore):
  -- if the residue is non-zero, the firing condition (residue = 0 ∧ value > 0)
  -- cannot hold.
  refine ⟨?_, ?_, hnoEasy, ?_, hrank, hhardPos, ?_, ?_⟩
  · exact ⟨[], by simp⟩
  · simp [deltaRecMS, recMS]
  · intro i hi hnone hfire
    exact hcore i hi hnone hfire.1
  · intro hi
    unfold corePrefixAbove
    simp
  · intro j hj hlt
    omega

private lemma easyLabels_eq_nil_afterS2
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    easyLabels afterS2L = [] := by
  intro labeled unl s2L_pair afterS2L
  have hgeom := s2Good_geometric_transitions_process
    A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hgood0 : S2Good (easyMS labeled) labeled labeled 0 [] :=
    s2Good_initial_processInsertionsLabeled A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  set pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 ([] : List ℕ) with hpair
  have hgood_hard :
      hardLabels pair.1 = hardLabels labeled := by
    rw [hpair]
    have hlen : unl.length + 1 = (forget labeled).length.succ := by
      simp [unl]
    rw [hlen]
    exact hardLabels_scanFromSmallestLabeled_eq_of_S2Good_geometric
      hgeom.1 hgeom.2 (forget labeled).length.succ labeled 0 [] hgood0
  have hrec_ms :
      recMS pair.2 = easyMS labeled := by
    rw [hpair]
    have hlen : unl.length + 1 = (forget labeled).length.succ := by
      simp [unl]
    rw [hlen]
    have hfuel : (forget labeled).length.succ ≥ labeled.length - 0 := by
      simp [length_forget]
    exact recMS_scanFromSmallestLabeled_eq_target_of_S2Good_geometric
      hgeom.1 hgeom.2 (forget labeled).length.succ labeled 0 [] hgood0 hfuel
  exact (s2_process_history_safe A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos).2.2

private lemma s3Good_initial_postS2
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    let recS2L := s2L_pair.2
    S3Good afterS2L recS2L afterS2L 0 recS2L := by
  intro labeled unl s2L_pair afterS2L recS2L
  exact s3Good_initial_of_facts afterS2L recS2L
    (easyLabels_eq_nil_afterS2 A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos)
    (origin_none_not_div3_afterS2 A_init ν hA_reg hA_clean)
    (hard_rank_s3_at_post_s2 A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos)
    (hard_origin_positive_afterS2 A_init ν hA_flat hA_clean hν_sort hν_pos)

private lemma s3Good_skip_index_core
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hgood : S3Good start rec0 A idx rec)
    (hidx : ¬ idx ≥ A.length)
    (hfire : ¬ ((forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)) :
    (A[idx]'(by omega)).origin = none := by
  cases horig : (A[idx]'(by omega)).origin with
  | none => rfl
  | some pr =>
      cases pr with
      | mk p kind =>
          cases kind
          · exfalso
            have hi : idx < A.length := by omega
            have hno := no_easy_origin_of_easyLabels_eq_nil hgood.noEasy hi
            exact hno (by simpa [horig])
          · exfalso
            -- A hard label at an S3 position must be a positive multiple of 3,
            -- so the scan would fire. This is part of the dynamic rank invariant.
            have hi : idx < A.length := by omega
            have hpos := hgood.hardPositive idx hi p horig
            have hrank := hgood.hardRank idx hi p horig
            obtain ⟨_, _, hsum⟩ := hrank
            have hmod : (A[idx]'hi).value % 3 = 0 := by
              have hprefix := hgood.prefixRank hi
              rw [hprefix] at hsum
              have hv : (A[idx]'hi).value = 3 * (p - idx) := by
                omega
              rw [hv]
              exact Nat.mul_mod_right 3 (p - idx)
            apply hfire
            constructor
            · have hval_eq : (A[idx]'hi).value = (forget A)[idx]! := by
                have hlt : idx < (forget A).length := by simpa [length_forget] using hi
                rw [getElem!_pos (forget A) idx hlt]
                simp [forget, List.getElem_map]
              rwa [← hval_eq]
            · have hval_eq : (A[idx]'hi).value = (forget A)[idx]! := by
                have hlt : idx < (forget A).length := by simpa [length_forget] using hi
                rw [getElem!_pos (forget A) idx hlt]
                simp [forget, List.getElem_map]
              rwa [← hval_eq]

private lemma s3Good_firing_origin_hard
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hgood : S3Good start rec0 A idx rec)
    (hidx : ¬ idx ≥ A.length)
    (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!) :
    ∃ p, (A[idx]'(by omega)).origin = some (p, InsertionKind.hard) := by
  have hi : idx < A.length := by omega
  cases horig : (A[idx]'hi).origin with
  | none =>
      exfalso
      have hval_eq : (A[idx]'hi).value = (forget A)[idx]! := by
        have hlt : idx < (forget A).length := by simpa [length_forget] using hi
        rw [getElem!_pos (forget A) idx hlt]
        simp [forget, List.getElem_map]
      apply hgood.coreNotFire idx hi horig
      rw [hval_eq]
      exact hfire
  | some pr =>
      cases pr with
      | mk p kind =>
          cases kind
          · exfalso
            have hno := no_easy_origin_of_easyLabels_eq_nil hgood.noEasy hi
            exact hno (by simpa [horig])
          · refine ⟨p, ?_⟩
            simp [horig]

private lemma s3Good_delete_recPrefix
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hgood : S3Good start rec0 A idx rec) :
    ∃ added, rec ++ [(forget A)[idx]! / 3 + idx] = rec0 ++ added := by
  obtain ⟨added, hrec⟩ := hgood.rec_prefix
  subst hrec
  exact ⟨added ++ [(forget A)[idx]! / 3 + idx], by simp [List.append_assoc]⟩

private lemma s3Good_delete_noEasy
    {A : List Labeled} {idx : ℕ}
    (hnoEasy : easyLabels A = []) :
    easyLabels
      ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
        if j < idx then { x with value := x.value - 3 } else x)) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro x hx
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hx
  rcases pair with ⟨a, j⟩
  have ha_mem_erase : a ∈ A.eraseIdx idx := List.fst_mem_of_mem_zipIdx hpair
  have ha_mem : a ∈ A := List.mem_of_mem_eraseIdx ha_mem_erase
  have hnil := List.filterMap_eq_nil_iff.mp (by
    unfold easyLabels at hnoEasy
    exact hnoEasy)
  have ha_none := hnil a ha_mem
  by_cases hj : j < idx <;> simp [easyLabels, hj, ha_none]

private lemma hardLabels_lowerPrefix_eq (A : List Labeled) (idx : ℕ) :
    hardLabels
      ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
        if j < idx then { x with value := x.value - 3 } else x)) =
    hardLabels (A.eraseIdx idx) := by
  unfold hardLabels
  rw [List.filterMap_map]
  conv_rhs => rw [show A.eraseIdx idx = (A.eraseIdx idx).zipIdx.map Prod.fst from by simp]
  rw [List.filterMap_map]
  congr 1
  funext ⟨x, j⟩
  by_cases hj : j < idx <;> simp [hj]

private lemma hardMS_lowerPrefix_eq (A : List Labeled) (idx : ℕ) :
    hardMS
      ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
        if j < idx then { x with value := x.value - 3 } else x)) =
    hardMS (A.eraseIdx idx) := by
  unfold hardMS
  rw [hardLabels_lowerPrefix_eq]

private lemma s3Good_fired_record_eq_hardLabel
    {start A : List Labeled} {rec0 rec : List ℕ} {idx p : ℕ}
    (hgood : S3Good start rec0 A idx rec)
    (hidx : ¬ idx ≥ A.length)
    (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)
    (hhard : (A[idx]'(by omega)).origin = some (p, InsertionKind.hard)) :
    (forget A)[idx]! / 3 + idx = p := by
  have hi : idx < A.length := by omega
  have hrank := hgood.hardRank idx hi p (by
    convert hhard using 1)
  obtain ⟨_, horg, hsum⟩ := hrank
  have hprefix := hgood.prefixRank hi
  have hval_eq : (A[idx]'hi).value = (forget A)[idx]! := by
    have hlt : idx < (forget A).length := by simpa [length_forget] using hi
    rw [getElem!_pos (forget A) idx hlt]
    simp [forget, List.getElem_map]
  rw [hprefix] at hsum
  rw [hval_eq] at hsum
  omega

private lemma s3Good_delete_prefixCore
    {A : List Labeled} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none) :
    ∀ (j : ℕ)
      (hj : j < ((A.eraseIdx idx).zipIdx.map (fun x : Labeled × ℕ =>
        if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1)).length),
      j < idx →
        (((A.eraseIdx idx).zipIdx.map (fun x : Labeled × ℕ =>
          if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))[j]'hj).origin = none := by
  intro j hj hjlt
  have hidx_lt : idx < A.length := by omega
  have hlen_new :
      ((A.eraseIdx idx).zipIdx.map (fun x : Labeled × ℕ =>
        if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1)).length =
        A.length - 1 := by
    simp [List.length_eraseIdx_of_lt hidx_lt]
  have hj_old : j < A.length := by
    rw [hlen_new] at hj
    omega
  have hj_erase : j < (A.eraseIdx idx).length := by
    simpa [List.length_eraseIdx_of_lt hidx_lt] using hj
  rw [List.getElem_map, List.getElem_zipIdx]
  simp [hjlt]
  have hget : (A.eraseIdx idx)[j]'hj_erase = A[j]'hj_old := by
    rw [List.getElem_eraseIdx]
    simp [hjlt]
  rw [hget]
  exact hprefix j hj_old hjlt

/-- `coreNotFire` is preserved when a value is lowered by 3 in `ℕ`.

If `v ∈ {0, 1, 2}` then `v - 3 = 0` in `ℕ`, so `0 < v - 3` fails and the firing
conjunction fails trivially.  If `v ≥ 4` then `(v - 3) % 3 = v % 3`, so the
hypothesis carries.  If `v = 3` then `v % 3 = 0 ∧ 0 < v` holds, contradicting
the hypothesis (`v = 3` cannot be a core value satisfying `coreNotFire`). -/
private lemma coreNotFire_sub3 {v : ℕ}
    (h : ¬ (v % 3 = 0 ∧ 0 < v)) :
    ¬ ((v - 3) % 3 = 0 ∧ 0 < v - 3) := by
  intro ⟨hmod, hpos⟩
  apply h
  refine ⟨?_, by omega⟩
  -- v - 3 > 0 in ℕ means v ≥ 4; combined with (v-3)%3 = 0, get v%3 = 0.
  omega

/-! ### Accessors for the S3 delete-and-lower-prefix transform. -/

private lemma s3Delete_getElem_lt
    (A : List Labeled) (idx i : ℕ) (hidx_lt : idx < A.length) (hi_lt : i < idx)
    (hi_A : i < A.length)
    (hi : i < ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
        if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1)).length) :
    ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
        if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))[i]'hi
      = { value := (A[i]'hi_A).value - 3, origin := (A[i]'hi_A).origin } := by
  have hi_erase : i < (A.eraseIdx idx).length := by
    simpa [List.length_eraseIdx_of_lt hidx_lt] using hi
  have hgetE : (A.eraseIdx idx)[i]'hi_erase = A[i]'hi_A := by
    rw [List.getElem_eraseIdx]; simp [hi_lt]
  rw [List.getElem_map, List.getElem_zipIdx]
  simp [hi_lt, hgetE]

private lemma s3Delete_getElem_ge
    (A : List Labeled) (idx i : ℕ) (hidx_lt : idx < A.length) (hi_ge : ¬ i < idx)
    (hi_A : i + 1 < A.length)
    (hi : i < ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
        if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1)).length) :
    ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
        if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))[i]'hi
      = A[i+1]'hi_A := by
  have hi_erase : i < (A.eraseIdx idx).length := by
    simpa [List.length_eraseIdx_of_lt hidx_lt] using hi
  have hgetE : (A.eraseIdx idx)[i]'hi_erase = A[i+1]'hi_A := by
    rw [List.getElem_eraseIdx]; simp [hi_ge]
  rw [List.getElem_map, List.getElem_zipIdx]
  simp [hi_ge, hgetE]

/-! ### S3 delete-and-lower-prefix field lemmas. -/

private lemma s3Good_delete_coreNotFire
    {A : List Labeled} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hCNF : ∀ (i : ℕ) (hi : i < A.length),
      (A[i]'hi).origin = none →
        ¬ ((A[i]'hi).value % 3 = 0 ∧ 0 < (A[i]'hi).value)) :
    let A' := ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
      if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))
    ∀ (i : ℕ) (hi : i < A'.length),
      (A'[i]'hi).origin = none →
        ¬ ((A'[i]'hi).value % 3 = 0 ∧ 0 < (A'[i]'hi).value) := by
  intro A' i hi horg
  have hidx_lt : idx < A.length := by omega
  have hlen_new : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx_of_lt hidx_lt]
  by_cases h : i < idx
  · have hi_A : i < A.length := by omega
    have hA'i := s3Delete_getElem_lt A idx i hidx_lt h hi_A hi
    rw [hA'i] at horg ⊢
    -- horg : (A[i]).origin = none
    exact coreNotFire_sub3 (hCNF i hi_A horg)
  · have hi_A : i + 1 < A.length := by rw [hlen_new] at hi; omega
    have hA'i := s3Delete_getElem_ge A idx i hidx_lt h hi_A hi
    rw [hA'i] at horg ⊢
    exact hCNF (i+1) hi_A horg

private lemma s3Good_delete_hardPositive
    {A : List Labeled} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hpos : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
      (A[i]'hi).origin = some (p, .hard) → 0 < (A[i]'hi).value)
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none) :
    let A' := ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
      if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))
    ∀ (i : ℕ) (hi : i < A'.length) (p : ℕ),
      (A'[i]'hi).origin = some (p, .hard) → 0 < (A'[i]'hi).value := by
  intro A' i hi p horg
  have hidx_lt : idx < A.length := by omega
  have hlen_new : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx_of_lt hidx_lt]
  by_cases h : i < idx
  · -- Hard in prefix is vacuous: prefixCore says origin = none.
    exfalso
    have hi_A : i < A.length := by omega
    have hA'i := s3Delete_getElem_lt A idx i hidx_lt h hi_A hi
    rw [hA'i] at horg
    -- horg : (A[i]).origin = some (p, .hard) but A[i].origin = none.
    rw [hprefix i hi_A h] at horg
    cases horg
  · have hi_A : i + 1 < A.length := by rw [hlen_new] at hi; omega
    have hA'i := s3Delete_getElem_ge A idx i hidx_lt h hi_A hi
    rw [hA'i] at horg ⊢
    exact hpos (i+1) hi_A p horg

/-- After the S3 delete-and-lower-prefix transform, the prefix-core count at a
suffix index transports: `corePrefixAbove A' i = corePrefixAbove A (i+1)` when
`i ≥ idx` and `A[idx]` is not a core entry (hard, by `s3Good_firing_origin_hard`).

Decomposition:
* `A.take (i+1) = A.take idx ++ (A.drop idx).take (i+1 - idx)`.
* `A'.take i  = A'.take idx ++ (A'.drop idx).take (i - idx)`.
* `(A.take idx).countP = (A'.take idx).countP = idx` (both all-core by prefixCore).
* `(A.drop idx).take (i+1 - idx) = A[idx] :: (A.drop (idx+1)).take (i - idx)`.
* `(A'.drop idx).take (i - idx) = (A.drop (idx+1)).take (i - idx)` (eraseIdx).
* `A[idx]`'s `origin ≠ none` (hard), so the head contributes 0 to `countP`.
-/
private lemma corePrefixAbove_delete_shift
    {A : List Labeled} {idx i : ℕ} (hidx_lt : idx < A.length)
    (hi_ge : idx ≤ i) (hi_succ : i + 1 ≤ A.length)
    (hidx_not_core : (A[idx]'hidx_lt).origin ≠ none)
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none) :
    let A' := ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
      if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))
    corePrefixAbove A' i = corePrefixAbove A (i+1) := by
  intro A'
  have hlen_new : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx_of_lt hidx_lt]
  unfold corePrefixAbove
  -- Use `List.countP_take` decompositions via take/drop split at idx.
  set p : Labeled → Bool := fun y => decide (y.origin = none) with hp_def
  -- Decompose A.take (i+1) = A.take idx ++ (A.drop idx).take (i+1-idx).
  have hsplit_A : A.take (i+1) = A.take idx ++ (A.drop idx).take (i+1 - idx) := by
    conv_lhs => rw [show i+1 = idx + (i+1 - idx) from by omega]
    rw [List.take_add]
  -- Decompose A'.take i = A'.take idx ++ (A'.drop idx).take (i-idx).
  have hsplit_A' : A'.take i = A'.take idx ++ (A'.drop idx).take (i - idx) := by
    conv_lhs => rw [show i = idx + (i - idx) from by omega]
    rw [List.take_add]
  rw [hsplit_A, hsplit_A', List.countP_append, List.countP_append]
  -- Step 1: countP on A.take idx = idx (all core by prefixCore).
  have hA_pref : (A.take idx).countP p = idx := by
    rw [countP_eq_length_of_all p]
    · rw [List.length_take]; omega
    · intro x hx
      obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
      have hlen_take : (A.take idx).length = idx := by
        rw [List.length_take]; omega
      have hj_bound : j < idx := by rw [hlen_take] at hj; exact hj
      have hjA : j < A.length := by omega
      have hgetA : (A.take idx)[j]'hj = A[j]'hjA := List.getElem_take
      rw [← hget, hgetA, hp_def]
      simp [hprefix j hjA hj_bound]
  -- Step 2: countP on A'.take idx = idx (lowered prefix has same origins).
  have hA'_pref : (A'.take idx).countP p = idx := by
    rw [countP_eq_length_of_all p]
    · rw [List.length_take, hlen_new]; omega
    · intro x hx
      obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
      have hlen_take' : (A'.take idx).length = idx := by
        rw [List.length_take, hlen_new]; omega
      have hj_bound : j < idx := by rw [hlen_take'] at hj; exact hj
      have hjA : j < A.length := by omega
      have hjA' : j < A'.length := by rw [hlen_new]; omega
      have hgetA' : (A'.take idx)[j]'hj = A'[j]'hjA' := List.getElem_take
      rw [← hget, hgetA']
      have hA'j := s3Delete_getElem_lt A idx j hidx_lt hj_bound hjA hjA'
      rw [hA'j, hp_def]
      simp [hprefix j hjA hj_bound]
  rw [hA_pref, hA'_pref]
  -- Now show: idx + (A'.drop idx).take (i - idx).countP p =
  --           idx + (A.drop idx).take (i+1 - idx).countP p
  congr 1
  -- Step 3: Show the suffix counts agree.
  -- (A.drop idx).take (i+1 - idx) = A[idx] :: (A.drop (idx+1)).take (i - idx) for i ≥ idx.
  have hA_suf : (A.drop idx).take (i+1 - idx) =
      (A[idx]'hidx_lt) :: (A.drop (idx+1)).take (i - idx) := by
    have h1 : (A.drop idx).take (i+1 - idx) = (A.drop idx).take ((i - idx) + 1) := by
      congr 1; omega
    rw [h1]
    have h2 : A.drop idx = (A[idx]'hidx_lt) :: A.drop (idx+1) :=
      (List.drop_eq_getElem_cons hidx_lt)
    rw [h2, List.take_succ_cons]
  rw [hA_suf, List.countP_cons]
  -- Now: ((A.drop (idx+1)).take (i-idx)).countP p + (if p A[idx] then 1 else 0)
  -- A[idx].origin ≠ none, so p A[idx] = decide (A[idx].origin = none) = false.
  have hp_idx : p (A[idx]'hidx_lt) = false := by
    rw [hp_def]
    simp [hidx_not_core]
  rw [hp_idx]
  simp
  -- Remaining: (A'.drop idx).take (i - idx).countP p = (A.drop (idx+1)).take (i - idx).countP p.
  -- A'.drop idx in our case = (A.eraseIdx idx).drop idx mapped by the "if" (which is `else x` since j ≥ idx).
  -- (A.eraseIdx idx).drop idx = A.drop (idx+1) (since erasing position idx shifts everything after by 1).
  -- The map applies only `else x` for j ≥ idx, which is identity. So A'.drop idx = A.drop (idx+1).
  congr 1
  -- Show: (A'.drop idx).take (i - idx) = (A.drop (idx+1)).take (i - idx).
  apply List.ext_getElem
  · -- length equality
    have hlen_A'_drop : (A'.drop idx).length = A.length - 1 - idx := by
      rw [List.length_drop, hlen_new]
    have hlen_A_drop : (A.drop (idx+1)).length = A.length - (idx+1) := by
      rw [List.length_drop]
    simp [List.length_take, hlen_A'_drop, hlen_A_drop]; omega
  · intro k hk_A' hk_A
    -- Show: (A'.drop idx).take (i-idx) [k] = (A.drop (idx+1)).take (i-idx) [k].
    -- LHS: A'.drop idx [k] (when k < i-idx) = A'[k+idx].
    -- A'[k+idx]: since k+idx ≥ idx, accessor_ge gives A'[k+idx] = A[k+idx+1].
    -- RHS: A.drop (idx+1) [k] (when k < i-idx) = A[k+idx+1].
    rw [List.getElem_take, List.getElem_drop]
    rw [List.getElem_take, List.getElem_drop]
    have hk_bound : k < i - idx := by
      simp [List.length_take, List.length_drop, hlen_new] at hk_A'
      omega
    have hk_idx_A : k + idx + 1 < A.length := by omega
    have hk_idx_A' : k + idx < A'.length := by rw [hlen_new]; omega
    have h_not_lt : ¬ k + idx < idx := by omega
    have hA'_k_idx := s3Delete_getElem_ge A idx (k + idx) hidx_lt h_not_lt hk_idx_A hk_idx_A'
    convert hA'_k_idx using 2 <;> omega

private lemma s3Good_delete_hardRankS3
    {A : List Labeled} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hidx_not_core : (A[idx]'(by omega : idx < A.length)).origin ≠ none)
    (hrank : ∀ (i : ℕ) (hi : i < A.length) (p : ℕ),
      (A[i]'hi).origin = some (p, .hard) → HardRankAtS3 A i p)
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none) :
    let A' := ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
      if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))
    ∀ (i : ℕ) (hi : i < A'.length) (p : ℕ),
      (A'[i]'hi).origin = some (p, .hard) → HardRankAtS3 A' i p := by
  intro A' i hi p horg
  have hidx_lt : idx < A.length := by omega
  have hlen_new : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx_of_lt hidx_lt]
  by_cases h : i < idx
  · -- prefix: contradiction via prefixCore.
    exfalso
    have hi_A : i < A.length := by omega
    have hA'i := s3Delete_getElem_lt A idx i hidx_lt h hi_A hi
    rw [hA'i] at horg
    rw [hprefix i hi_A h] at horg
    cases horg
  · -- suffix: A'[i] = A[i+1], rank transports via corePrefixAbove_delete_shift.
    have hi_A : i + 1 < A.length := by rw [hlen_new] at hi; omega
    have hA'i := s3Delete_getElem_ge A idx i hidx_lt h hi_A hi
    have horg_A : (A[i+1]'hi_A).origin = some (p, .hard) := by rw [hA'i] at horg; exact horg
    have hrank_old := hrank (i+1) hi_A p horg_A
    obtain ⟨_, _, hsum⟩ := hrank_old
    refine ⟨hi, ?_, ?_⟩
    · rw [hA'i]; exact horg_A
    · have hcpa : corePrefixAbove A' i = corePrefixAbove A (i+1) := by
        have hge : idx ≤ i := by omega
        have hi_succ : i + 1 ≤ A.length := by omega
        exact corePrefixAbove_delete_shift hidx_lt hge hi_succ hidx_not_core hprefix
      rw [hA'i, hcpa]
      exact hsum

private lemma s3Good_delete_corePrefixAbove_idx
    {A : List Labeled} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hprefix : ∀ (j : ℕ) (hj : j < A.length), j < idx → (A[j]'hj).origin = none) :
    let A' := ((A.eraseIdx idx).zipIdx.map (fun (x : Labeled × ℕ) =>
      if x.2 < idx then { x.1 with value := x.1.value - 3 } else x.1))
    ∀ (_hi : idx < A'.length), corePrefixAbove A' idx = idx := by
  intro A' _hi
  have hidx_lt : idx < A.length := by omega
  have hlen_new : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx_of_lt hidx_lt]
  unfold corePrefixAbove
  have hlen_take : (A'.take idx).length = idx := by
    rw [List.length_take, hlen_new]; omega
  rw [countP_eq_length_of_all (fun y : Labeled => decide (y.origin = none))]
  · exact hlen_take
  · intro x hx
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
    have hj_bound : j < idx := by rw [hlen_take] at hj; exact hj
    have hjA' : j < A'.length := by rw [hlen_new]; omega
    have hgetA' : (A'.take idx)[j]'hj = A'[j]'hjA' := List.getElem_take
    rw [← hget, hgetA']
    have hjA : j < A.length := by omega
    have hA'j := s3Delete_getElem_lt A idx j hidx_lt hj_bound hjA hjA'
    rw [hA'j]
    simp [hprefix j hjA hj_bound]

private lemma s3Good_delete_rank_order_fields
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)
    (hgood : S3Good start rec0 A idx rec) :
    let A' := ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
      if j < idx then { x with value := x.value - 3 } else x))
    (∀ (i : ℕ) (hi : i < A'.length),
        (A'[i]'hi).origin = none →
          ¬ ((A'[i]'hi).value % 3 = 0 ∧ 0 < (A'[i]'hi).value)) ∧
    (∀ (i : ℕ) (hi : i < A'.length) (p : ℕ),
        (A'[i]'hi).origin = some (p, .hard) → HardRankAtS3 A' i p) ∧
    (∀ (i : ℕ) (hi : i < A'.length) (p : ℕ),
        (A'[i]'hi).origin = some (p, .hard) → 0 < (A'[i]'hi).value) ∧
    (∀ (hi : idx < A'.length), corePrefixAbove A' idx = idx) := by
  -- Derive `A[idx].origin ≠ none` from `hfire` + `hgood.coreNotFire`,
  -- needed for the count-shift in the hardRank field.
  have hidx_lt : idx < A.length := by omega
  have hidx_not_core : (A[idx]'hidx_lt).origin ≠ none := by
    intro hnone
    apply hgood.coreNotFire idx hidx_lt hnone
    have hval_eq : (A[idx]'hidx_lt).value = (forget A)[idx]! := by
      have hlt : idx < (forget A).length := by simpa [length_forget] using hidx_lt
      rw [getElem!_pos (forget A) idx hlt]
      simp [forget, List.getElem_map]
    rw [hval_eq]
    exact hfire
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact s3Good_delete_coreNotFire hidx hgood.coreNotFire
  · exact s3Good_delete_hardRankS3 hidx hidx_not_core hgood.hardRank hgood.prefixCore
  · exact s3Good_delete_hardPositive hidx hgood.hardPositive hgood.prefixCore
  · exact s3Good_delete_corePrefixAbove_idx hidx hgood.prefixCore

private lemma s3Good_delete_step
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)
    (hgood : S3Good start rec0 A idx rec) :
    S3Good start rec0
      ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
        if j < idx then { x with value := x.value - 3 } else x))
      idx (rec ++ [(forget A)[idx]! / 3 + idx]) := by
  have hhard := s3Good_firing_origin_hard hgood hidx hfire
  have hrankOrder := s3Good_delete_rank_order_fields (start := start) (rec0 := rec0)
    (rec := rec) hidx hfire hgood
  refine ⟨s3Good_delete_recPrefix hgood, ?_, s3Good_delete_noEasy hgood.noEasy, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hhard
    have hrec : (forget A)[idx]! / 3 + idx = p :=
      s3Good_fired_record_eq_hardLabel hgood hidx hfire hp
    have hi : idx < A.length := by omega
    have herase_perm := hardLabels_eraseIdx_of_hard A idx hi p hp
    have herase_ms : hardMS A = ({p} : Multiset ℕ) + hardMS (A.eraseIdx idx) := by
      unfold hardMS
      exact coe_multiset_eq_of_list_perm herase_perm
    have hlower : hardMS ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
        if j < idx then { x with value := x.value - 3 } else x)) =
        hardMS (A.eraseIdx idx) := hardMS_lowerPrefix_eq A idx
    have hacc := hgood.ms_account
    rw [herase_ms] at hacc
    calc
      deltaRecMS (rec ++ [(forget A)[idx]! / 3 + idx]) rec0 +
          hardMS ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
            if j < idx then { x with value := x.value - 3 } else x))
          = (deltaRecMS rec rec0 + ({p} : Multiset ℕ)) + hardMS (A.eraseIdx idx) := by
              rw [hlower, hrec]
              rw [deltaRecMS_append_singleton_of_prefix p hgood.rec_prefix]
      _ = deltaRecMS rec rec0 + (({p} : Multiset ℕ) + hardMS (A.eraseIdx idx)) := by
              rw [add_assoc]
      _ = hardMS start := hacc
  -- Dynamic S3 delete/lower-prefix preservation.
  · exact hrankOrder.1
  · exact hrankOrder.2.1
  · exact hrankOrder.2.2.1
  · exact hrankOrder.2.2.2
  · exact s3Good_delete_prefixCore hidx hgood.prefixCore

private lemma s3Good_skip_step
    {start A : List Labeled} {rec0 rec : List ℕ} {idx : ℕ}
    (hidx : ¬ idx ≥ A.length)
    (hfire : ¬ ((forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!))
    (hgood : S3Good start rec0 A idx rec) :
    S3Good start rec0 A (idx + 1) rec := by
  refine ⟨hgood.rec_prefix, hgood.ms_account, hgood.noEasy, hgood.coreNotFire,
    hgood.hardRank, hgood.hardPositive, ?_, ?_⟩
  · -- Frontier rank after skip is a dynamic S3 order invariant.
    intro hi_next
    have hidx_core : (A[idx]'(by omega)).origin = none :=
      s3Good_skip_index_core hgood hidx hfire
    exact corePrefixAbove_succ_of_prefixCore hgood.prefixCore hi_next hidx_core
  intro j hj hjlt
  by_cases hji : j < idx
  · exact hgood.prefixCore j hj hji
  · have hj_eq : j = idx := by omega
    subst hj_eq
    exact s3Good_skip_index_core hgood hidx hfire

private lemma s3Good_step_transitions
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    let recS2L := s2L_pair.2
    (∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ A.length)
        (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!),
        S3Good afterS2L recS2L A idx rec →
          S3Good afterS2L recS2L
            ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
              if j < idx then { x with value := x.value - 3 } else x))
            idx (rec ++ [(forget A)[idx]! / 3 + idx])) ∧
    (∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ A.length)
        (hfire : ¬ ((forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)),
        S3Good afterS2L recS2L A idx rec →
          S3Good afterS2L recS2L A (idx + 1) rec) := by
  intro labeled unl s2L_pair afterS2L recS2L
  constructor
  · intro A idx rec hidx hfire hgood
    exact s3Good_delete_step hidx hfire hgood
  · intro A idx rec hidx hfire hgood
    exact s3Good_skip_step hidx hfire hgood

private lemma deltaRecMS_scanFromLargestLabeled_eq_of_S3Good_transitions
    {start : List Labeled} {rec0 : List ℕ}
    (hdelete : ∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ A.length)
        (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!),
        S3Good start rec0 A idx rec →
          S3Good start rec0
            ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
              if j < idx then { x with value := x.value - 3 } else x))
            idx (rec ++ [(forget A)[idx]! / 3 + idx]))
    (hskip : ∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ A.length)
        (hfire : ¬ ((forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)),
        S3Good start rec0 A idx rec →
          S3Good start rec0 A (idx + 1) rec) :
    ∀ (fuel : ℕ) (A : List Labeled) (idx : ℕ) (rec : List ℕ),
      S3Good start rec0 A idx rec →
      fuel ≥ A.length - idx →
        deltaRecMS (scanFromLargestLabeled fuel A idx rec).2 rec0 = hardMS start := by
  intro fuel
  induction fuel with
  | zero =>
      intro A idx rec hgood hfuel
      have hterminal : idx ≥ A.length := by omega
      simp [scanFromLargestLabeled]
      exact s3Good_terminal_deltaRecMS hgood hterminal
  | succ fuel' ih =>
      intro A idx rec hgood hfuel
      by_cases hidx_ge : idx ≥ A.length
      · simp [scanFromLargestLabeled, hidx_ge]
        exact s3Good_terminal_deltaRecMS hgood hidx_ge
      · simp only [scanFromLargestLabeled]
        rw [if_neg hidx_ge]
        split
        · next hfire_prop =>
          have hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]! := by
            simpa [forget] using hfire_prop
          apply ih
          · exact hdelete A idx rec hidx_ge hfire hgood
          · have hlen_erased :
                (((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
                  if j < idx then { x with value := x.value - 3 } else x)).length) =
                  A.length - 1 := by
              simp [List.length_eraseIdx_of_lt (by omega : idx < A.length)]
            rw [hlen_erased]
            omega
        · next hfire_prop =>
          have hfire_false : ¬ ((forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!) := by
            intro hp
            have hbool : ((forget A)[idx]! % 3 == 0 && (forget A)[idx]! > 0) = true := by
              have hidx_lt : idx < A.length := by omega
              have hval :
                  (Option.map (fun x => x.value) A[idx]?).getD 0 = (forget A)[idx]! := by
                rw [getElem!_pos (forget A) idx (by simpa [length_forget] using hidx_lt)]
                simp [forget, List.getElem?_eq_getElem hidx_lt]
              have hprop :
                  (Option.map (fun x => x.value) A[idx]?).getD 0 % 3 = 0 ∧
                    0 < (Option.map (fun x => x.value) A[idx]?).getD 0 := by
                constructor
                · rw [hval]; exact hp.1
                · rw [hval]; exact hp.2
              simpa [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hprop
            exact hfire_prop hbool
          apply ih
          · exact hskip A idx rec hidx_ge hfire_false hgood
          · omega

private lemma s3Good_initial_and_transitions
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    let recS2L := s2L_pair.2
    S3Good afterS2L recS2L afterS2L 0 recS2L ∧
    (∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ A.length)
        (hfire : (forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!),
        S3Good afterS2L recS2L A idx rec →
          S3Good afterS2L recS2L
            ((A.eraseIdx idx).zipIdx.map (fun (x, j) =>
              if j < idx then { x with value := x.value - 3 } else x))
            idx (rec ++ [(forget A)[idx]! / 3 + idx])) ∧
    (∀ (A : List Labeled) (idx : ℕ) (rec : List ℕ)
        (hidx : ¬ idx ≥ A.length)
        (hfire : ¬ ((forget A)[idx]! % 3 = 0 ∧ 0 < (forget A)[idx]!)),
        S3Good afterS2L recS2L A idx rec →
          S3Good afterS2L recS2L A (idx + 1) rec) := by
  intro labeled unl s2L_pair afterS2L recS2L
  exact ⟨s3Good_initial_postS2 A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos,
    s3Good_step_transitions A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos⟩

/-- Labeled S3 core theorem; the unlabeled statement below is a transport
through `forget_scanFromLargestLabeled`. -/
private lemma s3_records_hard_ms_labeled
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    let recS2L := s2L_pair.2
    let s3L_pair := scanFromLargestLabeled (afterS2L.length + 1) afterS2L 0 recS2L
    deltaRecMS s3L_pair.2 recS2L = hardMS afterS2L := by
  intro labeled unl s2L_pair afterS2L recS2L s3L_pair
  have hs3 := s3Good_initial_and_transitions A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hgood0 := hs3.1
  have hdelete := hs3.2.1
  have hskip := hs3.2.2
  have hfuel : afterS2L.length + 1 ≥ afterS2L.length - 0 := by omega
  simpa using
    deltaRecMS_scanFromLargestLabeled_eq_of_S3Good_transitions
      (start := afterS2L) (rec0 := recS2L)
      hdelete hskip (afterS2L.length + 1) afterS2L 0 recS2L hgood0 hfuel

/-- **Bridge 4 core statement**: S3's added records, as a multiset, are exactly
the hard labels in the post-S2 labeled state. -/
private lemma s3_records_hard_ms
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    let recS2L := s2L_pair.2
    let afterS2 := forget afterS2L
    let recS3 := (scanFromLargest (afterS2.length + 1) afterS2 0 recS2L).2
    deltaRecMS recS3 recS2L = hardMS afterS2L := by
  intro labeled unl s2L_pair afterS2L recS2L afterS2 recS3
  set s3L_pair := scanFromLargestLabeled (afterS2L.length + 1) afterS2L 0 recS2L
    with hs3L_pair
  have hcomm := forget_scanFromLargestLabeled (afterS2L.length + 1) afterS2L 0 recS2L
  have hrec_eq : s3L_pair.2 = recS3 := by
    rw [hs3L_pair]
    have hrec_unl : recS3 =
        (scanFromLargest (afterS2L.length + 1) (forget afterS2L) 0 recS2L).2 := by
      simp [recS3, afterS2, length_forget]
    exact hcomm.2.trans hrec_unl.symm
  rw [← hrec_eq]
  rw [hs3L_pair]
  exact s3_records_hard_ms_labeled A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos

/-! ### Bridge 4: S3 records value/3 + h  p (the heart). -/
private lemma s3_records_at_witness_count
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl := forget labeled
    let s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 []
    let afterS2L := s2L_pair.1
    let recS2L := s2L_pair.2
    let afterS2 := forget afterS2L
    let recS3 := (scanFromLargest (afterS2.length + 1) afterS2 0 recS2L).2
    (List.diff recS3 recS2L).Perm (hardLabels afterS2L) := by
  exact list_diff_perm_of_deltaRecMS_eq_hardMS
    (s3_records_hard_ms A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos)

/-! END Lemma 4 sidecar -/

/-- **Invariant R-C** — paper `Thm2WithProof.tex` L604–613.

When S3 scans the post-S2 list (which contains exactly the hard-labeled
parts as its multiples of 3, by R-B), it deletes each in turn and
records `p` — the size of the original hard insertion — because the
value `3(p-h)` plus the current top-count `h` equals `p`.

PROOF GUIDE (paper): a hard-labeled part `x` was created at value
`3(p-h)` with `h` larger parts raised at creation.  By `no_raise_labels`,
`x`'s value never changes after creation; the `h` parts above it
(unlabeled nonmultiples of 3) remain above it until `x` is deleted.  Any
later inserted multiple above `x` is deleted earlier in S3 (S3 scans
largest-to-smallest); any later inserted easy multiple was deleted in S2
(by R-A).  So when S3 reaches `x`, exactly `h` parts are larger, and S3
records `(value/3) + h = (p-h) + h = p`. -/
lemma s3_records_hard_labels
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat   : IsThreeFlat (forget A_init))
    (hA_reg    : IsThreeRegular (forget A_init))
    (hA_clean  : ∀ x ∈ A_init, x.origin = none)
    (hν_sort   : ν.Pairwise (· ≥ ·))
    (hν_pos    : ∀ x ∈ ν, 0 < x) :
    let labeled := processInsertionsLabeled ν A_init
    let unl     := forget labeled
    let (afterS2, recS2) := scanFromSmallest (unl.length + 1) unl 0 []
    let recS3 := (scanFromLargest (afterS2.length + 1) afterS2 0 recS2).2
    (List.diff recS3 recS2).mergeSort (· ≥ ·) =
      (hardLabels labeled).mergeSort (· ≥ ·) := by
  set labeled := processInsertionsLabeled ν A_init with hlabeled
  set unl := forget labeled with hunl
  set s2_pair := scanFromSmallest (unl.length + 1) unl 0 ([] : List ℕ) with hs2_pair
  set afterS2 := s2_pair.1 with hafterS2
  set recS2 := s2_pair.2 with hrecS2
  set recS3 := (scanFromLargest (afterS2.length + 1) afterS2 0 recS2).2 with hrecS3
  set s2L_pair := scanFromSmallestLabeled (unl.length + 1) labeled 0 ([] : List ℕ)
    with hs2L_pair
  set afterS2L := s2L_pair.1 with hafterS2L
  set recS2L := s2L_pair.2 with hrecS2L
  have hcomm := forget_scanFromSmallestLabeled (unl.length + 1) labeled 0 ([] : List ℕ)
  have hafter_eq : afterS2 = forget afterS2L := by
    rw [hafterS2L]
    exact hcomm.1.symm
  have hrec_eq : recS2 = recS2L := by
    rw [hrecS2L]
    exact hcomm.2.symm
  have hhard_eq : hardLabels afterS2L = hardLabels labeled := by
    rw [hafterS2L, hs2L_pair]
    have hlen : unl.length + 1 = (forget labeled).length.succ := by
      simp [unl]
    rw [hlen]
    exact hardLabels_scanFromSmallestLabeled_eq_process
      A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hperm_after : (List.diff recS3 recS2).Perm (hardLabels afterS2L) := by
    subst recS3
    rw [hafter_eq, hrec_eq]
    exact s3_records_at_witness_count A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hperm : (List.diff recS3 recS2).Perm (hardLabels labeled) := by
    exact hperm_after.trans (List.Perm.of_eq hhard_eq)
  have htrans : ∀ (a b c : ℕ), decide (a ≥ b) = true → decide (b ≥ c) = true →
      decide (a ≥ c) = true := by simp; omega
  have htotal : ∀ (a b : ℕ), (decide (a ≥ b) || decide (b ≥ a)) = true := by simp; omega
  have h1 := List.pairwise_mergeSort htrans htotal (List.diff recS3 recS2)
  have h2 := List.pairwise_mergeSort htrans htotal (hardLabels labeled)
  have hperm' : ((List.diff recS3 recS2).mergeSort (· ≥ ·)).Perm
      ((hardLabels labeled).mergeSort (· ≥ ·)) :=
    (List.mergeSort_perm _ _).trans (hperm.trans (List.mergeSort_perm _ _).symm)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by simp at *; omega) h1 h2 hperm'
private lemma tryHard_labels_perm (A : List Labeled) (p h : ℕ) (r : List Labeled)
    (hr : tryHardInsertionLabeled A p h = some r) :
    (easyLabels r ++ hardLabels r).Perm (p :: (easyLabels A ++ hardLabels A)) := by
  unfold tryHardInsertionLabeled at hr
  have hcond : ¬(h ≥ p ∨ h > A.length) := by
    intro hc; simp [hc] at hr
  simp only [hcond, ↓reduceIte] at hr
  set newPart : Labeled := ⟨3 * (p - h), some (p, .hard)⟩ with newPart_def
  set raised := A.zipIdx.map (fun (x, j) =>
    if j < h then { x with value := x.value + 3 } else x) with raised_def
  set result := List.insertIdx raised h newPart with result_def
  have hr' : r = result := by
    revert hr
    split_ifs with hadm
    · intro h; exact (Option.some.inj h).symm
    · intro h; exact h.elim
  subst hr'
  have hlen : h ≤ raised.length := by
    simp [raised_def]; push_neg at hcond; exact hcond.2
  have hperm : result.Perm (newPart :: raised) :=
    List.perm_insertIdx newPart raised hlen
  have hfm := (List.Perm.filterMap (fun x : Labeled => match x.origin with
                     | some (p, .easy) => some p | _ => none) hperm).append
              (List.Perm.filterMap (fun x : Labeled => match x.origin with
                     | some (p, .hard) => some p | _ => none) hperm)
  change (easyLabels result ++ hardLabels result).Perm
    (easyLabels (newPart :: raised) ++ hardLabels (newPart :: raised)) at hfm
  have he_cons : easyLabels (newPart :: raised) = easyLabels raised := by
    simp [easyLabels, newPart_def]
  have hh_cons : hardLabels (newPart :: raised) = p :: hardLabels raised := by
    simp [hardLabels, newPart_def]
  have heq_easy : easyLabels raised = easyLabels A := by
    unfold easyLabels
    show List.filterMap _ raised = List.filterMap _ A
    rw [show raised = A.zipIdx.map (fun (x, j) =>
      if j < h then { x with value := x.value + 3 } else x) from rfl]
    rw [List.filterMap_map]
    conv_rhs => rw [show A = (A.zipIdx.map Prod.fst) from by simp]
    rw [List.filterMap_map]
    congr 1; funext ⟨x, j⟩; simp only [Function.comp_def]; split_ifs <;> rfl
  have heq_hard : hardLabels raised = hardLabels A := by
    unfold hardLabels
    show List.filterMap _ raised = List.filterMap _ A
    rw [show raised = A.zipIdx.map (fun (x, j) =>
      if j < h then { x with value := x.value + 3 } else x) from rfl]
    rw [List.filterMap_map]
    conv_rhs => rw [show A = (A.zipIdx.map Prod.fst) from by simp]
    rw [List.filterMap_map]
    congr 1; funext ⟨x, j⟩; simp only [Function.comp_def]; split_ifs <;> rfl
  rw [he_cons, hh_cons, heq_easy, heq_hard] at hfm
  exact hfm.trans (by
    show (easyLabels A ++ (p :: hardLabels A)).Perm (p :: (easyLabels A ++ hardLabels A))
    have : easyLabels A ++ p :: hardLabels A =
        (easyLabels A ++ [p]) ++ hardLabels A := by simp
    rw [this]
    have : p :: (easyLabels A ++ hardLabels A) =
        ([p] ++ easyLabels A) ++ hardLabels A := by simp
    rw [this]
    exact List.perm_append_comm.append_right _)

private lemma findHard_labels_perm (A : List Labeled) (p : ℕ) (r : List Labeled)
    (h_idx : ℕ := 0)
    (hr : findHardInsertionLabeled A p h_idx = some r) :
    (easyLabels r ++ hardLabels r).Perm (p :: (easyLabels A ++ hardLabels A)) := by
  by_cases hcond : h_idx ≥ p ∨ h_idx > A.length
  · simp [findHardInsertionLabeled, hcond] at hr
  · cases htry : tryHardInsertionLabeled A p h_idx with
    | some r' =>
      have : findHardInsertionLabeled A p h_idx = some r' := by
        rw [findHardInsertionLabeled]; simp [hcond, htry]
      rw [this] at hr
      have := Option.some.inj hr
      subst this
      exact tryHard_labels_perm A p h_idx r' htry
    | none =>
      have hfind : findHardInsertionLabeled A p h_idx =
          findHardInsertionLabeled A p (h_idx + 1) := by
        rw [findHardInsertionLabeled]; simp [hcond, htry]
      rw [hfind] at hr
      exact findHard_labels_perm A p r (h_idx + 1) hr
termination_by p + A.length + 1 - h_idx

private lemma tryEasy_labels_perm (A : List Labeled) (p : ℕ) (r : List Labeled)
    (hr : tryEasyInsertionLabeled A p = some r) :
    (easyLabels r ++ hardLabels r).Perm (p :: (easyLabels A ++ hardLabels A)) := by
  simp only [tryEasyInsertionLabeled] at hr
  set newPart : Labeled := ⟨3 * p, some (p, .easy)⟩ with newPart_def
  set pos := (A.takeWhile (·.value ≥ 3 * p)).length with pos_def
  set result := List.insertIdx A pos newPart with result_def
  have hr' : r = result := by
    revert hr
    split_ifs with hadm
    · intro h; exact (Option.some.inj h).symm
    · intro h; exact h.elim
  subst hr'
  have hlen : pos ≤ A.length := by
    simp [pos_def]; exact (A.takeWhile_prefix _).length_le
  have hperm : result.Perm (newPart :: A) :=
    List.perm_insertIdx newPart A hlen
  have hfm := (List.Perm.filterMap (fun x : Labeled => match x.origin with
                     | some (p, .easy) => some p | _ => none) hperm).append
              (List.Perm.filterMap (fun x : Labeled => match x.origin with
                     | some (p, .hard) => some p | _ => none) hperm)
  change (easyLabels result ++ hardLabels result).Perm
    (easyLabels (newPart :: A) ++ hardLabels (newPart :: A)) at hfm
  have he_cons : easyLabels (newPart :: A) = p :: easyLabels A := by
    simp [easyLabels, newPart_def]
  have hh_cons : hardLabels (newPart :: A) = hardLabels A := by
    simp [hardLabels, newPart_def]
  rw [he_cons, hh_cons] at hfm
  exact hfm.trans (by simp [List.cons_append])

/-- Each `performInsertionLabeled` step adds exactly one label `p` (either easy
or hard), provided the insertion succeeds (i.e., not the fallback case). -/
private lemma labels_perm_of_perform (A : List Labeled) (p : ℕ)
    (h_succeeds : findHardInsertionLabeled A p ≠ none ∨ tryEasyInsertionLabeled A p ≠ none) :
    (easyLabels (performInsertionLabeled A p) ++ hardLabels (performInsertionLabeled A p)).Perm
      (p :: (easyLabels A ++ hardLabels A)) := by
  unfold performInsertionLabeled
  match hm : findHardInsertionLabeled A p with
  | some r =>
    simp only [hm]
    exact findHard_labels_perm A p r 0 hm
  | none =>
    simp only [hm]
    match hm2 : tryEasyInsertionLabeled A p with
    | some r =>
      simp only [hm2]
      exact tryEasy_labels_perm A p r hm2
    | none =>
      exfalso
      rcases h_succeeds with h1 | h2
      · exact h1 hm
      · exact h2 hm2

private lemma findHardInsertion_preserves_height_inv (A : List ℕ) (p q h₀ : ℕ) (r : List ℕ)
    (h_inv : ∀ (i : ℕ) (hi : i < A.length), 3 ∣ A[i]'hi → A[i]'hi + 3 * i ≥ 3 * q)
    (hpq : p ≥ q)
    (hr : findHardInsertion A p h₀ = some r) :
    ∀ (i : ℕ) (hi : i < r.length), 3 ∣ r[i]'hi → r[i]'hi + 3 * i ≥ 3 * q := by
  unfold findHardInsertion at hr
  split at hr
  · simp at hr
  · next hguard =>
    push_neg at hguard
    obtain ⟨hlt_p, hle_len⟩ := hguard
    split at hr
    · next result0 htry_eq =>
      have hr_eq : result0 = r := Option.some.inj hr
      intro i hi hdvd
      simp only [tryHardInsertion] at htry_eq
      split at htry_eq
      · simp at htry_eq
      · split at htry_eq
        · next hcond =>
          have heq := Option.some.inj htry_eq
          set newPart := 3 * (p - h₀)
          set raised := List.map (fun x : ℕ × ℕ => if x.2 < h₀ then x.1 + 3 else x.1) A.zipIdx
          set result := List.insertIdx raised h₀ newPart
          have hraised_len : raised.length = A.length := by simp [raised]
          have hresult_len : result.length = A.length + 1 := by
            simp only [result, List.length_insertIdx]; split <;> omega
          have h_r0_eq : result0 = result := heq.symm
          have h_r_eq : r = result := by rw [← hr_eq, h_r0_eq]
          have hraised_lt_val (j : ℕ) (hj : j < h₀) :
              raised[j]'(by omega) = A[j]'(by omega) + 3 := by
            simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
            simp only [Nat.zero_add]; exact if_pos hj
          have hraised_ge_val (j : ℕ) (hj : ¬(j < h₀)) (hjlen : j < A.length) :
              raised[j]'(by omega) = A[j]'hjlen := by
            simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
            simp only [Nat.zero_add]; exact if_neg hj
          have hresult_before (j : ℕ) (hj : j < h₀) :
              result[j]'(by omega) = A[j]'(by omega) + 3 := by
            simp only [result, List.getElem_insertIdx, show j < h₀ from hj]
            exact hraised_lt_val j hj
          have hresult_at : result[h₀]'(by omega) = newPart := by
            simp only [result, List.getElem_insertIdx, show ¬(h₀ < h₀) from Nat.lt_irrefl h₀]
            simp
          have hresult_after (j : ℕ) (hj : j > h₀) (hjlen : j < result.length) :
              result[j]'hjlen = A[j - 1]'(by omega) := by
            simp only [result, List.getElem_insertIdx, show ¬(j < h₀) from by omega,
                       show ¬(j = h₀) from by omega]
            exact hraised_ge_val (j - 1) (by omega) (by omega)
          have hi' : i < result.length := h_r_eq ▸ hi
          suffices h : result[i]'hi' + 3 * i ≥ 3 * q by
            have heq_val : r[i]'hi = result[i]'hi' := by
              subst h_r_eq; rfl
            linarith [heq_val]
          by_cases hi_lt : i < h₀
          · have := hresult_before i hi_lt
            rw [this]
            have hdvd' : 3 ∣ result[i]'hi' := by subst h_r_eq; exact hdvd
            rw [this] at hdvd'
            have hdvd_orig : 3 ∣ A[i]'(by omega) := by omega
            have := h_inv i (by omega) hdvd_orig
            omega
          · by_cases hi_eq : i = h₀
            · subst hi_eq
              rw [hresult_at]
              show 3 * (p - i) + 3 * i ≥ 3 * q
              omega
            · have hi_gt : i > h₀ := by omega
              have := hresult_after i hi_gt hi'
              rw [this]
              have hdvd' : 3 ∣ result[i]'hi' := by subst h_r_eq; exact hdvd
              rw [this] at hdvd'
              have := h_inv (i - 1) (by omega) hdvd'
              omega
        · simp at htry_eq
    · exact findHardInsertion_preserves_height_inv A p q (h₀ + 1) r h_inv hpq hr
termination_by p + A.length + 1 - h₀

private lemma performInsertion_preserves_height_inv (A : List ℕ) (p q : ℕ)
    (h_inv : ∀ (i : ℕ) (hi : i < A.length), 3 ∣ A[i]'hi → A[i]'hi + 3 * i ≥ 3 * q)
    (hpq : p ≥ q) :
    ∀ (i : ℕ) (hi : i < (performInsertion A p).length),
      3 ∣ (performInsertion A p)[i]'hi → (performInsertion A p)[i]'hi + 3 * i ≥ 3 * q := by
  unfold performInsertion
  split
  · next result hr =>
    exact findHardInsertion_preserves_height_inv A p q 0 result h_inv hpq hr
  · split
    · next result hr =>
      intro i hi hdvd
      simp only [tryEasyInsertion] at hr
      split at hr
      · next hcond =>
        have heq := Option.some.inj hr
        set pos := (A.takeWhile (· ≥ 3 * p)).length
        set result_easy := List.insertIdx A pos (3 * p)
        have hpos_le : pos ≤ A.length :=
          (List.IsPrefix.sublist (List.takeWhile_prefix _)).length_le
        have hresult_len : result_easy.length = A.length + 1 := by
          simp only [result_easy, List.length_insertIdx]; split <;> omega
        have h_eq : result = result_easy := heq.symm
        have hresult_before (j : ℕ) (hj : j < pos) :
            result_easy[j]'(by omega) = A[j]'(by omega) := by
          simp [result_easy, List.getElem_insertIdx, hj]
        have hresult_at : result_easy[pos]'(by omega) = 3 * p := by
          simp [result_easy, List.getElem_insertIdx]
        have hresult_after (j : ℕ) (hj : j > pos) (hjlen : j < result_easy.length) :
            result_easy[j]'hjlen = A[j - 1]'(by omega) := by
          simp [result_easy, List.getElem_insertIdx, show ¬(j < pos) from by omega,
                show ¬(j = pos) from by omega]
        have hi' : i < result_easy.length := by rw [← h_eq]; exact hi
        suffices h : result_easy[i]'hi' + 3 * i ≥ 3 * q by
          have heq_val : result[i]'hi = result_easy[i]'hi' := by
            subst h_eq; rfl
          linarith [heq_val]
        have hdvd' : 3 ∣ result_easy[i]'hi' := by
          have heq_val : result[i]'hi = result_easy[i]'hi' := by subst h_eq; rfl
          rw [← heq_val]; exact hdvd
        by_cases hi_lt : i < pos
        · rw [hresult_before i hi_lt] at hdvd' ⊢
          exact h_inv i (by omega) hdvd'
        · by_cases hi_eq : i = pos
          · subst hi_eq
            rw [hresult_at]
            have : 3 * p + 3 * pos ≥ 3 * p := Nat.le_add_right _ _
            linarith [Nat.mul_le_mul_left 3 hpq]
          · have hi_gt : i > pos := by omega
            rw [hresult_after i hi_gt hi']
            rw [hresult_after i hi_gt hi'] at hdvd'
            have := h_inv (i - 1) (by omega) hdvd'
            omega
      · simp at hr
    · exact h_inv

private lemma not_in_takeWhile_lt' (A : List ℕ) (p : ℕ)
    (pos : ℕ) (hpos_def : pos = (A.takeWhile (· ≥ 3*p)).length)
    (hpos_lt : pos < A.length) :
    A[pos]'hpos_lt < 3 * p := by
  subst hpos_def
  induction A with
  | nil => simp at hpos_lt
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    split
    · next h =>
      simp only [List.length_cons, List.getElem_cons_succ]
      exact ih (by simp only [List.takeWhile_cons, h, ↓reduceIte, List.length_cons] at hpos_lt; omega)
    · next h =>
      simp only [List.length_nil, List.getElem_cons_zero]
      simp [decide_eq_true_eq] at h
      omega

-- Elements in the takeWhile prefix satisfy the predicate
private lemma takeWhile_prefix_ge' (A : List ℕ) (p : ℕ)
    (j : ℕ) (hj : j < (A.takeWhile (· ≥ 3*p)).length) (hjA : j < A.length) :
    A[j]'hjA ≥ 3 * p := by
  have hmem : (A.takeWhile (· ≥ 3*p))[j] ∈ A.takeWhile (· ≥ 3*p) := List.getElem_mem ..
  have hpred := List.mem_takeWhile_imp hmem
  have hge := of_decide_eq_true hpred
  have hprefix := List.takeWhile_prefix (p := fun x => decide (x ≥ 3*p)) (l := A)
  have heq : (A.takeWhile (· ≥ 3*p))[j] = A[j]'hjA := by
    exact List.IsPrefix.getElem hprefix hj
  linarith [heq]

set_option maxHeartbeats 1600000 in
private lemma tryEasyInsertion_succeeds_of_pos_pos' (A : List ℕ) (p : ℕ)
    (hflat : IsThreeFlat A) (hp : 0 < p)
    (hpos_pos : 0 < (A.takeWhile (· ≥ 3*p)).length)
    (hAne : A ≠ []) :
    (tryEasyInsertion A p).isSome := by
  set pos := (A.takeWhile (· ≥ 3*p)).length with hpos_def
  set result := List.insertIdx A pos (3 * p) with hresult_def
  have hpos_le : pos ≤ A.length := (List.IsPrefix.sublist (List.takeWhile_prefix _)).length_le
  have hpos_lt : pos < A.length := by
    by_contra hge; push_neg at hge
    have hAlen_pos : 0 < A.length := by cases A with | nil => simp at hAne | cons _ _ => simp
    have hlast_ge := takeWhile_prefix_ge' A p (A.length - 1) (by omega) (by omega)
    have hlast' := hflat.2.2 hAne
    have : A[A.length - 1]'(by omega) = A.getLast hAne := by simp [List.getLast_eq_getElem]
    omega
  have hprev_ge : A[pos - 1]'(by omega) ≥ 3 * p := takeWhile_prefix_ge' A p (pos - 1) (by omega) (by omega)
  have hcur_lt : A[pos]'hpos_lt < 3 * p := not_in_takeWhile_lt' A p pos rfl hpos_lt
  have hgap_orig : A[pos - 1]'(by omega) - A[pos]'hpos_lt < 3 := by
    have h := hflat.2.1 (pos - 1) (by omega : (pos - 1) + 1 < A.length)
    convert h using 2; congr 1; omega
  have hgap_left : A[pos - 1]'(by omega) - (3 * p) < 3 := by omega
  have hgap_right : 3 * p - A[pos]'hpos_lt < 3 := by omega
  have hresult_len : result.length = A.length + 1 := by
    simp [result, List.length_insertIdx, show pos ≤ A.length from hpos_le]
  have hresult_lt' (i : ℕ) (hi : i < pos) : result[i]'(by omega) = A[i]'(by omega) := by
    simp [result, List.getElem_insertIdx, hi]
  have hresult_eq : result[pos]'(by omega) = 3 * p := by simp [result, List.getElem_insertIdx]
  have hresult_gt' (i : ℕ) (hi : i > pos) (hilen : i < result.length) :
      result[i]'hilen = A[i-1]'(by omega) := by
    simp [result, List.getElem_insertIdx, show ¬(i < pos) from by omega, show ¬(i = pos) from by omega]
  suffices hcond : isThreeFlatBool result = true ∧ isFlatRemovableBool result pos = true by
    unfold tryEasyInsertion
    simp only [show (A.takeWhile (· ≥ 3 * p)).length = pos from rfl,
               show List.insertIdx A pos (3 * p) = result from rfl,
               hcond.1, hcond.2, Bool.and_self, ↓reduceIte, Option.isSome_some]
  obtain ⟨⟨hpw, hpos_all⟩, hgaps, hlast⟩ := hflat
  refine ⟨?_, ?_⟩
  · unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      by_cases hi_lt : i < pos
      · by_cases hj_lt : j < pos
        · rw [hresult_lt' i hi_lt, hresult_lt' j hj_lt]
          exact List.pairwise_iff_getElem.mp hpw i j (by omega) (by omega) hij
        · by_cases hj_eq : j = pos
          · have hrj : result[j]'hj = 3 * p := by
              have : result[j]'hj = result[pos]'(by omega) := by congr 1; try omega
              rw [this]; exact hresult_eq
            rw [hresult_lt' i hi_lt, hrj]
            exact takeWhile_prefix_ge' A p i (by omega) (by omega)
          · rw [hresult_lt' i hi_lt, hresult_gt' j (by omega) hj]
            exact List.pairwise_iff_getElem.mp hpw i (j-1) (by omega) (by omega) (by omega)
      · by_cases hi_eq : i = pos
        · have hj_gt : j > pos := by omega
          have hri : result[i]'hi = 3 * p := by
            have : result[i]'hi = result[pos]'(by omega) := by congr 1; try omega
            rw [this]; exact hresult_eq
          rw [hri, hresult_gt' j hj_gt hj]
          have : A[j-1]'(by omega) ≤ A[pos]'hpos_lt := by
            rcases Nat.lt_or_ge (j - 1) (pos + 1) with h | h
            · exact le_of_eq (by congr 1; omega)
            · exact List.pairwise_iff_getElem.mp hpw pos (j-1) hpos_lt (by omega) (by omega)
          omega
        · rw [hresult_gt' i (by omega) hi, hresult_gt' j (by omega) hj]
          exact List.pairwise_iff_getElem.mp hpw (i-1) (j-1) (by omega) (by omega) (by omega)
    · intro x hx; simp only [result] at hx
      rw [List.mem_insertIdx (by omega : pos ≤ A.length)] at hx
      rcases hx with rfl | hx
      · positivity
      · exact hpos_all x hx
    · intro i hi; rw [hresult_len] at hi
      rw [getElem!_pos result i (by omega), getElem!_pos result (i+1) (by omega)]
      by_cases hi_lt : i < pos
      · by_cases hi1_lt : i + 1 < pos
        · rw [hresult_lt' i hi_lt, hresult_lt' (i+1) hi1_lt]; exact hgaps i (by omega)
        · have hri : result[i]'(by omega) = A[pos-1]'(by omega) := by
            rw [hresult_lt' i hi_lt]; congr 1; omega
          have hri1 : result[i+1]'(by omega) = 3 * p := by
            have : result[i+1]'(by omega) = result[pos]'(by omega) := by congr 1; try omega
            rw [this]; exact hresult_eq
          rw [hri, hri1]; exact hgap_left
      · by_cases hi_eq : i = pos
        · have hri : result[i]'(by omega) = 3 * p := by
            have : result[i]'(by omega) = result[pos]'(by omega) := by congr 1; try omega
            rw [this]; exact hresult_eq
          have hri1 : result[i+1]'(by omega) = A[pos]'hpos_lt := by
            rw [hresult_gt' (i+1) (by omega) (by omega)]; congr 1; try omega
          rw [hri, hri1]; exact hgap_right
        · have hri : result[i]'(by omega) = A[i-1]'(by omega) := hresult_gt' i (by omega) (by omega)
          have hri1 : result[i+1]'(by omega) = A[i]'(by omega) := by
            rw [hresult_gt' (i+1) (by omega) (by omega)]; congr 1; try omega
          rw [hri, hri1]
          have hgi := hgaps (i - 1) (by omega : (i - 1) + 1 < A.length)
          convert hgi using 2; congr 1; omega
    · have hne2 : result ≠ [] := by intro he; simp [he] at hresult_len
      rw [List.getLast?_eq_some_getLast hne2]; simp only [decide_eq_true_eq]
      have hlast_val : result.getLast hne2 = A.getLast hAne := by
        rw [List.getLast_eq_getElem, List.getLast_eq_getElem,
            hresult_gt' (result.length - 1) (by omega) (by omega)]
        congr 1; omega
      rw [hlast_val]; exact hlast hAne
  · unfold isFlatRemovableBool
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · rw [getElem!_pos result pos (by omega), hresult_eq]; omega
    · rw [show result.eraseIdx pos = A from List.eraseIdx_insertIdx_self (3 * p)]
      unfold isThreeFlatBool isPositivePartitionBool
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨hpw, fun x hx => hpos_all x hx⟩, ?_⟩, ?_⟩
      · intro i hi; rw [getElem!_pos A i (by omega), getElem!_pos A (i+1) (by omega)]
        exact hgaps i (by omega)
      · cases hl : A.getLast? with
        | none => simp
        | some x => simp; rw [List.getLast?_eq_some_getLast hAne] at hl
                    exact (Option.some.inj hl) ▸ hlast hAne

-- Helper: tryEasyInsertion succeeds when pos = 0 and A[0] > 3*(p-1)
-- When pos=0, result is 3*p :: A. It's 3-flat iff 3*p - A[0] < 3.
-- Since A[0] > 3*(p-1) = 3*p-3, we get 3*p - A[0] < 3.
-- Also isFlatRemovableBool (3*p :: A) 0 = true since erase gives A.
set_option maxHeartbeats 800000 in
private lemma tryEasyInsertion_succeeds_of_pos_zero_large (A : List ℕ) (p : ℕ)
    (hflat : IsThreeFlat A) (hp : 0 < p)
    (hpos_zero : (A.takeWhile (· ≥ 3*p)).length = 0)
    (hAlen_pos : 0 < A.length)
    (hlarge : A[0]'hAlen_pos > 3 * (p - 1)) :
    (tryEasyInsertion A p).isSome := by
  -- First establish A[0] < 3*p
  have hA0_lt : A[0]'hAlen_pos < 3 * p := by
    have := not_in_takeWhile_lt' A p 0 (by omega) hAlen_pos
    exact this
  -- Prove isThreeFlatBool A = true
  have isThreeFlatBool_of_IsThreeFlat : isThreeFlatBool A = true := by
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := hflat
    refine ⟨⟨⟨hpw, ?_⟩, ?_⟩, ?_⟩
    · intro x hx; exact hpos x hx
    · intro i hi
      have hlen : i + 1 < A.length := by omega
      have hgi := hgaps i hlen
      rw [getElem!_pos A i (by omega), getElem!_pos A (i+1) (by omega)]
      exact hgi
    · cases hl : A.getLast? with
      | none => simp
      | some x =>
        simp
        have hne : A ≠ [] := by intro h; simp [h] at hl
        rw [List.getLast?_eq_some_getLast hne] at hl
        have hlast2 := hlast hne
        have heq := Option.some.inj hl
        rw [← heq]; exact hlast2
  -- Unfold tryEasyInsertion and simplify with pos = 0
  unfold tryEasyInsertion
  simp only [hpos_zero]
  have hins : List.insertIdx A 0 (3 * p) = (3 * p) :: A := by
    simp [List.insertIdx_zero]
  simp only [hins]
  -- First prove isFlatRemovableBool (3*p :: A) 0 = true
  have hremov : isFlatRemovableBool ((3 * p) :: A) 0 = true := by
    unfold isFlatRemovableBool
    simp only [List.length_cons, Nat.zero_lt_succ, decide_true, Bool.true_and,
               List.getElem!_cons_zero, Nat.mul_mod_right, beq_self_eq_true,
               List.eraseIdx_cons_zero]
    exact isThreeFlatBool_of_IsThreeFlat
  -- Now prove isThreeFlatBool (3*p :: A) = true
  have hflat_cons : isThreeFlatBool ((3 * p) :: A) = true := by
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := hflat
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- Pairwise (· ≥ ·) for (3*p :: A)
      apply List.pairwise_cons.mpr
      constructor
      · intro x hx
        have hge := List.pairwise_iff_getElem.mp hpw
        have h0 : A[0]'hAlen_pos < 3 * p := hA0_lt
        have hx_le : x ≤ A[0]'hAlen_pos := by
          rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · exact Nat.le_refl _
          · exact hge 0 i hAlen_pos hi (by omega)
        omega
      · exact hpw
    · -- all (· > 0) for (3*p :: A)
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · positivity
      · exact hpos x hx
    · -- gaps < 3 for (3*p :: A)
      intro i hi
      simp only [List.length_cons] at hi
      have hilen : i + 1 < (3 * p :: A).length := by simp; omega
      rw [getElem!_pos (3 * p :: A) i (by simp; omega),
          getElem!_pos (3 * p :: A) (i+1) (by simp; omega)]
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · -- gap from (3*p :: A)[0] to (3*p :: A)[1] = 3*p - A[0]
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        omega
      · -- gap from (3*p :: A)[i] to (3*p :: A)[i+1] for i ≥ 1
        have hii : (3 * p :: A)[i]'(by simp; omega) = A[i-1]'(by omega) := by
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          simp [List.getElem_cons_succ]
        have hii1 : (3 * p :: A)[i+1]'(by simp; omega) = A[i]'(by omega) := by
          simp [List.getElem_cons_succ]
        rw [hii, hii1]
        have hgi := hgaps (i - 1) (by omega : (i - 1) + 1 < A.length)
        have heq : A[i - 1 + 1]'(by omega) = A[i]'(by omega) := by
          congr 1; omega
        linarith [heq ▸ hgi]
    · -- last element < 3
      simp only [List.getLast?_cons]
      cases hl : A.getLast? with
      | none =>
        have hne : A ≠ [] := by intro h; simp [h] at hAlen_pos
        have := List.getLast?_eq_some_getLast hne
        rw [this] at hl; simp at hl
      | some x =>
        simp
        have hne : A ≠ [] := by intro h; simp [h] at hAlen_pos
        rw [List.getLast?_eq_some_getLast hne] at hl
        have hlast2 := hlast hne
        have heq := Option.some.inj hl
        rw [← heq]; exact hlast2
  -- Combine
  simp [hflat_cons, hremov]

-- Helper: findHardInsertion succeeds when all elements ≤ 3*(p-1)
-- The safety bound forces existence of an h where tryHardInsertion works.
private lemma findHardInsertion_isSome_of_try_at (A : List ℕ) (p h₀ h : ℕ)
    (hh₀_lt : h₀ < p) (hh₀_le : h₀ ≤ A.length)
    (htry : (tryHardInsertion A p h₀).isSome)
    (hle : h ≤ h₀) :
    (findHardInsertion A p h).isSome := by
  have key : ∀ n : ℕ, ∀ h' : ℕ, h₀ + 1 - h' = n + 1 → h' ≤ h₀ →
      (findHardInsertion A p h').isSome := by
    intro n
    induction n with
    | zero =>
      intro h' heq hle'
      have hh'_eq : h' = h₀ := by omega
      rw [hh'_eq]; unfold findHardInsertion
      rw [if_neg (by omega : ¬(h₀ ≥ p ∨ h₀ > A.length))]
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp htry
      rw [hr]; simp
    | succ m ih =>
      intro h' heq hle'
      unfold findHardInsertion
      rw [if_neg (by omega : ¬(h' ≥ p ∨ h' > A.length))]
      cases hc : tryHardInsertion A p h' with
      | some r => simp
      | none => simp; exact ih (h' + 1) (by omega) (by omega)
  exact key (h₀ - h) h (by omega) hle

set_option maxHeartbeats 800000 in
private lemma findHardInsertion_succeeds_of_all_small (A : List ℕ) (p : ℕ)
    (hflat : IsThreeFlat A) (hreg : IsThreeRegular A)
    (hp : 0 < p) (hp_le : p ≤ A.length)
    (hsafe : ∀ (i : Fin A.length), A[i.val] + 3 * (i.val + 1) ≤ 3 * p + 3 * A.length)
    (hsmall : ∀ (i : ℕ) (hi : i < A.length), A[i]'hi ≤ 3 * (p - 1)) :
    (findHardInsertion A p).isSome := by
  -- Suffices to find h₀ < p, h₀ ≤ A.length where tryHardInsertion succeeds
  suffices ∃ h₀, h₀ < p ∧ h₀ ≤ A.length ∧ (tryHardInsertion A p h₀).isSome by
    obtain ⟨h₀, hlt, hle, htry⟩ := this
    exact findHardInsertion_isSome_of_try_at A p h₀ 0 hlt hle htry (Nat.zero_le _)
  -- Crossing argument: define P(h) := A[h] ≥ 3*(p-h) - 2 for h < p.
  -- Show ¬P(0) and P(p-1), find first h₀ where P holds.
  -- At h₀: A[h₀] ≥ 3*(p-h₀)-2, and ¬P(h₀-1) gives A[h₀-1] ≤ 3*(p-h₀)-1 (using hreg).
  -- These conditions guarantee tryHardInsertion succeeds at h₀.
  have hAlen_pos : 0 < A.length := by omega
  -- ¬P(0): A[0] ≤ 3*(p-1) = 3*p-3 < 3*p-2
  have hnotP0 : A[0]'hAlen_pos < 3 * p - 2 := by
    have := hsmall 0 hAlen_pos; omega
  -- P(p-1): A[p-1] ≥ 1 ≥ 3*(p-(p-1))-2 = 1
  have hPpm1 : A[p-1]'(by omega) ≥ 3 * (p - (p-1)) - 2 := by
    have := hflat.1.2 (A[p-1]'(by omega)) (List.getElem_mem ..); omega
  have hp_ge2 : p ≥ 2 := by
    have hA0_pos := hflat.1.2 (A[0]'hAlen_pos) (List.getElem_mem hAlen_pos)
    omega
  have hfind : ∃ (h₀ : ℕ) (_ : h₀ < A.length), h₀ ≥ 1 ∧ h₀ < p ∧
      A[h₀]'(by omega) ≥ 3 * (p - h₀) - 2 ∧
      A[h₀ - 1]'(by omega) < 3 * (p - h₀) + 1 := by
    -- Inductive search from p-1 downward
    suffices aux : ∀ k : ℕ, (hk : k < p) → k ≥ 1 → A[k]'(by omega) ≥ 3 * (p - k) - 2 →
        ∃ (h₀ : ℕ) (_ : h₀ < A.length), h₀ ≥ 1 ∧ h₀ < p ∧
          A[h₀]'(by omega) ≥ 3 * (p - h₀) - 2 ∧
          A[h₀ - 1]'(by omega) < 3 * (p - h₀) + 1 by
      exact aux (p - 1) (by omega) (by omega) hPpm1
    intro k hk
    induction k with
    | zero => intro hge; omega
    | succ n ih =>
      intro hn_ge hPn
      by_cases hn_zero : n = 0
      · subst hn_zero
        refine ⟨1, by omega, by omega, by omega, hPn, ?_⟩
        -- Need: A[0] < 3*(p-1)+1. We have hnotP0: A[0] < 3*p-2 and 3*(p-1)+1 = 3*p-2
        show A[1 - 1]'(by omega) < 3 * (p - 1) + 1
        simp only [show 1 - 1 = 0 from rfl]; omega
      · by_cases hPprev : A[n]'(by omega) ≥ 3 * (p - n) - 2
        · exact ih (by omega) (by omega) hPprev
        · push_neg at hPprev
          refine ⟨n + 1, by omega, by omega, hk, hPn, ?_⟩
          -- Need: A[n+1-1] < 3*(p-(n+1))+1, i.e., A[n] < 3*(p-n-1)+1
          -- hPprev: A[n] < 3*(p-n)-2. And 3*(p-n)-2 = 3*(p-n-1)+1
          show A[n + 1 - 1]'(by omega) < 3 * (p - (n + 1)) + 1
          have heq : n + 1 - 1 = n := by omega
          simp only [heq]; omega
  -- Step 2: Use h₀ to show tryHardInsertion succeeds
  obtain ⟨h₀, hh₀_lt_len, hh₀_ge, hh₀_lt, hAh₀_ge, hAh₀m1_lt⟩ := hfind
  refine ⟨h₀, hh₀_lt, by omega, ?_⟩
  -- Key arithmetic setup
  have hreg_h₀m1 : ¬(3 ∣ A[h₀ - 1]'(by omega)) :=
    hreg.2 (A[h₀ - 1]'(by omega)) (List.getElem_mem (by omega))
  have hAh₀m1_bound : A[h₀ - 1]'(by omega) ≤ 3 * (p - h₀) - 1 := by
    have hle : A[h₀ - 1]'(by omega) ≤ 3 * (p - h₀) := by omega
    by_contra hgt; push_neg at hgt
    exact hreg_h₀m1 ⟨p - h₀, by omega⟩
  have hAm1_ge_h₀ : A[h₀ - 1]'(by omega) ≥ A[h₀]'(by omega) :=
    List.pairwise_iff_getElem.mp hflat.1.1 (h₀ - 1) h₀ (by omega) (by omega) (by omega)
  have hAh₀_le_np : A[h₀]'(by omega) ≤ 3 * (p - h₀) - 1 := by omega
  -- Unfold tryHardInsertion
  unfold tryHardInsertion
  have hguard : ¬(h₀ ≥ p ∨ h₀ > A.length) := by omega
  simp only [hguard, ↓reduceIte]
  set newPart := 3 * (p - h₀)
  set raised := List.map (fun x : ℕ × ℕ => if x.2 < h₀ then x.1 + 3 else x.1) A.zipIdx
  set result := List.insertIdx raised h₀ newPart
  -- Properties of raised
  have hraised_len : raised.length = A.length := by simp [raised]
  have hresult_len : result.length = A.length + 1 := by
    simp only [result, List.length_insertIdx]; split <;> omega
  have hraised_lt_val (i : ℕ) (hi : i < h₀) :
      raised[i]'(by omega) = A[i]'(by omega) + 3 := by
    simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
    simp only [Nat.zero_add]; exact if_pos hi
  have hraised_ge_val (i : ℕ) (hi : ¬(i < h₀)) (hilen : i < A.length) :
      raised[i]'(by omega) = A[i]'hilen := by
    simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
    simp only [Nat.zero_add]; exact if_neg hi
  -- Properties of result
  have hresult_before (i : ℕ) (hi : i < h₀) :
      result[i]'(by omega) = A[i]'(by omega) + 3 := by
    simp only [result, List.getElem_insertIdx, show i < h₀ from hi]
    exact hraised_lt_val i hi
  have hresult_at : result[h₀]'(by omega) = newPart := by
    simp only [result, List.getElem_insertIdx, show ¬(h₀ < h₀) from Nat.lt_irrefl h₀]
    simp
  have hresult_after (i : ℕ) (hi : i > h₀) (hilen : i < result.length) :
      result[i]'hilen = A[i - 1]'(by omega) := by
    simp only [result, List.getElem_insertIdx, show ¬(i < h₀) from by omega,
               show ¬(i = h₀) from by omega]
    exact hraised_ge_val (i - 1) (by omega) (by omega)
  -- Key gap bounds
  have hgap_right : newPart - A[h₀]'(by omega) < 3 := by
    show 3 * (p - h₀) - A[h₀]'(by omega) < 3; omega
  have hgap_left : A[h₀ - 1]'(by omega) + 3 - newPart < 3 := by
    show A[h₀ - 1]'(by omega) + 3 - (3 * (p - h₀)) < 3; omega
  have hnewPart_pos : 0 < newPart := by show 0 < 3 * (p - h₀); omega
  -- PART A: isThreeFlatBool result = true
  have hflat_result : isThreeFlatBool result = true := by
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    obtain ⟨⟨hpw, hpos_all⟩, hgaps_orig, hlast⟩ := hflat
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- Pairwise (· ≥ ·)
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      by_cases hi_lt : i < h₀
      · by_cases hj_lt : j < h₀
        · rw [hresult_before i hi_lt, hresult_before j hj_lt]
          have := List.pairwise_iff_getElem.mp hpw i j (by omega) (by omega) hij; omega
        · by_cases hj_eq : j = h₀
          · have hresult_j : result[j]'hj = newPart := by
              have heq : result[j]'hj = result[h₀]'(by omega) := by congr 1
              rw [heq, hresult_at]
            rw [hresult_before i hi_lt, hresult_j]
            have hge_prev : A[i]'(by omega) ≥ A[h₀ - 1]'(by omega) := by
              rcases Nat.lt_or_ge (i + 1) h₀ with h | h
              · exact List.pairwise_iff_getElem.mp hpw i (h₀ - 1) (by omega) (by omega) (by omega)
              · have heq : i = h₀ - 1 := by omega
                have : A[i]'(by omega) = A[h₀ - 1]'(by omega) := by congr 1
                omega
            show A[i]'(by omega) + 3 ≥ newPart; show A[i]'(by omega) + 3 ≥ 3 * (p - h₀); omega
          · rw [hresult_before i hi_lt, hresult_after j (by omega) hj]
            have := List.pairwise_iff_getElem.mp hpw i (j - 1) (by omega) (by omega) (by omega)
            omega
      · by_cases hi_eq : i = h₀
        · have hresult_i : result[i]'hi = newPart := by
            have heq : result[i]'hi = result[h₀]'(by omega) := by congr 1
            rw [heq, hresult_at]
          rw [hresult_i, hresult_after j (by omega) hj]
          have : A[j - 1]'(by omega) ≤ A[h₀]'(by omega) := by
            rcases Nat.lt_or_ge (j - 1) (h₀ + 1) with h | h
            · have heq : j - 1 = h₀ := by omega
              have : A[j - 1]'(by omega) = A[h₀]'(by omega) := by congr 1
              omega
            · exact List.pairwise_iff_getElem.mp hpw h₀ (j - 1) (by omega) (by omega) (by omega)
          show newPart ≥ A[j - 1]'(by omega); show 3 * (p - h₀) ≥ A[j - 1]'(by omega); omega
        · rw [hresult_after i (by omega) hi, hresult_after j (by omega) hj]
          exact List.pairwise_iff_getElem.mp hpw (i - 1) (j - 1) (by omega) (by omega) (by omega)
    · -- All positive
      intro x hx; simp only [result] at hx
      rw [List.mem_insertIdx (by omega : h₀ ≤ raised.length)] at hx
      rcases hx with rfl | hx
      · exact hnewPart_pos
      · simp only [raised, List.mem_map] at hx
        obtain ⟨⟨a, k⟩, hmem, hx_eq⟩ := hx
        have ha_mem : a ∈ A := List.fst_mem_of_mem_zipIdx hmem
        split_ifs at hx_eq with hlt
        · have : 0 < a := hpos_all a ha_mem; omega
        · exact hx_eq ▸ hpos_all a ha_mem
    · -- Gaps < 3
      intro i hi; rw [hresult_len] at hi
      rw [getElem!_pos result i (by omega), getElem!_pos result (i + 1) (by omega)]
      by_cases hi_lt : i + 1 < h₀
      · rw [hresult_before i (by omega), hresult_before (i + 1) hi_lt]
        have := hgaps_orig i (by omega : i + 1 < A.length); omega
      · by_cases hi_eq : i + 1 = h₀
        · have hi_is : i = h₀ - 1 := by omega
          have hi1_is : i + 1 = h₀ := hi_eq
          have hri : result[i]'(by omega) = result[h₀ - 1]'(by omega) := by congr 1
          have hri1 : result[i + 1]'(by omega) = result[h₀]'(by omega) := by congr 1
          rw [hri, hri1, hresult_before (h₀ - 1) (by omega), hresult_at]
          exact hgap_left
        · by_cases hi_eq2 : i = h₀
          · have hri : result[i]'(by omega) = result[h₀]'(by omega) := by congr 1
            have hri1 : result[i + 1]'(by omega) = result[h₀ + 1]'(by omega) := by
              congr 1; omega
            rw [hri, hri1, hresult_at, hresult_after (h₀ + 1) (by omega) (by omega)]
            show newPart - A[h₀ + 1 - 1]'(by omega) < 3
            have : A[h₀ + 1 - 1]'(by omega) = A[h₀]'(by omega) := by congr 1
            rw [this]; exact hgap_right
          · rw [hresult_after i (by omega) (by omega),
                 hresult_after (i + 1) (by omega) (by omega)]
            have hgi := hgaps_orig (i - 1) (by omega : (i - 1) + 1 < A.length)
            have h1 : i + 1 - 1 = (i - 1) + 1 := by omega
            have h2 : A[i + 1 - 1]'(by omega) = A[(i - 1) + 1]'(by omega) := by congr 1
            rw [h2]; exact hgi
    · -- Last element < 3
      have hne : result ≠ [] := by intro he; simp [he] at hresult_len
      have hAne : A ≠ [] := by intro h; simp [h] at hAlen_pos
      rw [List.getLast?_eq_some_getLast hne]; simp only [decide_eq_true_eq]
      have hlast_val : result.getLast hne = A.getLast hAne := by
        rw [List.getLast_eq_getElem, List.getLast_eq_getElem,
            hresult_after (result.length - 1) (by omega) (by omega)]
        congr 1; omega
      rw [hlast_val]; exact hlast hAne
  -- PART B: isFlatRemovableBool result h₀ = false
  have hnotRemov : isFlatRemovableBool result h₀ = false := by
    suffices hkey : isThreeFlatBool (result.eraseIdx h₀) = false by
      simp only [isFlatRemovableBool, hkey, Bool.and_false]
    have herase : result.eraseIdx h₀ = raised := by
      simp only [result]; exact List.eraseIdx_insertIdx_self newPart
    rw [herase]
    -- The gap at h₀-1 in raised is (A[h₀-1]+3) - A[h₀] ≥ 3, so NOT 3-flat
    simp only [isThreeFlatBool, Bool.and_eq_false_iff]
    left; right
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have hfail := hall (h₀ - 1) (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at hfail
    have heq : h₀ - 1 + 1 = h₀ := by omega
    rw [heq] at hfail
    rw [getElem!_pos raised (h₀ - 1) (show h₀ - 1 < raised.length by omega),
        getElem!_pos raised h₀ (show h₀ < raised.length by omega)] at hfail
    rw [hraised_lt_val (h₀ - 1) (by omega), hraised_ge_val h₀ (by omega) (by omega)] at hfail
    omega
  -- Combine
  simp only [hflat_result, hnotRemov, Bool.not_false, Bool.true_and, ↓reduceIte,
             Option.isSome_some]

/-- Variant of `findHardInsertion_succeeds_of_all_small` that uses a height invariant
instead of `IsThreeRegular`. The height invariant says that every multiple of 3 in A
has height (value + 3*index) ≥ 3*p. This implies at the crossing point h₀-1,
the element is not a multiple of 3, giving the same strict bound. -/
private lemma findHardInsertion_succeeds_of_height_inv (A : List ℕ) (p : ℕ)
    (hflat : IsThreeFlat A) (hp : 0 < p) (hp_le : p ≤ A.length)
    (hsafe : ∀ (i : Fin A.length), A[i.val] + 3 * (i.val + 1) ≤ 3 * p + 3 * A.length)
    (hsmall : ∀ (i : ℕ) (hi : i < A.length), A[i]'hi ≤ 3 * (p - 1))
    (h_height : ∀ (i : ℕ) (hi : i < A.length), 3 ∣ A[i]'hi → A[i]'hi + 3 * i ≥ 3 * p) :
    (findHardInsertion A p).isSome := by
  -- Same crossing argument as findHardInsertion_succeeds_of_all_small
  suffices ∃ h₀, h₀ < p ∧ h₀ ≤ A.length ∧ (tryHardInsertion A p h₀).isSome by
    obtain ⟨h₀, hlt, hle, htry⟩ := this
    exact findHardInsertion_isSome_of_try_at A p h₀ 0 hlt hle htry (Nat.zero_le _)
  have hAlen_pos : 0 < A.length := by omega
  have hnotP0 : A[0]'hAlen_pos < 3 * p - 2 := by
    have := hsmall 0 hAlen_pos; omega
  have hPpm1 : A[p-1]'(by omega) ≥ 3 * (p - (p-1)) - 2 := by
    have := hflat.1.2 (A[p-1]'(by omega)) (List.getElem_mem ..); omega
  have hp_ge2 : p ≥ 2 := by
    have hA0_pos := hflat.1.2 (A[0]'hAlen_pos) (List.getElem_mem hAlen_pos)
    omega
  have hfind : ∃ (h₀ : ℕ) (_ : h₀ < A.length), h₀ ≥ 1 ∧ h₀ < p ∧
      A[h₀]'(by omega) ≥ 3 * (p - h₀) - 2 ∧
      A[h₀ - 1]'(by omega) < 3 * (p - h₀) + 1 := by
    suffices aux : ∀ k : ℕ, (hk : k < p) → k ≥ 1 → A[k]'(by omega) ≥ 3 * (p - k) - 2 →
        ∃ (h₀ : ℕ) (_ : h₀ < A.length), h₀ ≥ 1 ∧ h₀ < p ∧
          A[h₀]'(by omega) ≥ 3 * (p - h₀) - 2 ∧
          A[h₀ - 1]'(by omega) < 3 * (p - h₀) + 1 by
      exact aux (p - 1) (by omega) (by omega) hPpm1
    intro k hk
    induction k with
    | zero => intro hge; omega
    | succ n ih =>
      intro hn_ge hPn
      by_cases hn_zero : n = 0
      · subst hn_zero
        refine ⟨1, by omega, by omega, by omega, hPn, ?_⟩
        show A[1 - 1]'(by omega) < 3 * (p - 1) + 1
        simp only [show 1 - 1 = 0 from rfl]; omega
      · by_cases hPprev : A[n]'(by omega) ≥ 3 * (p - n) - 2
        · exact ih (by omega) (by omega) hPprev
        · push_neg at hPprev
          refine ⟨n + 1, by omega, by omega, hk, hPn, ?_⟩
          show A[n + 1 - 1]'(by omega) < 3 * (p - (n + 1)) + 1
          have heq : n + 1 - 1 = n := by omega
          simp only [heq]; omega
  obtain ⟨h₀, hh₀_lt_len, hh₀_ge, hh₀_lt, hAh₀_ge, hAh₀m1_lt⟩ := hfind
  refine ⟨h₀, hh₀_lt, by omega, ?_⟩
  -- Key: use height invariant instead of hreg
  have hreg_h₀m1 : ¬(3 ∣ A[h₀ - 1]'(by omega)) := by
    intro hdvd
    have hh := h_height (h₀ - 1) (by omega) hdvd
    -- height(h₀-1) = A[h₀-1] + 3*(h₀-1) ≥ 3*p (from h_height)
    -- But A[h₀-1] < 3*(p-h₀)+1, so height < 3*(p-h₀)+1 + 3*(h₀-1) = 3*p - 2 < 3*p
    have hbound : A[h₀ - 1]'(by omega) ≤ 3 * (p - h₀) := by omega
    omega
  have hAh₀m1_bound : A[h₀ - 1]'(by omega) ≤ 3 * (p - h₀) - 1 := by
    have hle : A[h₀ - 1]'(by omega) ≤ 3 * (p - h₀) := by omega
    by_contra hgt; push_neg at hgt
    exact hreg_h₀m1 ⟨p - h₀, by omega⟩
  have hAm1_ge_h₀ : A[h₀ - 1]'(by omega) ≥ A[h₀]'(by omega) :=
    List.pairwise_iff_getElem.mp hflat.1.1 (h₀ - 1) h₀ (by omega) (by omega) (by omega)
  have hAh₀_le_np : A[h₀]'(by omega) ≤ 3 * (p - h₀) - 1 := by omega
  -- The rest is identical to findHardInsertion_succeeds_of_all_small from this point
  unfold tryHardInsertion
  have hguard : ¬(h₀ ≥ p ∨ h₀ > A.length) := by omega
  simp only [hguard, ↓reduceIte]
  set newPart := 3 * (p - h₀)
  set raised := List.map (fun x : ℕ × ℕ => if x.2 < h₀ then x.1 + 3 else x.1) A.zipIdx
  set result := List.insertIdx raised h₀ newPart
  have hraised_len : raised.length = A.length := by simp [raised]
  have hresult_len : result.length = A.length + 1 := by
    simp only [result, List.length_insertIdx]; split <;> omega
  have hraised_lt_val (i : ℕ) (hi : i < h₀) :
      raised[i]'(by omega) = A[i]'(by omega) + 3 := by
    simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
    simp only [Nat.zero_add]; exact if_pos hi
  have hraised_ge_val (i : ℕ) (hi : ¬(i < h₀)) (hilen : i < A.length) :
      raised[i]'(by omega) = A[i]'hilen := by
    simp only [raised]; rw [List.getElem_map, List.getElem_zipIdx]
    simp only [Nat.zero_add]; exact if_neg hi
  have hresult_before (i : ℕ) (hi : i < h₀) :
      result[i]'(by omega) = A[i]'(by omega) + 3 := by
    simp only [result, List.getElem_insertIdx, show i < h₀ from hi]
    exact hraised_lt_val i hi
  have hresult_at : result[h₀]'(by omega) = newPart := by
    simp only [result, List.getElem_insertIdx, show ¬(h₀ < h₀) from Nat.lt_irrefl h₀]
    simp
  have hresult_after (i : ℕ) (hi : i > h₀) (hilen : i < result.length) :
      result[i]'hilen = A[i - 1]'(by omega) := by
    simp only [result, List.getElem_insertIdx, show ¬(i < h₀) from by omega,
               show ¬(i = h₀) from by omega]
    exact hraised_ge_val (i - 1) (by omega) (by omega)
  have hgap_right : newPart - A[h₀]'(by omega) < 3 := by
    show 3 * (p - h₀) - A[h₀]'(by omega) < 3; omega
  have hgap_left : A[h₀ - 1]'(by omega) + 3 - newPart < 3 := by
    show A[h₀ - 1]'(by omega) + 3 - (3 * (p - h₀)) < 3; omega
  have hnewPart_pos : 0 < newPart := by show 0 < 3 * (p - h₀); omega
  -- PART A: isThreeFlatBool result = true
  have hflat_result : isThreeFlatBool result = true := by
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    obtain ⟨⟨hpw, hpos_all⟩, hgaps_orig, hlast⟩ := hflat
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- Pairwise (· ≥ ·)
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      by_cases hi_lt : i < h₀
      · by_cases hj_lt : j < h₀
        · rw [hresult_before i hi_lt, hresult_before j hj_lt]
          have := List.pairwise_iff_getElem.mp hpw i j (by omega) (by omega) hij; omega
        · by_cases hj_eq : j = h₀
          · have hresult_j : result[j]'hj = newPart := by
              have heq : result[j]'hj = result[h₀]'(by omega) := by congr 1
              rw [heq, hresult_at]
            rw [hresult_before i hi_lt, hresult_j]
            have hge_prev : A[i]'(by omega) ≥ A[h₀ - 1]'(by omega) := by
              rcases Nat.lt_or_ge (i + 1) h₀ with h | h
              · exact List.pairwise_iff_getElem.mp hpw i (h₀ - 1) (by omega) (by omega) (by omega)
              · have heq : i = h₀ - 1 := by omega
                have : A[i]'(by omega) = A[h₀ - 1]'(by omega) := by congr 1
                omega
            show A[i]'(by omega) + 3 ≥ newPart; show A[i]'(by omega) + 3 ≥ 3 * (p - h₀); omega
          · rw [hresult_before i hi_lt, hresult_after j (by omega) hj]
            have := List.pairwise_iff_getElem.mp hpw i (j - 1) (by omega) (by omega) (by omega)
            omega
      · by_cases hi_eq : i = h₀
        · have hresult_i : result[i]'hi = newPart := by
            have heq : result[i]'hi = result[h₀]'(by omega) := by congr 1
            rw [heq, hresult_at]
          rw [hresult_i, hresult_after j (by omega) hj]
          have : A[j - 1]'(by omega) ≤ A[h₀]'(by omega) := by
            rcases Nat.lt_or_ge (j - 1) (h₀ + 1) with h | h
            · have heq : j - 1 = h₀ := by omega
              have : A[j - 1]'(by omega) = A[h₀]'(by omega) := by congr 1
              omega
            · exact List.pairwise_iff_getElem.mp hpw h₀ (j - 1) (by omega) (by omega) (by omega)
          show newPart ≥ A[j - 1]'(by omega); show 3 * (p - h₀) ≥ A[j - 1]'(by omega); omega
        · rw [hresult_after i (by omega) hi, hresult_after j (by omega) hj]
          exact List.pairwise_iff_getElem.mp hpw (i - 1) (j - 1) (by omega) (by omega) (by omega)
    · -- All positive
      intro x hx; simp only [result] at hx
      rw [List.mem_insertIdx (by omega : h₀ ≤ raised.length)] at hx
      rcases hx with rfl | hx
      · exact hnewPart_pos
      · simp only [raised, List.mem_map] at hx
        obtain ⟨⟨val, idx⟩, hmem, heq⟩ := hx
        simp only [] at heq
        split at heq
        · have := hpos_all val (List.fst_mem_of_mem_zipIdx hmem); omega
        · have := hpos_all val (List.fst_mem_of_mem_zipIdx hmem); omega
    · -- Gaps < 3
      intro i hi
      rw [getElem!_pos result i (by omega), getElem!_pos result (i+1) (by omega)]
      by_cases hi_lt_h0m1 : i + 1 < h₀
      · -- Both in "raised" region
        rw [hresult_before i (by omega), hresult_before (i+1) hi_lt_h0m1]
        have := hgaps_orig i (by omega)
        omega
      · by_cases hi_eq_h0m1 : i + 1 = h₀
        · -- Gap from raised[h₀-1] to newPart
          have hi_eq : i = h₀ - 1 := by omega
          have hri : result[i]'(by omega) = A[h₀ - 1]'(by omega) + 3 := by
            rw [show result[i]'(by omega) = result[h₀ - 1]'(by omega) from by congr 1]
            exact hresult_before (h₀ - 1) (by omega)
          have hri1 : result[i+1]'(by omega) = newPart := by
            have heq : result[i+1]'(by omega) = result[h₀]'(by omega) := by congr 1
            rw [heq, hresult_at]
          rw [hri, hri1]
          show A[h₀ - 1]'(by omega) + 3 - (3 * (p - h₀)) < 3
          omega
        · by_cases hi_eq_h0 : i = h₀
          · -- Gap from newPart to A[h₀]
            have hri : result[i]'(by omega) = newPart := by
              have : result[i]'(by omega) = result[h₀]'(by omega) := by congr 1
              rw [this, hresult_at]
            have hri1 : result[i+1]'(by omega) = A[h₀]'(by omega) := by
              rw [hresult_after (i+1) (by omega) (by omega)]; congr 1
            rw [hri, hri1]
            exact hgap_right
          · -- Both in "original" region (after h₀)
            have hi_gt : i > h₀ := by omega
            -- result[i] = A[i-1], result[i+1] = A[(i+1)-1] = A[i]
            have hval_i : result[i]'(by omega) = A[i - 1]'(by omega) :=
              hresult_after i (by omega) (by omega)
            have hval_i1 : result[i + 1]'(by omega) = A[i + 1 - 1]'(by omega) :=
              hresult_after (i + 1) (by omega) (by omega)
            rw [hval_i, hval_i1]
            have hgap := hgaps_orig (i - 1) (by omega)
            have hget_eq : A[i - 1 + 1]'(by omega) = A[i + 1 - 1]'(by omega) := by congr 1; omega
            rw [← hget_eq]; exact hgap
    · -- Last element < 3
      have hne : result ≠ [] := by intro he; simp [he] at hresult_len
      have hAne : A ≠ [] := by intro h; simp [h] at hAlen_pos
      rw [List.getLast?_eq_some_getLast hne]; simp only [decide_eq_true_eq]
      have hlast_val : result.getLast hne = A.getLast hAne := by
        rw [List.getLast_eq_getElem, List.getLast_eq_getElem,
            hresult_after (result.length - 1) (by omega) (by omega)]
        congr 1; omega
      rw [hlast_val]; exact hlast hAne
  -- PART B: ¬ isFlatRemovableBool result h₀
  have hnotRemov : isFlatRemovableBool result h₀ = false := by
    suffices hkey : isThreeFlatBool (result.eraseIdx h₀) = false by
      simp only [isFlatRemovableBool, hkey, Bool.and_false]
    have herase : result.eraseIdx h₀ = raised := by
      simp only [result]; exact List.eraseIdx_insertIdx_self newPart
    rw [herase]
    -- The gap at h₀-1 in raised is (A[h₀-1]+3) - A[h₀] ≥ 3, so NOT 3-flat
    simp only [isThreeFlatBool, Bool.and_eq_false_iff]
    left; right
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have hfail := hall (h₀ - 1) (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at hfail
    have heq : h₀ - 1 + 1 = h₀ := by omega
    rw [heq] at hfail
    rw [getElem!_pos raised (h₀ - 1) (show h₀ - 1 < raised.length by omega),
        getElem!_pos raised h₀ (show h₀ < raised.length by omega)] at hfail
    rw [hraised_lt_val (h₀ - 1) (by omega), hraised_ge_val h₀ (by omega) (by omega)] at hfail
    omega
  -- Combine
  simp only [hflat_result, hnotRemov, Bool.not_false, Bool.true_and, ↓reduceIte,
             Option.isSome_some]

theorem performInsertion_always_succeeds (A : List ℕ) (p : ℕ) (hp : 0 < p)
    (hflat : IsThreeFlat A)
    (hreg : IsThreeRegular A)
    (hp_le : p ≤ A.length)
    (hsafe : ∀ (i : Fin A.length), A[i.val] + 3 * (i.val + 1) ≤ 3 * p + 3 * A.length) :
    (findHardInsertion A p).isSome ∨ (tryEasyInsertion A p).isSome := by
  have hAne : A ≠ [] := by intro h; simp [h] at hp_le; omega
  have hAlen_pos : 0 < A.length := by cases A with | nil => simp at hAne | cons _ _ => simp
  set pos := (A.takeWhile (· ≥ 3*p)).length with hpos_def
  by_cases hpos_pos : pos > 0
  · -- Case 1: pos > 0 → easy insertion succeeds
    exact Or.inr (tryEasyInsertion_succeeds_of_pos_pos' A p hflat hp hpos_pos hAne)
  · -- Case 2: pos = 0
    push_neg at hpos_pos
    have hpos_zero : pos = 0 := by omega
    -- All elements < 3*p (since nothing in takeWhile prefix)
    have hA0_lt : A[0]'hAlen_pos < 3 * p := by
      have := not_in_takeWhile_lt' A p 0 (by omega) hAlen_pos
      exact this
    by_cases hlarge : A[0]'hAlen_pos > 3 * (p - 1)
    · -- Case 2a: A[0] > 3*(p-1) → easy insertion at pos=0 succeeds
      exact Or.inr (tryEasyInsertion_succeeds_of_pos_zero_large A p hflat hp hpos_zero hAlen_pos hlarge)
    · -- Case 2b: A[0] ≤ 3*(p-1) → hard insertion succeeds
      push_neg at hlarge
      have hsmall : ∀ (i : ℕ) (hi : i < A.length), A[i]'hi ≤ 3 * (p - 1) := by
        intro i hi
        have hpw := List.pairwise_iff_getElem.mp hflat.1.1
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · exact hlarge
        · have hge : A[0]'hAlen_pos ≥ A[i]'hi :=
            hpw 0 i hAlen_pos hi (by omega)
          omega
      exact Or.inl (findHardInsertion_succeeds_of_all_small A p hflat hreg hp hp_le hsafe hsmall)

/-- Trajectory safety: at each step k along the trajectory starting from a 3-flat 3-regular
partition with sorted positive bounded ν, the labeled insertion succeeds (either hard or easy).

The proof uses the height invariant: every multiple of 3 in the intermediate state has
"height" (value + 3*position) ≥ 3*ν[k], which prevents the ★ case at the crossing point
of the hard insertion argument. See .search_memory/exist_insertion/META.md for full analysis. -/
private lemma trajectory_insertion_succeeds
    (A_init : List Labeled) (ν : List ℕ) (k : ℕ)
    (hk : k < ν.length)
    (hA_flat : IsThreeFlat (forget A_init))
    (hA_reg : IsThreeRegular (forget A_init))
    (hA_clean : ∀ x ∈ A_init, x.origin = none)
    (hν_sort : ν.Pairwise (· ≥ ·))
    (hν_pos : ∀ x ∈ ν, 0 < x)
    (h_bound : ∀ x ∈ ν, x ≤ (forget A_init).length) :
    let Ak := (ν.take k).foldl (fun acc x => performInsertionLabeled acc x) A_init
    findHardInsertionLabeled Ak ν[k] ≠ none ∨
    tryEasyInsertionLabeled Ak ν[k] ≠ none := by
  intro Ak
  -- Convert to unlabeled via forget commutation
  suffices h_unl : (findHardInsertion (forget Ak) ν[k]).isSome ∨
      (tryEasyInsertion (forget Ak) ν[k]).isSome by
    rcases h_unl with h1 | h2
    · left; intro hcontra
      have hfind := forget_findHardInsertionLabeled Ak ν[k] 0
      simp only [hcontra, Option.map_none] at hfind
      rw [← hfind] at h1
      simp at h1
    · right; intro hcontra
      have heasy := forget_tryEasyInsertionLabeled Ak ν[k]
      simp only [hcontra, Option.map_none] at heasy
      rw [← heasy] at h2
      simp at h2
  -- Key properties of the trajectory state
  have hAk_flat : IsThreeFlat (forget Ak) := by
    simp only [Ak]
    suffices gen : ∀ (m : ℕ), m ≤ k →
        IsThreeFlat (forget ((ν.take m).foldl (fun acc x => performInsertionLabeled acc x) A_init)) by
      exact gen k (le_refl k)
    intro m hm
    induction m with
    | zero => simpa [List.take, List.foldl]
    | succ n ih =>
      have hfold_step : (ν.take (n + 1)).foldl (fun acc x => performInsertionLabeled acc x) A_init =
          performInsertionLabeled ((ν.take n).foldl (fun acc x => performInsertionLabeled acc x) A_init)
            (ν[n]'(by omega)) := by
        simp_rw [List.take_succ_eq_append_getElem (show n < ν.length from by omega),
          List.foldl_append, List.foldl]
      rw [hfold_step, forget_performInsertionLabeled]
      exact performInsertion_preserves_flat' _ _ (ih (by omega))
  have hpk_pos : 0 < ν[k] := hν_pos _ (List.getElem_mem hk)
  have hpk_le : ν[k] ≤ (forget Ak).length := by
    have hbound := h_bound _ (List.getElem_mem hk)
    suffices (forget A_init).length ≤ (forget Ak).length from by omega
    simp only [Ak]
    suffices gen : ∀ (m : ℕ), m ≤ k →
        (forget A_init).length ≤ (forget ((ν.take m).foldl (fun acc x => performInsertionLabeled acc x) A_init)).length by
      exact gen k (le_refl k)
    intro m hm
    induction m with
    | zero => simp [List.take, List.foldl]
    | succ n ih =>
      have hfold_step : (ν.take (n + 1)).foldl (fun acc x => performInsertionLabeled acc x) A_init =
          performInsertionLabeled ((ν.take n).foldl (fun acc x => performInsertionLabeled acc x) A_init)
            (ν[n]'(by omega)) := by
        simp_rw [List.take_succ_eq_append_getElem (show n < ν.length from by omega),
          List.foldl_append, List.foldl]
      rw [hfold_step, forget_performInsertionLabeled]
      have := performInsertion_length_ge (forget ((ν.take n).foldl (fun acc x => performInsertionLabeled acc x) A_init)) (ν[n]'(by omega))
      have ih_val := ih (by omega)
      omega
  -- Safety condition (automatic for 3-flat partitions with p ≥ 1)
  have hsafe : ∀ (i : Fin (forget Ak).length),
      (forget Ak)[i.val] + 3 * (i.val + 1) ≤ 3 * ν[k] + 3 * (forget Ak).length := by
    intro ⟨i, hi⟩; simp only []
    -- For 3-flat of length r: A[i] < 3*(r-i), so A[i]+3*(i+1) < 3*r+3 ≤ 3*ν[k]+3*r
    suffices (forget Ak)[i] + 3 * i < 3 * (forget Ak).length from by omega
    obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := hAk_flat
    have hne : forget Ak ≠ [] := by
      intro h; have : (forget Ak).length = 0 := by rw [h]; simp
      omega
    -- Prove by induction from the end: A[j] + 3*j < 3*length
    suffices ∀ j (hj : j < (forget Ak).length), (forget Ak)[j] + 3 * j < 3 * (forget Ak).length by
      exact this i hi
    intro j hj
    -- Strong induction: induct on distance from end (length - 1 - j)
    suffices gen : ∀ d, d = (forget Ak).length - 1 - j →
        (forget Ak)[j] + 3 * j < 3 * (forget Ak).length from
      gen _ rfl
    intro d
    induction d generalizing j with
    | zero =>
      intro hd
      have hj_last : j = (forget Ak).length - 1 := by omega
      have hlast_val := hlast hne
      have heq : (forget Ak)[j]'hj = (forget Ak).getLast hne := by
        rw [List.getLast_eq_getElem]; congr 1
      have hj_lt3 : (forget Ak)[j]'hj < 3 := heq ▸ hlast_val
      omega
    | succ m ihm =>
      intro hd
      have hj_next : j + 1 < (forget Ak).length := by omega
      have hgap := hgaps j (by omega)
      have h_next := ihm (j + 1) hj_next (by omega)
      -- hgap : (forget Ak)[j] - (forget Ak)[j+1] < 3
      -- h_next : (forget Ak)[j+1] + 3 * (j+1) < 3 * (forget Ak).length
      -- Goal : (forget Ak)[j] + 3 * j < 3 * (forget Ak).length
      set vj := (forget Ak)[j]'hj
      set vj1 := (forget Ak)[j + 1]'hj_next
      omega
  -- Main case split: k = 0 uses regularity directly; k ≥ 1 uses height invariant
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0: forget Ak = forget A_init, which is 3-regular
    have hAk_eq : Ak = A_init := by simp [Ak, List.take, List.foldl]
    have hAk_forget : forget Ak = forget A_init := by rw [hAk_eq]
    have hpk_le' : ν[0] ≤ (forget A_init).length := by rw [← hAk_forget]; exact hpk_le
    have hsafe' : ∀ (i : Fin (forget A_init).length),
        (forget A_init)[i.val] + 3 * (i.val + 1) ≤ 3 * ν[0] + 3 * (forget A_init).length := by
      intro ⟨i, hi⟩
      have hi' : i < (forget Ak).length := hAk_forget ▸ hi
      have h := hsafe ⟨i, hi'⟩
      simp only [hAk_forget] at h
      exact h
    exact performInsertion_always_succeeds (forget A_init) ν[0] hpk_pos hA_flat hA_reg
      hpk_le' hsafe'
  · -- k ≥ 1: Use the height invariant to bypass IsThreeRegular.
    -- Same structure as performInsertion_always_succeeds
    have hAne : forget Ak ≠ [] := by
      intro h
      have hlen0 : (forget Ak).length = 0 := by rw [h]; simp
      have := hpk_le; omega
    have hAlen_pos : 0 < (forget Ak).length := List.length_pos_iff.mpr hAne
    set pos := ((forget Ak).takeWhile (· ≥ 3 * ν[k])).length with hpos_def
    by_cases hpos_pos : pos > 0
    · -- Case 1: pos > 0 → easy insertion succeeds
      exact Or.inr (tryEasyInsertion_succeeds_of_pos_pos' (forget Ak) ν[k] hAk_flat hpk_pos
        hpos_pos hAne)
    · -- Case 2: pos = 0
      push_neg at hpos_pos
      have hpos_zero : pos = 0 := by omega
      have hA0_lt : (forget Ak)[0]'hAlen_pos < 3 * ν[k] := by
        have := not_in_takeWhile_lt' (forget Ak) ν[k] 0 (by omega) hAlen_pos
        exact this
      by_cases hlarge : (forget Ak)[0]'hAlen_pos > 3 * (ν[k] - 1)
      · -- Case 2a: easy insertion at pos=0
        exact Or.inr (tryEasyInsertion_succeeds_of_pos_zero_large (forget Ak) ν[k] hAk_flat
          hpk_pos hpos_zero hAlen_pos hlarge)
      · -- Case 2b: hard insertion via height invariant
        push_neg at hlarge
        have hsmall : ∀ (i : ℕ) (hi : i < (forget Ak).length),
            (forget Ak)[i]'hi ≤ 3 * (ν[k] - 1) := by
          intro i hi
          have hpw := List.pairwise_iff_getElem.mp hAk_flat.1.1
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · exact hlarge
          · have hge : (forget Ak)[0]'hAlen_pos ≥ (forget Ak)[i]'hi :=
              hpw 0 i hAlen_pos hi (by omega)
            omega
        -- Height invariant: every mult-of-3 in (forget Ak) has height ≥ 3*ν[k]
        have h_height : ∀ (i : ℕ) (hi : i < (forget Ak).length),
            3 ∣ (forget Ak)[i]'hi → (forget Ak)[i]'hi + 3 * i ≥ 3 * ν[k] := by
          -- We prove: for all j ≤ k, after j insertions, every mult-3 element has
          -- height ≥ 3*ν[k]. Since ν is sorted decreasing, each insertion of size
          -- ν[j'] (j' < k) satisfies ν[j'] ≥ ν[k], so inserted elements have
          -- height ≥ 3*ν[j'] ≥ 3*ν[k], and existing elements have height increased.
          suffices gen : ∀ (j : ℕ) (hj : j ≤ k),
              ∀ (i : ℕ) (hi : i < (forget ((ν.take j).foldl (fun acc x => performInsertionLabeled acc x) A_init)).length),
                3 ∣ (forget ((ν.take j).foldl (fun acc x => performInsertionLabeled acc x) A_init))[i]'hi →
                (forget ((ν.take j).foldl (fun acc x => performInsertionLabeled acc x) A_init))[i]'hi + 3 * i ≥ 3 * ν[k] by
            exact gen k (le_refl k)
          intro j hj
          induction j with
          | zero =>
            -- Base case: A₀ = A_init, which has no multiples of 3
            simp only [List.take, List.foldl]
            intro i hi hdvd
            exfalso
            have hmem : (forget A_init)[i]'hi ∈ forget A_init := List.getElem_mem hi
            exact hA_reg.2 _ hmem hdvd
          | succ n ih =>
            -- Inductive step: A_{n+1} = performInsertionLabeled A_n ν[n]
            have hn_lt : n < ν.length := by omega
            have hfold_step : (ν.take (n + 1)).foldl (fun acc x => performInsertionLabeled acc x) A_init =
                performInsertionLabeled ((ν.take n).foldl (fun acc x => performInsertionLabeled acc x) A_init)
                  (ν[n]'hn_lt) := by
              simp_rw [List.take_succ_eq_append_getElem (show n < ν.length from hn_lt),
                List.foldl_append, List.foldl]
            simp only [hfold_step, forget_performInsertionLabeled]
            -- The IH gives us the height invariant for A_n
            have ih_An := ih (by omega : n ≤ k)
            -- ν[n] ≥ ν[k] because ν is sorted decreasing and n < k
            have hνn_ge_νk : ν[n]'hn_lt ≥ ν[k] := by
              have := List.pairwise_iff_getElem.mp hν_sort n k hn_lt hk (by omega)
              exact this
            -- Apply the sub-lemma: performInsertion preserves height invariant
            exact performInsertion_preserves_height_inv
              (forget ((ν.take n).foldl (fun acc x => performInsertionLabeled acc x) A_init))
              (ν[n]'hn_lt) (ν[k]) ih_An hνn_ge_νk
        exact Or.inl (findHardInsertion_succeeds_of_height_inv (forget Ak) ν[k] hAk_flat
          hpk_pos hpk_le hsafe hsmall h_height)

/-- Variant of `labels_union_eq_nu` with the correct hypotheses: instead of requiring
the insertion to succeed for ALL `B`, we maintain the invariant that intermediate
states are 3-flat (via `performInsertion_preserves_flat`) and use
`performInsertion_always_succeeds` to show insertions succeed at each step.

This avoids the universally-quantified `h_all_succeed` hypothesis of `labels_union_eq_nu`
which is unprovable (counterexample: B=[], p=1, both insertions fail because [3] is not 3-flat). -/
private lemma labels_union_perm_nu
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat   : IsThreeFlat (forget A_init))
    (hA_reg    : IsThreeRegular (forget A_init))
    (hA_clean  : ∀ x ∈ A_init, x.origin = none)
    (hν_sort   : ν.Pairwise (· ≥ ·))
    (hν_pos    : ∀ x ∈ ν, 0 < x)
    (h_bound   : ∀ x ∈ ν, x ≤ (forget A_init).length) :
    (easyLabels (processInsertionsLabeled ν A_init) ++
     hardLabels (processInsertionsLabeled ν A_init)).mergeSort (· ≥ ·) =
      ν.mergeSort (· ≥ ·) := by
  -- Reduce mergeSort equality to permutation
  suffices hperm : (easyLabels (processInsertionsLabeled ν A_init) ++
      hardLabels (processInsertionsLabeled ν A_init)).Perm ν by
    have htrans : ∀ (a b c : ℕ), decide (a ≥ b) = true → decide (b ≥ c) = true →
        decide (a ≥ c) = true := by simp; omega
    have htotal : ∀ (a b : ℕ), (decide (a ≥ b) || decide (b ≥ a)) = true := by simp; omega
    have h1 := List.pairwise_mergeSort htrans htotal
      (easyLabels (processInsertionsLabeled ν A_init) ++
       hardLabels (processInsertionsLabeled ν A_init))
    have h2 := List.pairwise_mergeSort htrans htotal ν
    have hperm' : ((easyLabels (processInsertionsLabeled ν A_init) ++
        hardLabels (processInsertionsLabeled ν A_init)).mergeSort (· ≥ ·)).Perm
        (ν.mergeSort (· ≥ ·)) :=
      (List.mergeSort_perm _ _).trans (hperm.trans (List.mergeSort_perm _ _).symm)
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by simp at *; omega)
      h1 h2 hperm'
  have h_trajectory_succeeds :
      (easyLabels (processInsertionsLabeled ν A_init) ++
       hardLabels (processInsertionsLabeled ν A_init)).Perm
        (ν ++ (easyLabels A_init ++ hardLabels A_init)) := by
    -- Key structural lemma: for any ν' and A, if all insertions along the
    -- specific trajectory succeed, then the label permutation holds.
    suffices gen : ∀ (ν' : List ℕ) (A : List Labeled),
        (∀ (k : ℕ) (hk : k < ν'.length),
          let Ak := (ν'.take k).foldl (fun acc x => performInsertionLabeled acc x) A
          findHardInsertionLabeled Ak ν'[k] ≠ none ∨
          tryEasyInsertionLabeled Ak ν'[k] ≠ none) →
        (easyLabels (processInsertionsLabeled ν' A) ++
         hardLabels (processInsertionsLabeled ν' A)).Perm
          (ν' ++ (easyLabels A ++ hardLabels A)) by
      apply gen
      -- Use trajectory_insertion_succeeds for each step
      exact fun k hk => trajectory_insertion_succeeds A_init ν k hk
        hA_flat hA_reg hA_clean hν_sort hν_pos h_bound
    -- Structural induction on ν'
    intro ν'
    induction ν' with
    | nil => intro A _; simp [processInsertionsLabeled]
    | cons p' rest ih =>
      intro A h_succ
      simp only [processInsertionsLabeled]
      have h0 : findHardInsertionLabeled A p' ≠ none ∨
          tryEasyInsertionLabeled A p' ≠ none := by
        have := h_succ 0 (by simp)
        simpa [List.take, List.foldl] using this
      have h_perm := labels_perm_of_perform A p' h0
      have h_rest : ∀ (k : ℕ) (hk : k < rest.length),
          let Ak := (rest.take k).foldl (fun acc x => performInsertionLabeled acc x)
            (performInsertionLabeled A p')
          findHardInsertionLabeled Ak rest[k] ≠ none ∨
          tryEasyInsertionLabeled Ak rest[k] ≠ none := by
        intro k hk
        have h := h_succ (k + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.foldl_cons] at h
        exact h
      have step := ih (performInsertionLabeled A p') h_rest
      exact step.trans ((List.Perm.append_left _ h_perm).trans List.perm_middle)
  have hnil : easyLabels A_init ++ hardLabels A_init = [] := by
    have he : easyLabels A_init = [] := by
      unfold easyLabels; rw [List.filterMap_eq_nil_iff]
      intro x hx; have := hA_clean x hx; simp [this]
    have hh : hardLabels A_init = [] := by
      unfold hardLabels; rw [List.filterMap_eq_nil_iff]
      intro x hx; have := hA_clean x hx; simp [this]
    rw [he, hh]; rfl
  rw [hnil, List.append_nil] at h_trajectory_succeeds; exact h_trajectory_succeeds

private lemma scanFromLargest_rec_prefix (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ) :
    rec.IsPrefix (scanFromLargest fuel A idx rec).2 := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromLargest]
  | succ n ih =>
    simp only [scanFromLargest]
    split
    · exact List.prefix_rfl
    · split
      · exact (List.prefix_append rec [A[idx]! / 3 + idx]).trans (ih _ _ _)
      · exact ih _ _ _

private lemma diff_append_prefix_eq (suffix l2 : List ℕ) : (l2 ++ suffix).diff l2 = suffix := by
  induction l2 with
  | nil => simp
  | cons a t ih => simp [List.diff_cons]; exact ih

/-- **Master theorem, Direction R**: applying the forward deletion
algorithm to the unlabeled image of `processInsertionsLabeled ν A_init`
recovers `ν` (up to sorted order).

CLOSED PROOF: chain R-A + R-C + `labels_union_eq_nu`.  The agent's job
is only to close the structural assembly of `mergeSort (recS2 ++ Δ)`
into `mergeSort (recS2) ++ mergeSort Δ` (up to permutation), substitute
via the three invariants, and conclude.  ~30 lines. -/
theorem labeled_round_trip_R
    (A_init : List Labeled) (ν : List ℕ)
    (hA_flat   : IsThreeFlat (forget A_init))
    (hA_reg    : IsThreeRegular (forget A_init))
    (hA_clean  : ∀ x ∈ A_init, x.origin = none)
    (hν_sort   : ν.Pairwise (· ≥ ·))
    (hν_pos    : ∀ x ∈ ν, 0 < x)
    (h_bound   : ∀ x ∈ ν, x ≤ (forget A_init).length) :
    let labeled := processInsertionsLabeled ν A_init
    let unl     := forget labeled
    let (afterS2, recS2) := scanFromSmallest (unl.length + 1) unl 0 []
    let recS3 := (scanFromLargest (afterS2.length + 1) afterS2 0 recS2).2
    recS3.mergeSort (· ≥ ·) = ν.mergeSort (· ≥ ·) := by
  have hA := s2_extracts_easy_labels A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hC := s3_records_hard_labels A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos
  have hUnion := labels_union_perm_nu A_init ν hA_flat hA_reg hA_clean hν_sort hν_pos h_bound
  -- Introduce the let bindings and set up abbreviations
  set labeled := processInsertionsLabeled ν A_init with labeled_def
  set unl := forget labeled with unl_def
  set sfs := scanFromSmallest (unl.length + 1) unl 0 [] with sfs_def
  set afterS2 := sfs.1 with afterS2_def
  set recS2 := sfs.2 with recS2_def
  set recS3 := (scanFromLargest (afterS2.length + 1) afterS2 0 recS2).2 with recS3_def
  -- Reduce let-bindings in hypotheses
  have hA' : recS2.mergeSort (· ≥ ·) = (easyLabels labeled).mergeSort (· ≥ ·) := hA
  have hC' : (List.diff recS3 recS2).mergeSort (· ≥ ·) =
      (hardLabels labeled).mergeSort (· ≥ ·) := by
    have := hC
    simp only [] at this
    exact this
  -- The main argument
  show recS3.mergeSort (· ≥ ·) = ν.mergeSort (· ≥ ·)
  have hprefix : recS2.IsPrefix recS3 := by
    rw [recS3_def]; exact scanFromLargest_rec_prefix _ _ _ _
  obtain ⟨suffix, hsuf⟩ := hprefix
  have hdiff : recS3.diff recS2 = suffix := by
    rw [← hsuf]; exact diff_append_prefix_eq suffix recS2
  rw [hdiff] at hC'
  have pA : recS2.Perm (easyLabels labeled) :=
    (List.mergeSort_perm recS2 _).symm.trans (hA' ▸ (List.mergeSort_perm (easyLabels labeled) _))
  have pC : suffix.Perm (hardLabels labeled) :=
    (List.mergeSort_perm suffix _).symm.trans (hC' ▸ (List.mergeSort_perm (hardLabels labeled) _))
  have pcat : (recS2 ++ suffix).Perm (easyLabels labeled ++ hardLabels labeled) := pA.append pC
  rw [show recS3 = recS2 ++ suffix from hsuf.symm]
  have sorted1 := List.pairwise_mergeSort (α := ℕ) (le := (· ≥ ·))
    (by intro a b c hab hbc; simp_all; omega) (by intro a b; simp; omega) (recS2 ++ suffix)
  have sorted2 := List.pairwise_mergeSort (α := ℕ) (le := (· ≥ ·))
    (by intro a b c hab hbc; simp_all; omega) (by intro a b; simp; omega)
    (easyLabels labeled ++ hardLabels labeled)
  have p12 : ((recS2 ++ suffix).mergeSort (· ≥ ·)).Perm
      ((easyLabels labeled ++ hardLabels labeled).mergeSort (· ≥ ·)) :=
    (List.mergeSort_perm _ _).trans (pcat.trans (List.mergeSort_perm _ _).symm)
  exact (List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => by simp at *; omega) sorted1 sorted2 p12).trans hUnion

end Labeled

/-! ## Correctness theorems for residueCore -/

private lemma residueCore_ne_nil_aux (v : List ℕ) (hv : v ≠ []) : residueCore v ≠ [] := by
  match v with
  | [] => exact absurd rfl hv
  | [a] => simp [residueCore]
  | a :: b :: rest =>
    simp [residueCore]
    split <;> simp

theorem residueCore_isThreeFlat (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2) :
    IsThreeFlat (residueCore v) := by
  induction v with
  | nil =>
    refine ⟨⟨List.Pairwise.nil, ?_⟩, ?_, ?_⟩
    · intro x hx; simp [residueCore] at hx
    · intro i hi; simp [residueCore] at hi
    · intro h; exact absurd rfl h
  | cons w rest ih =>
    have hvr : ∀ x ∈ rest, x = 1 ∨ x = 2 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hw : w = 1 ∨ w = 2 := hv w List.mem_cons_self
    have ih' := ih hvr
    cases rest with
    | nil =>
      show IsThreeFlat (residueCore [w])
      simp only [residueCore]
      refine ⟨⟨List.pairwise_singleton _ _, ?_⟩, ?_, ?_⟩
      · intro x hx
        simp at hx
        rcases hw with rfl | rfl
        · omega
        · omega
      · intro i hi; simp at hi
      · intro h
        show w < 3
        rcases hw with rfl | rfl <;> norm_num
    | cons w' rest' =>
      have htne : residueCore (w' :: rest') ≠ [] := residueCore_ne_nil_aux _ (by simp)
      obtain ⟨c_next, rest_tail, htail_eq⟩ : ∃ a t, residueCore (w' :: rest') = a :: t := by
        match h : residueCore (w' :: rest') with
        | [] => exact absurd h htne
        | a :: t => exact ⟨a, t, rfl⟩
      obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := ih'
      set c_i : ℕ := (if c_next % 3 == w % 3 then c_next
                 else if (c_next + 1) % 3 == w % 3 then c_next + 1
                 else c_next + 2) with hc_i_def
      have hRC : residueCore (w :: w' :: rest') = c_i :: (c_next :: rest_tail) := by
        show (match residueCore (w' :: rest') with
              | [] => [w]
              | c_next :: _ =>
                let c_i := if c_next % 3 == w % 3 then c_next
                  else if (c_next + 1) % 3 == w % 3 then c_next + 1
                  else c_next + 2
                c_i :: (residueCore (w' :: rest'))) = c_i :: (c_next :: rest_tail)
        rw [htail_eq]
      have hci_bounds : c_i = c_next ∨ c_i = c_next + 1 ∨ c_i = c_next + 2 := by
        rw [hc_i_def]
        by_cases h1 : c_next % 3 == w % 3
        · simp [h1]
        · by_cases h2 : (c_next + 1) % 3 == w % 3
          · simp [h1, h2]
          · simp [h1, h2]
      have hci_ge : c_next ≤ c_i := by rcases hci_bounds with h | h | h <;> omega
      have hci_diff : c_i - c_next < 3 := by rcases hci_bounds with h | h | h <;> omega
      rw [hRC]
      have hc_next_pos : 0 < c_next := by
        apply hpos
        rw [htail_eq]; exact List.mem_cons_self
      have hci_pos : 0 < c_i := lt_of_lt_of_le hc_next_pos hci_ge
      have hpw_tail : (c_next :: rest_tail).Pairwise (· ≥ ·) := htail_eq ▸ hpw
      have hpos_tail : ∀ x ∈ (c_next :: rest_tail), 0 < x := fun x hx => hpos x (htail_eq ▸ hx)
      have hgaps_tail : ∀ (i : ℕ) (hi : i + 1 < (c_next :: rest_tail).length),
          (c_next :: rest_tail)[i] - (c_next :: rest_tail)[i+1] < 3 := by
        intro i hi
        have hi2 : i + 1 < (residueCore (w' :: rest')).length := htail_eq ▸ hi
        have := hgaps i hi2
        have e0 : (residueCore (w' :: rest'))[i] = (c_next :: rest_tail)[i] := by
          exact List.getElem_of_eq htail_eq _
        have e1 : (residueCore (w' :: rest'))[i+1] = (c_next :: rest_tail)[i+1] := by
          exact List.getElem_of_eq htail_eq _
        rw [e0, e1] at this
        exact this
      have hlast_tail : (c_next :: rest_tail).getLast (by simp) < 3 := by
        have h1 := hlast htne
        have heq : (residueCore (w' :: rest')).getLast htne = (c_next :: rest_tail).getLast (by simp) := by
          congr 1
        rw [heq] at h1
        exact h1
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpw_tail⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hci_ge
        · have := List.rel_of_pairwise_cons hpw_tail hy'
          exact le_trans this hci_ge
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hci_pos
        · exact hpos_tail x hx'
      · intro i hi
        match i, hi with
        | 0, hi =>
          show c_i - c_next < 3
          exact hci_diff
        | i+1, hi =>
          have hi' : i + 1 < (c_next :: rest_tail).length := by
            simp only [List.length_cons] at hi ⊢; omega
          exact hgaps_tail i hi'
      · intro _
        exact hlast_tail

theorem residueCore_isThreeRegular (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2) :
    IsThreeRegular (residueCore v) := by
  obtain ⟨hpos, _, _⟩ := residueCore_isThreeFlat v hv
  refine ⟨hpos, ?_⟩
  clear hpos
  -- Prove the "no part divisible by 3" claim by induction on v
  induction v with
  | nil =>
    intro x hx
    simp [residueCore] at hx
  | cons w rest ih =>
    have hvr : ∀ x ∈ rest, x = 1 ∨ x = 2 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hw : w = 1 ∨ w = 2 := hv w List.mem_cons_self
    have ih_no_div : ∀ x ∈ residueCore rest, ¬ 3 ∣ x := by
      have ⟨_, hgap, hlast⟩ := residueCore_isThreeFlat rest hvr
      exact ih hvr hgap hlast
    cases rest with
    | nil =>
      -- residueCore [w] = [w], w ∈ {1,2}, so ¬ 3 ∣ w
      intro x hx
      show ¬ 3 ∣ x
      simp [residueCore] at hx
      subst hx
      rcases hw with rfl | rfl <;> decide
    | cons w' rest' =>
      have htne : residueCore (w' :: rest') ≠ [] := residueCore_ne_nil_aux _ (by simp)
      obtain ⟨c_next, rest_tail, htail_eq⟩ : ∃ a t, residueCore (w' :: rest') = a :: t := by
        match h : residueCore (w' :: rest') with
        | [] => exact absurd h htne
        | a :: t => exact ⟨a, t, rfl⟩
      set c_i : ℕ := (if c_next % 3 == w % 3 then c_next
                 else if (c_next + 1) % 3 == w % 3 then c_next + 1
                 else c_next + 2) with hc_i_def
      have hRC : residueCore (w :: w' :: rest') = c_i :: (c_next :: rest_tail) := by
        show (match residueCore (w' :: rest') with
              | [] => [w]
              | c_next :: _ =>
                let c_i := if c_next % 3 == w % 3 then c_next
                  else if (c_next + 1) % 3 == w % 3 then c_next + 1
                  else c_next + 2
                c_i :: (residueCore (w' :: rest'))) = c_i :: (c_next :: rest_tail)
        rw [htail_eq]
      -- Show c_i % 3 = w % 3
      have hci_mod : c_i % 3 = w % 3 := by
        rw [hc_i_def]
        by_cases h1 : c_next % 3 == w % 3
        · simp [h1]
          exact (beq_iff_eq.mp h1 : (c_next % 3 : ℕ) = w % 3)
        · by_cases h2 : (c_next + 1) % 3 == w % 3
          · simp [h1, h2]
            exact (beq_iff_eq.mp h2 : ((c_next + 1) % 3 : ℕ) = w % 3)
          · simp [h1, h2]
            have hh1 : c_next % 3 ≠ w % 3 := by simpa using h1
            have hh2 : (c_next + 1) % 3 ≠ w % 3 := by simpa using h2
            have hwlt : w % 3 < 3 := Nat.mod_lt _ (by norm_num)
            have hclt : c_next % 3 < 3 := Nat.mod_lt _ (by norm_num)
            omega
      have hci_not_div : ¬ 3 ∣ c_i := by
        rw [Nat.dvd_iff_mod_eq_zero, hci_mod]
        rcases hw with rfl | rfl <;> decide
      have htail_no_div : ∀ x ∈ (c_next :: rest_tail), ¬ 3 ∣ x := by
        intro x hx
        apply ih_no_div
        rw [htail_eq]
        exact hx
      intro x hx
      rw [hRC] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hci_not_div
      · exact htail_no_div x hx'

-- Helper: map (· % 3) on residueCore gives back v
private lemma residueCore_map_mod3 (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2) :
    List.map (· % 3) (residueCore v) = v := by
  induction v with
  | nil => simp [residueCore]
  | cons w rest ih =>
    have hvr : ∀ x ∈ rest, x = 1 ∨ x = 2 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hw : w = 1 ∨ w = 2 := hv w List.mem_cons_self
    cases rest with
    | nil =>
      simp [residueCore]
      rcases hw with rfl | rfl <;> decide
    | cons w' rest' =>
      have htne : residueCore (w' :: rest') ≠ [] := residueCore_ne_nil_aux _ (by simp)
      obtain ⟨c_next, rest_tail, htail_eq⟩ : ∃ a t, residueCore (w' :: rest') = a :: t := by
        match h : residueCore (w' :: rest') with
        | [] => exact absurd h htne
        | a :: t => exact ⟨a, t, rfl⟩
      set c_i : ℕ := (if c_next % 3 == w % 3 then c_next
                 else if (c_next + 1) % 3 == w % 3 then c_next + 1
                 else c_next + 2)
      have hRC : residueCore (w :: w' :: rest') = c_i :: (c_next :: rest_tail) := by
        show (match residueCore (w' :: rest') with
              | [] => [w]
              | c_next :: _ =>
                let c_i := if c_next % 3 == w % 3 then c_next
                  else if (c_next + 1) % 3 == w % 3 then c_next + 1
                  else c_next + 2
                c_i :: (residueCore (w' :: rest'))) = c_i :: (c_next :: rest_tail)
        rw [htail_eq]
      have hci_mod : c_i % 3 = w % 3 := by
        show (if c_next % 3 == w % 3 then c_next
              else if (c_next + 1) % 3 == w % 3 then c_next + 1
              else c_next + 2) % 3 = w % 3
        by_cases h1 : c_next % 3 == w % 3
        · simp [h1]
          exact (beq_iff_eq.mp h1 : (c_next % 3 : ℕ) = w % 3)
        · by_cases h2 : (c_next + 1) % 3 == w % 3
          · simp [h1, h2]
            exact (beq_iff_eq.mp h2 : ((c_next + 1) % 3 : ℕ) = w % 3)
          · simp [h1, h2]
            have hh1 : c_next % 3 ≠ w % 3 := by simpa using h1
            have hh2 : (c_next + 1) % 3 ≠ w % 3 := by simpa using h2
            have hwlt : w % 3 < 3 := Nat.mod_lt _ (by norm_num)
            have hclt : c_next % 3 < 3 := Nat.mod_lt _ (by norm_num)
            omega
      have hw_mod : w % 3 = w := by rcases hw with rfl | rfl <;> decide
      rw [hRC, List.map_cons]
      congr 1
      · rw [hci_mod, hw_mod]
      · have : List.map (· % 3) (residueCore (w' :: rest')) = w' :: rest' := ih hvr
        rw [htail_eq] at this
        exact this

theorem residueCore_residues (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2) :
    nonzeroResSeq (residueCore v) = v := by
  have hreg := residueCore_isThreeRegular v hv
  obtain ⟨_, hndvd⟩ := hreg
  unfold nonzeroResSeq
  have hfilt : (residueCore v).filter (fun x => ¬(x % 3 == 0)) = residueCore v := by
    rw [List.filter_eq_self]
    intro x hx
    simp [beq_iff_eq]
    exact fun heq => hndvd x hx (Nat.dvd_of_mod_eq_zero heq)
  rw [hfilt]
  exact residueCore_map_mod3 v hv

theorem residueCore_length (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2) :
    (residueCore v).length = v.length := by
  induction v with
  | nil => simp [residueCore]
  | cons w rest ih =>
    have hvr : ∀ x ∈ rest, x = 1 ∨ x = 2 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    cases rest with
    | nil => simp [residueCore]
    | cons w' rest' =>
      have hvr' : ∀ x ∈ w' :: rest', x = 1 ∨ x = 2 := hvr
      have ih' := ih hvr'
      have htne : residueCore (w' :: rest') ≠ [] := residueCore_ne_nil_aux _ (by simp)
      obtain ⟨c_next, rest_tail, htail_eq⟩ : ∃ a t, residueCore (w' :: rest') = a :: t := by
        match h : residueCore (w' :: rest') with
        | [] => exact absurd h htne
        | a :: t => exact ⟨a, t, rfl⟩
      show (residueCore (w :: w' :: rest')).length = (w :: w' :: rest').length
      have hRC : residueCore (w :: w' :: rest') =
        (if c_next % 3 == w % 3 then c_next
         else if (c_next + 1) % 3 == w % 3 then c_next + 1
         else c_next + 2) :: (c_next :: rest_tail) := by
        show (match residueCore (w' :: rest') with
              | [] => [w]
              | c_next :: _ =>
                let c_i := if c_next % 3 == w % 3 then c_next
                  else if (c_next + 1) % 3 == w % 3 then c_next + 1
                  else c_next + 2
                c_i :: (residueCore (w' :: rest'))) = _
        rw [htail_eq]
      rw [hRC]
      simp only [List.length_cons]
      have hlen : (c_next :: rest_tail).length = (w' :: rest').length := by
        rw [← htail_eq]; exact ih'
      simp only [List.length_cons] at hlen
      omega

private lemma nonzeroResSeq_of_threeRegular' (l : List ℕ) (hreg : IsThreeRegular l) :
    nonzeroResSeq l = l.map (· % 3) := by
  unfold nonzeroResSeq; congr 1
  apply List.filter_eq_self.mpr
  intro x hx; simp [beq_iff_eq]
  exact fun heq => hreg.2 x hx (Nat.dvd_of_mod_eq_zero heq)

private lemma isThreeFlat_tail' (a : ℕ) (l : List ℕ) (h : IsThreeFlat (a :: l)) : IsThreeFlat l := by
  obtain ⟨⟨hpw, hpos⟩, hgaps, hlast⟩ := h
  cases l with
  | nil =>
    exact ⟨⟨List.Pairwise.nil, fun x hx => by simp at hx⟩, fun i hi => by simp at hi, fun h => absurd rfl h⟩
  | cons b rest =>
    refine ⟨⟨(List.pairwise_cons.mp hpw).2, fun x hx => hpos x (List.mem_cons_of_mem _ hx)⟩, ?_, ?_⟩
    · intro i hi
      have hi' : (i + 1) + 1 < (a :: b :: rest).length := by simp at hi ⊢; omega
      have := hgaps (i + 1) hi'; simp only [List.getElem_cons_succ] at this; exact this
    · intro _; exact hlast (by simp)

private lemma isThreeRegular_tail' (a : ℕ) (l : List ℕ) (h : IsThreeRegular (a :: l)) : IsThreeRegular l :=
  ⟨⟨(List.pairwise_cons.mp h.1.1).2, fun x hx => h.1.2 x (List.mem_cons_of_mem _ hx)⟩,
   fun x hx => h.2 x (List.mem_cons_of_mem _ hx)⟩

private lemma unique_in_triple (n a v : ℕ) (ha_ge : a ≥ n) (ha_lt : a - n < 3)
    (ha_mod : a % 3 = v % 3) :
    a = (if n % 3 == v % 3 then n
         else if (n + 1) % 3 == v % 3 then n + 1
         else n + 2) := by
  have ha_range : a = n ∨ a = n + 1 ∨ a = n + 2 := by omega
  by_cases h1 : n % 3 == v % 3
  · simp [h1]
    have hn_mod : n % 3 = v % 3 := beq_iff_eq.mp h1
    rcases ha_range with rfl | rfl | rfl <;> omega
  · by_cases h2 : (n + 1) % 3 == v % 3
    · simp [h1, h2]
      have hn1_mod : (n + 1) % 3 = v % 3 := beq_iff_eq.mp h2
      have hn_mod : n % 3 ≠ v % 3 := by simpa using h1
      rcases ha_range with rfl | rfl | rfl <;> omega
    · simp [h1, h2]
      have hn_mod : n % 3 ≠ v % 3 := by simpa using h1
      have hn1_mod : (n + 1) % 3 ≠ v % 3 := by simpa using h2
      rcases ha_range with rfl | rfl | rfl <;> omega

theorem residueCore_unique (v : List ℕ) (hv : ∀ x ∈ v, x = 1 ∨ x = 2)
    (l : List ℕ) (hflat : IsThreeFlat l) (hreg : IsThreeRegular l)
    (hres : nonzeroResSeq l = v) :
    l = residueCore v := by
  induction v generalizing l with
  | nil =>
    have hfilt := nonzeroResSeq_of_threeRegular' l hreg
    rw [hfilt] at hres
    cases l with | nil => rfl | cons _ _ => simp at hres
  | cons w rest ih =>
    have hw : w = 1 ∨ w = 2 := hv w (by simp)
    have hvr : ∀ x ∈ rest, x = 1 ∨ x = 2 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hne : l ≠ [] := by intro h; subst h; simp [nonzeroResSeq] at hres
    obtain ⟨a, l', hl_eq⟩ := List.exists_cons_of_ne_nil hne
    subst hl_eq
    have hfilt := nonzeroResSeq_of_threeRegular' (a :: l') hreg
    rw [hfilt] at hres; simp only [List.map_cons] at hres
    have ha_mod : a % 3 = w := (List.cons_eq_cons.mp hres).1
    have hrest_eq : List.map (· % 3) l' = rest := (List.cons_eq_cons.mp hres).2
    have hflat' : IsThreeFlat l' := isThreeFlat_tail' a l' hflat
    have hreg' : IsThreeRegular l' := isThreeRegular_tail' a l' hreg
    have hres' : nonzeroResSeq l' = rest := by
      rw [nonzeroResSeq_of_threeRegular' l' hreg']; exact hrest_eq
    have ih' := ih hvr l' hflat' hreg' hres'
    cases rest with
    | nil =>
      simp [residueCore] at ih' ⊢
      refine ⟨?_, ih'⟩
      have ha_lt3 : a < 3 := by
        have hflat_al : IsThreeFlat [a] := by rw [← ih']; exact hflat
        exact hflat_al.2.2 (by simp)
      linarith [ha_mod, Nat.mod_eq_of_lt ha_lt3]
    | cons w' rest' =>
      have htne : residueCore (w' :: rest') ≠ [] := residueCore_ne_nil_aux _ (by simp)
      have hl'_ne : l' ≠ [] := by intro h; rw [h] at ih'; exact absurd ih'.symm htne
      obtain ⟨c_next, rest_tail, htail_eq⟩ : ∃ c t, residueCore (w' :: rest') = c :: t := by
        match h : residueCore (w' :: rest') with
        | [] => exact absurd h htne
        | c :: t => exact ⟨c, t, rfl⟩
      have hl'_eq : l' = c_next :: rest_tail := by rw [ih', htail_eq]
      have hRC : residueCore (w :: w' :: rest') =
        (if c_next % 3 == w % 3 then c_next
         else if (c_next + 1) % 3 == w % 3 then c_next + 1
         else c_next + 2) :: (c_next :: rest_tail) := by
        show (match residueCore (w' :: rest') with
              | [] => [w]
              | c_next :: _ =>
                let c_i := if c_next % 3 == w % 3 then c_next
                  else if (c_next + 1) % 3 == w % 3 then c_next + 1
                  else c_next + 2
                c_i :: (residueCore (w' :: rest'))) = _
        rw [htail_eq]
      suffices ha_eq : a = (if c_next % 3 == w % 3 then c_next
         else if (c_next + 1) % 3 == w % 3 then c_next + 1
         else c_next + 2) by
        rw [hl'_eq]; conv_lhs => rw [ha_eq]; exact hRC.symm
      have ha_ge_cn : a ≥ c_next := by
        have hpw := hflat.1.1; rw [List.pairwise_cons] at hpw
        exact hpw.1 c_next (by rw [hl'_eq]; simp)
      have ha_diff_lt3 : a - c_next < 3 := by
        have hflat_sub := hflat
        rw [show a :: l' = a :: c_next :: rest_tail from by rw [hl'_eq]] at hflat_sub
        have hlen : 0 + 1 < (a :: c_next :: rest_tail).length := by simp
        have hgap := hflat_sub.2.1 0 hlen
        simpa using hgap
      have hw_mod : w % 3 = w := by rcases hw with rfl | rfl <;> simp
      exact unique_in_triple c_next a w ha_ge_cn ha_diff_lt3 (by rw [ha_mod, hw_mod])

/-! ## Correctness of conjugate -/

private lemma sorted_filter_ge_length_iff (l : List ℕ) (hsorted : l.Pairwise (· ≥ ·))
    (i : ℕ) (hi : i < l.length) (k : ℕ) :
    (l.filter (fun x => decide (x ≥ k))).length ≥ i + 1 ↔ l[i] ≥ k := by
  induction l generalizing i k with
  | nil => simp at hi
  | cons a rest ih =>
    rw [List.pairwise_cons] at hsorted
    obtain ⟨hge_rest, hsorted_rest⟩ := hsorted
    simp only [List.filter_cons]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      constructor
      · intro h; by_contra hlt; push_neg at hlt
        have hnd : ¬(a ≥ k) := by omega
        simp only [decide_eq_true_eq, hnd, ↓reduceIte] at h
        have hemp : rest.filter (fun x => decide (x ≥ k)) = [] := by
          simp only [List.filter_eq_nil_iff]
          intro x hx; simp only [decide_eq_true_eq, not_le]
          have := hge_rest x hx; omega
        simp [hemp] at h
      · intro hge; simp [show decide (a ≥ k) = true from by simp [hge]]
    | succ i' =>
      simp only [List.getElem_cons_succ]
      have hi' : i' < rest.length := by simp at hi; omega
      split_ifs with hak
      · simp only [List.length_cons]; constructor
        · intro h; exact (ih hsorted_rest i' hi' k).mp (by omega)
        · intro h; have := (ih hsorted_rest i' hi' k).mpr h; omega
      · simp only [decide_eq_true_eq, not_le] at hak; constructor
        · intro h; exfalso
          have : rest.filter (fun x => decide (x ≥ k)) = [] := by
            simp only [List.filter_eq_nil_iff]
            intro x hx; simp only [decide_eq_true_eq, not_le]
            have := hge_rest x hx; omega
          simp [this] at h
        · intro h; exfalso
          have : a ≥ rest[i'] := hge_rest (rest[i']) (List.getElem_mem hi'); omega

private lemma filter_sublist_of_imp (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x, q x = true → p x = true) :
    (l.filter q).Sublist (l.filter p) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons]
    split_ifs with hq hp hp
    · exact List.Sublist.cons₂ _ ih
    · exfalso; exact hp (h a hq)
    · exact ih.cons _
    · exact ih

private lemma conj_pairwise (a : ℕ) (rest : List ℕ) :
    (conjugate (a :: rest)).Pairwise (· ≥ ·) := by
  show ((List.range a).map (fun j => ((a :: rest).filter (fun x => decide (x ≥ j + 1))).length)).Pairwise (· ≥ ·)
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map, List.length_range] at hi hj
  simp only [List.getElem_map, List.getElem_range]
  exact (filter_sublist_of_imp _ _ _ (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega)).length_le

namespace Labeled

/-- **Companion theorem** for `phi3Inverse_sortedRec_eq_nu`-style chains.
Specializes the R round-trip to the `phi3Inverse` setting. -/
theorem phi3Inverse_sortedRec_eq_nu_via_labels
    (l : List ℕ) :
    let A_init := residueCore (nonzeroResSeq l)
    let q := (List.range A_init.length).map (fun i =>
      ((l[i]?.getD 0) - (A_init[i]?.getD 0)) / 3)
    let ν := conjugate q
    sortedRec (phi3Inverse l) = ν := by
  intro A_init q ν
  -- Key auxiliary facts
  have hv_12 : ∀ x ∈ nonzeroResSeq l, x = 1 ∨ x = 2 := nonzeroResSeq_in_one_two l
  have hA_flat : IsThreeFlat A_init := residueCore_isThreeFlat _ hv_12
  have hA_reg : IsThreeRegular A_init := residueCore_isThreeRegular _ hv_12
  -- q.length = A_init.length
  have hq_len : q.length = A_init.length := by simp [q]
  -- ν is sorted (Pairwise ≥) via conj_pairwise
  have hν_sort : ν.Pairwise (· ≥ ·) := by
    show (conjugate q).Pairwise (· ≥ ·)
    cases hq : q with
    | nil => simp [conjugate]
    | cons a rest => exact conj_pairwise a rest
  -- ν has all positive parts (from conjugate structure)
  have hν_pos : ∀ x ∈ ν, 0 < x := by
    show ∀ x ∈ conjugate q, 0 < x
    intro x hx
    cases hq : q with
    | nil => simp [conjugate, hq] at hx
    | cons a rest =>
      rw [show conjugate q = conjugate (a :: rest) from by rw [hq]] at hx
      simp only [conjugate, List.mem_map, List.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      apply Nat.pos_of_ne_zero; intro h
      have hfilter_empty := List.eq_nil_of_length_eq_zero h
      have ha_mem : a ∈ (a :: rest).filter (fun x => x ≥ j + 1) := by
        simp [List.mem_filter]; omega
      rw [hfilter_empty] at ha_mem; simp at ha_mem
  -- Bound: each part of ν ≤ A_init.length
  have h_bound : ∀ x ∈ ν, x ≤ A_init.length := by
    show ∀ x ∈ conjugate q, x ≤ A_init.length
    intro x hx
    cases hq : q with
    | nil => simp [conjugate, hq] at hx
    | cons a rest =>
      rw [show conjugate q = conjugate (a :: rest) from by rw [hq]] at hx
      simp only [conjugate, List.mem_map, List.mem_range] at hx
      obtain ⟨j, _, rfl⟩ := hx
      have hfilt := List.length_filter_le (fun x => x ≥ j + 1) (a :: rest)
      have hlen_eq : (a :: rest).length = A_init.length := by
        have : q = a :: rest := hq
        rw [← this]; exact hq_len
      omega
  -- Apply labeled_round_trip_R with A_init := embed A_init
  have hRoundTrip := labeled_round_trip_R (embed A_init) ν
    (by rw [forget_embed]; exact hA_flat)
    (by rw [forget_embed]; exact hA_reg)
    (embed_no_label A_init)
    hν_sort
    hν_pos
    (by rw [forget_embed]; exact h_bound)
  -- Key: forget (processInsertionsLabeled ν (embed A_init)) = processInsertions ν A_init
  have hunl : forget (processInsertionsLabeled ν (embed A_init)) = processInsertions ν A_init := by
    rw [forget_processInsertionsLabeled, forget_embed]
  -- Connect sortedRec (phi3Inverse l) to the conclusion of labeled_round_trip_R
  -- phi3Inverse l = processInsertions ν A_init (definitionally)
  -- sortedRec (processInsertions ν A_init) unfolds to the same expression as hRoundTrip's LHS
  show sortedRec (processInsertions ν A_init) = ν
  conv_lhs => rw [show processInsertions ν A_init =
      forget (processInsertionsLabeled ν (embed A_init)) from hunl.symm]
  simp only [sortedRec]
  -- Now goal is: (let ... := scanFromSmallest ...; ...).mergeSort (· ≥ ·) = ν
  -- which is exactly hRoundTrip composed with mergeSort_eq_self
  have hν_ms : ν.mergeSort (· ≥ ·) = ν := List.mergeSort_eq_self (· ≥ ·) hν_sort
  exact hRoundTrip.trans hν_ms

end Labeled

private lemma eq_of_ge_iff' (n m : ℕ) (h : ∀ k : ℕ, n ≥ k + 1 ↔ m ≥ k + 1) : n = m := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := (h n).mpr (by omega); omega
  · have := (h m).mp (by omega); omega

theorem conjugate_involution (l : List ℕ) (hl : IsPositivePartition l) :
    conjugate (conjugate l) = l := by
  obtain ⟨hsorted, hpos⟩ := hl
  cases l with
  | nil => simp [conjugate]
  | cons a rest =>
    have ha_pos : 0 < a := hpos a (by simp)
    set cl := conjugate (a :: rest)
    have hcl_len : cl.length = a := by simp [cl, conjugate]
    have hcl_sorted : cl.Pairwise (· ≥ ·) := conj_pairwise a rest
    have hcl_ne : cl ≠ [] := by intro h; simp [h] at hcl_len; omega
    have hcl_getElem : ∀ (j : ℕ) (hj : j < a),
        cl[j]'(by omega) = ((a :: rest).filter (fun x => decide (x ≥ j + 1))).length := by
      intro j hj
      show (conjugate (a :: rest))[j]'_ = _
      simp [conjugate, List.getElem_map, List.getElem_range, hj]
    have hcl0 : cl[0]'(by omega) = (a :: rest).length := by
      rw [hcl_getElem 0 ha_pos]
      congr 1; apply List.filter_eq_self.mpr
      intro x hx; simp; exact hpos x hx
    obtain ⟨hd, tl, hcl_eq⟩ := List.exists_cons_of_ne_nil hcl_ne
    have hhd : hd = (a :: rest).length := by
      have h0 : cl[0]'(by omega) = hd := by simp [hcl_eq]
      linarith [hcl0]
    show conjugate cl = a :: rest
    have hconj_cl : conjugate cl = (List.range hd).map
        (fun i => (cl.filter (fun x => decide (x ≥ i + 1))).length) := by
      show conjugate cl = _; rw [hcl_eq]; rfl
    rw [hconj_cl, hhd]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range]
      apply eq_of_ge_iff'
      intro m
      constructor
      · intro hge
        have hm_lt : m < cl.length := by
          have := List.length_filter_le (fun x => decide (x ≥ i + 1)) cl; omega
        have hclm := (sorted_filter_ge_length_iff cl hcl_sorted m hm_lt (i + 1)).mp hge
        rw [hcl_getElem m (by omega)] at hclm
        exact (sorted_filter_ge_length_iff (a :: rest) hsorted i h1 (m + 1)).mp hclm
      · intro hge
        have hfilt := (sorted_filter_ge_length_iff (a :: rest) hsorted i h1 (m + 1)).mpr hge
        have hm_lt : m < cl.length := by
          rw [hcl_len]
          have : (a :: rest)[i] ≤ a := by
            rcases i with _ | i'
            · simp
            · exact List.pairwise_iff_getElem.mp hsorted 0 (i' + 1) (by omega) h1 (by omega)
          omega
        have hclm_ge : cl[m]'hm_lt ≥ i + 1 := by
          rw [hcl_getElem m (by omega)]; exact hfilt
        exact (sorted_filter_ge_length_iff cl hcl_sorted m hm_lt (i + 1)).mpr hclm_ge

private lemma conjugate_weight_filter_range_lt (x a : ℕ) (hx : x ≤ a) :
    (List.range a).filter (fun j => decide (x ≥ j + 1)) = List.range x := by
  induction a with
  | zero =>
    interval_cases x
    simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    simp only [List.filter_cons, List.filter_nil]
    by_cases hxn : x ≤ n
    · have hlt : ¬ (decide (x ≥ n + 1) = true) := by simp; omega
      rw [if_neg hlt, List.append_nil]
      exact ih hxn
    · push_neg at hxn
      have hxeq : x = n + 1 := by omega
      subst hxeq
      have hge : decide ((n + 1) ≥ n + 1) = true := by simp
      rw [if_pos hge]
      have hfilt : (List.range n).filter (fun j => decide ((n+1) ≥ j + 1)) = List.range n := by
        apply List.filter_eq_self.mpr
        intro j hj
        simp [List.mem_range] at hj ⊢
        omega
      rw [hfilt, List.range_succ]

private lemma conjugate_weight_sum_map_ite_eq_filter_length {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map (fun x => if p x then 1 else 0)).sum = (l.filter (fun x => decide (p x))).length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons, decide_eq_true_eq]
    split
    · simp [ih, List.length_cons, Nat.add_comm]
    · simp [ih]

private lemma conjugate_weight_sum_map_filter_length_eq_sum (l : List ℕ) (a : ℕ) (hmax : ∀ x ∈ l, x ≤ a) :
    ((List.range a).map (fun j => (l.filter (fun x => decide (x ≥ j + 1))).length)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ a := hmax x (by simp)
    have hxs : ∀ y ∈ xs, y ≤ a := fun y hy => hmax y (by simp [hy])
    simp only [List.sum_cons]
    have hfilt_cons : ∀ j, (List.filter (fun y => decide (y ≥ j + 1)) (x :: xs)).length
        = (if x ≥ j + 1 then 1 else 0) + (List.filter (fun y => decide (y ≥ j + 1)) xs).length := by
      intro j
      simp only [List.filter_cons, decide_eq_true_eq]
      split
      · simp [List.length_cons, Nat.add_comm]
      · simp
    conv_lhs =>
      arg 1; arg 1; ext j; rw [hfilt_cons j]
    rw [show ((List.range a).map (fun j => (if x ≥ j + 1 then 1 else 0) + (List.filter (fun y => decide (y ≥ j + 1)) xs).length)).sum
        = ((List.range a).map (fun j => if x ≥ j + 1 then 1 else 0)).sum +
          ((List.range a).map (fun j => (List.filter (fun y => decide (y ≥ j + 1)) xs).length)).sum from by
          rw [← List.sum_map_add]]
    rw [ih hxs]
    congr 1
    rw [conjugate_weight_sum_map_ite_eq_filter_length, conjugate_weight_filter_range_lt x a hx, List.length_range]

theorem conjugate_weight (l : List ℕ) (hl : IsPositivePartition l) :
    partWeight (conjugate l) = partWeight l := by
  unfold partWeight conjugate
  cases l with
  | nil => simp
  | cons a rest =>
    simp only
    have hmax : ∀ x ∈ (a :: rest), x ≤ a := by
      intro x hx
      have hpw := hl.1
      simp only [List.pairwise_cons] at hpw
      rcases List.mem_cons.mp hx with h | h
      · omega
      · exact hpw.1 x h
    exact conjugate_weight_sum_map_filter_length_eq_sum (a :: rest) a hmax

/-! ## Supporting Lemmas -/

private lemma record_bound_filter_eraseIdx_of_neg (p : ℕ → Bool) (l : List ℕ) (i : ℕ) (hi : i < l.length)
    (hneg : p (l[i]'hi) = false) :
    (l.eraseIdx i).filter p = l.filter p := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.eraseIdx_cons_zero, List.getElem_cons_zero] at hneg ⊢
      simp [hneg]
    | succ j =>
      simp only [List.eraseIdx_cons_succ, List.filter_cons]
      have hj : j < t.length := by simpa using hi
      have hneg' : p (t[j]'hj) = false := by simpa using hneg
      rw [ih j hj hneg']

private lemma record_bound_scanFromSmallest_filter_length (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ) :
    ((scanFromSmallest fuel A idx rec).1.filter (fun x => decide (¬(x % 3 == 0)))).length =
    (A.filter (fun x => decide (¬(x % 3 == 0)))).length := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromSmallest]
  | succ fuel' ih =>
    simp only [scanFromSmallest]
    split
    · rfl
    · rename_i h; push_neg at h
      have hact : A.length - 1 - idx < A.length := by omega
      split
      · rename_i hfr
        have hmod3 : (A[A.length - 1 - idx]! % 3 == 0) = true := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          exact beq_iff_eq.mpr hfr.1.2
        have hpred_false : (fun x : ℕ => decide (¬(x % 3 == 0))) (A[A.length - 1 - idx]'hact) = false := by
          simp only [decide_eq_false_iff_not, not_not]
          rw [← getElem!_pos A (A.length - 1 - idx) hact]; exact hmod3
        have hfilter_eq : (A.eraseIdx (A.length - 1 - idx)).filter (fun x => decide (¬(x % 3 == 0))) =
            A.filter (fun x => decide (¬(x % 3 == 0))) :=
          record_bound_filter_eraseIdx_of_neg _ A (A.length - 1 - idx) hact hpred_false
        have h1 := ih (A.eraseIdx (A.length - 1 - idx)) idx (rec ++ [A[A.length - 1 - idx]! / 3])
        rw [h1, hfilter_eq]
      · exact ih A (idx + 1) rec

-- Core mathematical lemma: in a 3-flat partition, A[j]/3 ≤ count of non-mults in suffix
-- Proved by induction on suffix length (A.length - 1 - j)
private lemma threeFlat_div3_le_suffix_nonmults (A : List ℕ)
    (hgap : ∀ (i : ℕ) (hi : i + 1 < A.length), A[i]'(by omega) - A[i + 1]'hi < 3)
    (hlast : ∀ h : A ≠ [], A.getLast h < 3)
    (hpw : A.Pairwise (· ≥ ·)) :
    ∀ j : ℕ, (hj : j < A.length) →
    A[j]'hj / 3 ≤ ((List.drop (j+1) A).filter (fun x => ¬(x % 3 == 0))).length := by
  intro j hj
  suffices hsuff : ∀ d : ℕ, ∀ j : ℕ, (hj : j < A.length) → A.length - 1 - j = d →
      A[j]'hj / 3 ≤ ((List.drop (j+1) A).filter (fun x => ¬(x % 3 == 0))).length from
    hsuff (A.length - 1 - j) j hj rfl
  intro d
  induction d with
  | zero =>
    intro j hj hd
    have hj_last : j = A.length - 1 := by omega
    subst hj_last
    have hdrop_nil : List.drop (A.length - 1 + 1) A = [] := by
      simp [List.drop_eq_nil_iff]; omega
    simp [hdrop_nil]
    have hne : A ≠ [] := by intro h; simp [h] at hj
    have hA_last : A.getLast hne < 3 := hlast hne
    have hA_last_eq : A[A.length - 1]'hj = A.getLast hne := by
      rw [List.getLast_eq_getElem]
    omega
  | succ d ih =>
    intro j hj hd
    have hj1 : j + 1 < A.length := by omega
    have hge : A[j]'hj ≥ A[j+1]'hj1 := by
      exact List.pairwise_iff_getElem.mp hpw j (j+1) (by omega) hj1 (by omega)
    have hgap_j := hgap j hj1
    have hdrop_cons : List.drop (j+1) A = A[j+1]'hj1 :: List.drop (j+1+1) A :=
      List.drop_eq_getElem_cons hj1
    rw [hdrop_cons]
    simp only [List.filter_cons]
    by_cases hmod : A[j+1]'hj1 % 3 = 0
    · have hpred : ¬(decide (¬((A[j+1]'hj1) % 3 == 0)) = true) := by simp [hmod]
      rw [if_neg hpred]
      have heq : A[j]'hj / 3 = A[j+1]'hj1 / 3 := by omega
      have ih_app := ih (j+1) hj1 (by omega)
      linarith
    · have hpred : (decide (¬((A[j+1]'hj1) % 3 == 0)) = true) := by simp [beq_iff_eq, hmod]
      rw [if_pos hpred, List.length_cons]
      have hstep : A[j]'hj / 3 ≤ A[j+1]'hj1 / 3 + 1 := by omega
      have ih_app := ih (j+1) hj1 (by omega)
      linarith

-- Corollary: in a 3-flat partition, val/3 ≤ total non-mult count for any val at any position
private lemma threeFlat_mult_div3_le_filter_length (A : List ℕ) (hflat : IsThreeFlat A)
    (j : ℕ) (hj : j < A.length) :
    A[j]'hj / 3 ≤ (A.filter (fun x => ¬(x % 3 == 0))).length := by
  obtain ⟨⟨hpw, _⟩, hgap, hlast⟩ := hflat
  have hsuffix := threeFlat_div3_le_suffix_nonmults A hgap hlast hpw j hj
  have hsub : (List.drop (j+1) A).Sublist A := List.drop_sublist (j+1) A
  have hfilt_sub := hsub.filter (fun x => ¬(x % 3 == 0))
  exact le_trans hsuffix (List.Sublist.length_le hfilt_sub)

private lemma record_bound_scanFromSmallest_rec_le (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hflat : IsThreeFlat A) (hrec : ∀ x ∈ rec, x ≤ (A.filter (fun x => decide (¬(x % 3 == 0)))).length) :
    ∀ x ∈ (scanFromSmallest fuel A idx rec).2,
      x ≤ (A.filter (fun x => decide (¬(x % 3 == 0)))).length := by
  induction fuel generalizing A idx rec with
  | zero =>
    simp only [scanFromSmallest]
    exact hrec
  | succ fuel' ih =>
    simp only [scanFromSmallest]
    split
    · exact hrec
    · rename_i h; push_neg at h
      have hact : A.length - 1 - idx < A.length := by omega
      split
      · rename_i hfr
        have hmod3 : (A[A.length - 1 - idx]! % 3 == 0) = true := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          exact beq_iff_eq.mpr hfr.1.2
        have hflatBool : isThreeFlatBool (A.eraseIdx (A.length - 1 - idx)) = true := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr
          exact hfr.2
        have hflat' : IsThreeFlat (A.eraseIdx (A.length - 1 - idx)) := by
          unfold isThreeFlatBool isPositivePartitionBool at hflatBool
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hflatBool
          obtain ⟨⟨⟨hpw', hall'⟩, hgaps'⟩, hlast'⟩ := hflatBool
          refine ⟨⟨hpw', fun x hx => hall' x hx⟩, ?_, ?_⟩
          · intro i hi
            have hgi := hgaps' i (by omega)
            rw [getElem!_pos _ i (by omega), getElem!_pos _ (i+1) (by omega)] at hgi
            exact hgi
          · intro hne
            rw [List.getLast?_eq_some_getLast hne] at hlast'
            simpa using hlast'
        have hpred_false : (fun x : ℕ => decide (¬(x % 3 == 0))) (A[A.length - 1 - idx]'hact) = false := by
          simp only [decide_eq_false_iff_not, not_not]
          rw [← getElem!_pos A (A.length - 1 - idx) hact]; exact hmod3
        have hfilter_eq : (A.eraseIdx (A.length - 1 - idx)).filter (fun x => decide (¬(x % 3 == 0))) =
            A.filter (fun x => decide (¬(x % 3 == 0))) :=
          record_bound_filter_eraseIdx_of_neg _ A (A.length - 1 - idx) hact hpred_false
        have hval_le : A[A.length - 1 - idx]! / 3 ≤ (A.filter (fun x => decide (¬(x % 3 == 0)))).length := by
          rw [getElem!_pos A (A.length - 1 - idx) hact]
          exact threeFlat_mult_div3_le_filter_length A hflat (A.length - 1 - idx) hact
        have hrec' : ∀ x ∈ rec ++ [A[A.length - 1 - idx]! / 3],
            x ≤ ((A.eraseIdx (A.length - 1 - idx)).filter (fun x => decide (¬(x % 3 == 0)))).length := by
          intro x hx
          rw [hfilter_eq]
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact hrec x hx
          · rw [hx]; exact hval_le
        have h_ih := ih (A.eraseIdx (A.length - 1 - idx)) idx (rec ++ [A[A.length - 1 - idx]! / 3]) hflat' hrec'
        intro x hx
        have hx' := h_ih x hx
        rw [hfilter_eq] at hx'
        exact hx'
      · exact ih A (idx + 1) rec hflat hrec

private lemma scanFromSmallest_isThreeFlat (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hflat : IsThreeFlat A) :
    IsThreeFlat (scanFromSmallest fuel A idx rec).1 := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromSmallest]; exact hflat
  | succ fuel' ih =>
    simp only [scanFromSmallest]
    split
    · exact hflat
    · rename_i h; push_neg at h
      split
      · rename_i hfr
        have hflatBool : isThreeFlatBool (A.eraseIdx (A.length - 1 - idx)) = true := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr
          exact hfr.2
        have hflat' : IsThreeFlat (A.eraseIdx (A.length - 1 - idx)) := by
          unfold isThreeFlatBool isPositivePartitionBool at hflatBool
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hflatBool
          obtain ⟨⟨⟨hpw', hall'⟩, hgaps'⟩, hlast'⟩ := hflatBool
          refine ⟨⟨hpw', fun x hx => hall' x hx⟩, ?_, ?_⟩
          · intro i hi
            have hgi := hgaps' i (by omega)
            rw [getElem!_pos _ i (by omega), getElem!_pos _ (i+1) (by omega)] at hgi
            exact hgi
          · intro hne
            rw [List.getLast?_eq_some_getLast hne] at hlast'
            simpa using hlast'
        exact ih (A.eraseIdx (A.length - 1 - idx)) idx (rec ++ [A[A.length - 1 - idx]! / 3]) hflat'
      · exact ih A (idx + 1) rec hflat

private lemma suffix_threeFlat_div3_le_drop_filter (A : List ℕ) (idx : ℕ) (hidx : idx < A.length)
    (hgap : ∀ (i : ℕ) (hi : i + 1 < (A.drop idx).length),
      (A.drop idx)[i]'(by omega) - (A.drop idx)[i + 1]'hi < 3)
    (hlast : ∀ h : A.drop idx ≠ [], (A.drop idx).getLast h < 3)
    (hpw : (A.drop idx).Pairwise (· ≥ ·)) :
    A[idx]'hidx / 3 ≤ ((A.drop (idx + 1)).filter (fun x => ¬(x % 3 == 0))).length := by
  have hdrop_ne : A.drop idx ≠ [] := by
    intro h; simp [List.drop_eq_nil_iff] at h; omega
  have hdrop_head : (A.drop idx)[0]'(by simp [List.length_drop]; omega) = A[idx]'hidx := by
    rw [List.getElem_drop]; congr 1
  have hdrop1_eq : (A.drop idx).drop 1 = A.drop (idx + 1) := by
    rw [List.drop_drop]
  have h := threeFlat_div3_le_suffix_nonmults (A.drop idx) hgap hlast hpw 0
    (by simp [List.length_drop]; omega)
  simp only [hdrop1_eq] at h
  rwa [hdrop_head] at h

private lemma record_bound_scanFromLargest_aux (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (k : ℕ) (hk : k ≥ ((A.drop idx).filter (fun x => decide (¬(x % 3 == 0)))).length + idx)
    (hrec : ∀ x ∈ rec, x ≤ k)
    (hgap : ∀ (i : ℕ) (hi : i + 1 < (A.drop idx).length),
      (A.drop idx)[i]'(by omega) - (A.drop idx)[i + 1]'hi < 3)
    (hlast : ∀ h : A.drop idx ≠ [], (A.drop idx).getLast h < 3)
    (hpw : (A.drop idx).Pairwise (· ≥ ·))
    (hpos_all : ∀ x ∈ A.drop idx, 0 < x) :
    ∀ x ∈ (scanFromLargest fuel A idx rec).2, x ≤ k := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromLargest]; exact hrec
  | succ fuel' ih =>
    simp only [scanFromLargest]
    split
    · exact hrec
    · rename_i hidx_lt; push_neg at hidx_lt
      split
      · rename_i hfire
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfire
        have hmod : A[idx]! % 3 = 0 := hfire.1
        have hpos : A[idx]! > 0 := hfire.2
        rw [getElem!_pos A idx hidx_lt] at hmod hpos
        -- The record entry is A[idx]/3 + idx
        have hval_bound : A[idx]'hidx_lt / 3 + idx ≤ k := by
          have hsuffix := suffix_threeFlat_div3_le_drop_filter A idx hidx_lt hgap hlast hpw
          have hdrop_filter_eq : ((A.drop idx).filter (fun x => decide (¬(x % 3 == 0)))).length =
              ((A.drop (idx + 1)).filter (fun x => decide (¬(x % 3 == 0)))).length := by
            have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
              List.drop_eq_getElem_cons hidx_lt
            rw [hdrop_cons, List.filter_cons]
            have hmod' : ¬(decide (¬(A[idx]'hidx_lt % 3 == 0)) = true) := by
              simp [beq_iff_eq, hmod]
            rw [if_neg hmod']
          linarith [hk, hdrop_filter_eq, hsuffix]
        -- Set up recursive call
        set A' := A.eraseIdx idx
        set A'' := A'.zipIdx.map (fun (x, j) => if j < idx then x - 3 else x)
        -- Suffix of A'' from idx onwards = A.drop (idx + 1)
        have hA''_drop : A''.drop idx = A.drop (idx + 1) := by
          apply List.ext_getElem
          · simp [A'', A', List.length_map, List.length_zipIdx, List.length_eraseIdx, List.length_drop,
                  hidx_lt]
            omega
          · intro i h1 h2
            simp only [A'', List.getElem_drop, List.getElem_map, List.getElem_zipIdx]
            simp only [A', List.getElem_eraseIdx]
            have h_not_lt : ¬(i + idx < idx) := by omega
            simp [h_not_lt]
            congr 1
            omega
        have hk' : k ≥ ((A''.drop idx).filter (fun x => decide (¬(x % 3 == 0)))).length + idx := by
          rw [hA''_drop]
          have hdrop_filter_eq : ((A.drop idx).filter (fun x => decide (¬(x % 3 == 0)))).length =
              ((A.drop (idx + 1)).filter (fun x => decide (¬(x % 3 == 0)))).length := by
            have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
              List.drop_eq_getElem_cons hidx_lt
            rw [hdrop_cons, List.filter_cons]
            have hmod' : ¬(decide (¬(A[idx]'hidx_lt % 3 == 0)) = true) := by
              simp [beq_iff_eq, hmod]
            rw [if_neg hmod']
          linarith [hk, hdrop_filter_eq]
        have hrec' : ∀ x ∈ rec ++ [A[idx]! / 3 + idx], x ≤ k := by
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact hrec x hx
          · rw [hx, getElem!_pos A idx hidx_lt]; exact hval_bound
        have hgap' : ∀ (i : ℕ) (hi : i + 1 < (A''.drop idx).length),
            (A''.drop idx)[i]'(by omega) - (A''.drop idx)[i + 1]'hi < 3 := by
          intro i hi
          simp only [hA''_drop] at hi ⊢
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          have hi_shifted : i + 1 + 1 < (A.drop idx).length := by
            simp [List.length_drop] at hi ⊢; omega
          have hgap_shifted := hgap (i + 1) hi_shifted
          simp only [hdrop_cons, List.getElem_cons_succ] at hgap_shifted
          exact hgap_shifted
        have hlast' : ∀ h : A''.drop idx ≠ [], (A''.drop idx).getLast h < 3 := by
          intro hne
          simp only [hA''_drop] at hne ⊢
          have hdrop_ne : A.drop idx ≠ [] := by
            intro h; simp [List.drop_eq_nil_iff] at h; omega
          have h1 := hlast hdrop_ne
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          have key : (A.drop idx).getLast hdrop_ne = (A.drop (idx + 1)).getLast hne := by
            simp only [hdrop_cons]
            exact List.getLast_cons hne
          linarith
        have hpw' : (A''.drop idx).Pairwise (· ≥ ·) := by
          rw [show A''.drop idx = A.drop (idx + 1) from hA''_drop]
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          rw [hdrop_cons] at hpw
          exact (List.pairwise_cons.mp hpw).2
        have hpos_all' : ∀ x ∈ A''.drop idx, 0 < x := by
          rw [hA''_drop]
          intro x hx
          have hdrop_cons := List.drop_eq_getElem_cons hidx_lt (l := A)
          have hmem : x ∈ A.drop idx := hdrop_cons ▸ List.mem_cons_of_mem _ hx
          exact hpos_all _ hmem
        exact ih A'' idx (rec ++ [A[idx]! / 3 + idx]) hk' hrec' hgap' hlast' hpw' hpos_all'
      · rename_i hskip
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and_or] at hskip
        -- In skip case: A[idx] is not a mult-of-3 (since all elements are positive by hpos_all)
        have hidx_pos : A[idx]'hidx_lt > 0 := by
          have hmem : A[idx]'hidx_lt ∈ A.drop idx := by
            have hdrop_cons := List.drop_eq_getElem_cons hidx_lt
            rw [hdrop_cons]; exact List.mem_cons_self
          exact hpos_all _ hmem
        have hskip_mod : ¬(A[idx]'hidx_lt % 3 = 0) := by
          have hskip' : ¬(A[idx]'hidx_lt % 3 = 0) ∨ ¬(A[idx]'hidx_lt > 0) := by
            rwa [getElem!_pos A idx hidx_lt] at hskip
          rcases hskip' with h | h
          · exact h
          · exact absurd hidx_pos h
        have hk' : k ≥ ((A.drop (idx + 1)).filter (fun x => decide (¬(x % 3 == 0)))).length + (idx + 1) := by
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          have hfilter_cons : ((A.drop idx).filter (fun x => decide (¬(x % 3 == 0)))).length ≥
              ((A.drop (idx + 1)).filter (fun x => decide (¬(x % 3 == 0)))).length + 1 := by
            rw [hdrop_cons, List.filter_cons]
            have hpass : (decide (¬(A[idx]'hidx_lt % 3 == 0)) = true) := by
              simp only [decide_eq_true_eq, beq_iff_eq]
              exact hskip_mod
            rw [if_pos hpass]
            simp [List.length_cons]
          linarith [hk, hfilter_cons]
        have hgap' : ∀ (i : ℕ) (hi : i + 1 < (A.drop (idx + 1)).length),
            (A.drop (idx + 1))[i]'(by omega) - (A.drop (idx + 1))[i + 1]'hi < 3 := by
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          intro i hi
          have hi_shifted : (i + 1) + 1 < (A.drop idx).length := by
            simp [List.length_drop] at hi ⊢; omega
          have hgap_shifted := hgap (i + 1) hi_shifted
          simp only [hdrop_cons, List.getElem_cons_succ] at hgap_shifted
          exact hgap_shifted
        have hlast' : ∀ h : A.drop (idx + 1) ≠ [], (A.drop (idx + 1)).getLast h < 3 := by
          intro hne
          have hdrop_ne : A.drop idx ≠ [] := by
            intro h; simp [List.drop_eq_nil_iff] at h; omega
          have h1 := hlast hdrop_ne
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          have key : (A.drop idx).getLast hdrop_ne = (A.drop (idx + 1)).getLast hne := by
            simp only [hdrop_cons]
            exact List.getLast_cons hne
          linarith
        have hpw' : (A.drop (idx + 1)).Pairwise (· ≥ ·) := by
          have hdrop_cons : A.drop idx = A[idx]'hidx_lt :: A.drop (idx + 1) :=
            List.drop_eq_getElem_cons hidx_lt
          rw [hdrop_cons] at hpw
          exact (List.pairwise_cons.mp hpw).2
        have hpos_all' : ∀ x ∈ A.drop (idx + 1), 0 < x := by
          intro x hx
          have hdrop_cons := List.drop_eq_getElem_cons hidx_lt (l := A)
          have hmem : x ∈ A.drop idx := hdrop_cons ▸ List.mem_cons_of_mem _ hx
          exact hpos_all _ hmem
        exact ih A (idx + 1) rec hk' hrec hgap' hlast' hpw' hpos_all'

private lemma record_bound_scanFromLargest_rec_le (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (k : ℕ) (hk : k ≥ (A.filter (fun x => decide (¬(x % 3 == 0)))).length + idx)
    (hrec : ∀ x ∈ rec, x ≤ k)
    (hgap : ∀ (i : ℕ) (hi : i + 1 < (A.drop idx).length),
      (A.drop idx)[i]'(by omega) - (A.drop idx)[i + 1]'hi < 3)
    (hlast : ∀ h : A.drop idx ≠ [], (A.drop idx).getLast h < 3)
    (hpw : (A.drop idx).Pairwise (· ≥ ·))
    (hpos_all : ∀ x ∈ A.drop idx, 0 < x) :
    ∀ x ∈ (scanFromLargest fuel A idx rec).2, x ≤ k := by
  have hk_drop : k ≥ ((A.drop idx).filter (fun x => decide (¬(x % 3 == 0)))).length + idx := by
    have hsub : (A.drop idx).Sublist A := List.drop_sublist idx A
    have hfilt_le := (hsub.filter (fun x => decide (¬(x % 3 == 0)))).length_le
    linarith
  exact record_bound_scanFromLargest_aux fuel A idx rec k hk_drop hrec hgap hlast hpw hpos_all

theorem record_bound (l : List ℕ) (hflat : IsThreeFlat l) :
    let k := (l.filter (fun x => ¬(x % 3 == 0))).length
    let (A₂, rec₂) := scanFromSmallest (l.length + 1) l 0 []
    let (_, rec₃) := scanFromLargest (A₂.length + 1) A₂ 0 rec₂
    ∀ x ∈ rec₃, x ≤ k := by
  intro k
  -- Prove with explicit projections then use definitional equality
  have hrec₂_le : ∀ x ∈ (scanFromSmallest (l.length + 1) l 0 []).2, x ≤ k :=
    record_bound_scanFromSmallest_rec_le (l.length + 1) l 0 [] hflat
      (by intro x hx; simp at hx)
  have hflat_s2 : IsThreeFlat (scanFromSmallest (l.length + 1) l 0 []).1 :=
    scanFromSmallest_isThreeFlat (l.length + 1) l 0 [] hflat
  have hfilt_eq : k ≥ ((scanFromSmallest (l.length + 1) l 0 []).1.filter
      (fun x => decide (¬(x % 3 == 0)))).length + 0 := by
    have hfl := record_bound_scanFromSmallest_filter_length (l.length + 1) l 0 []
    have hk : k = (l.filter (fun x => decide (¬(x % 3 == 0)))).length := rfl
    omega
  have hgap_s2 : ∀ (i : ℕ)
      (hi : i + 1 < ((scanFromSmallest (l.length + 1) l 0 []).1.drop 0).length),
      ((scanFromSmallest (l.length + 1) l 0 []).1.drop 0)[i]'(by omega) -
        ((scanFromSmallest (l.length + 1) l 0 []).1.drop 0)[i + 1]'hi < 3 := by
    simp only [List.drop_zero]; exact hflat_s2.2.1
  have hlast_s2 : ∀ h : (scanFromSmallest (l.length + 1) l 0 []).1.drop 0 ≠ [],
      ((scanFromSmallest (l.length + 1) l 0 []).1.drop 0).getLast h < 3 := by
    simp only [List.drop_zero]; exact hflat_s2.2.2
  have hpw_s2 : ((scanFromSmallest (l.length + 1) l 0 []).1.drop 0).Pairwise (· ≥ ·) := by
    simp only [List.drop_zero]; exact hflat_s2.1.1
  have hpos_all_s2 : ∀ x ∈ (scanFromSmallest (l.length + 1) l 0 []).1.drop 0, 0 < x := by
    simp only [List.drop_zero]; exact hflat_s2.1.2
  have hrec₃_le := record_bound_scanFromLargest_rec_le
    ((scanFromSmallest (l.length + 1) l 0 []).1.length + 1)
    (scanFromSmallest (l.length + 1) l 0 []).1
    0
    (scanFromSmallest (l.length + 1) l 0 []).2
    k hfilt_eq hrec₂_le hgap_s2 hlast_s2 hpw_s2 hpos_all_s2
  exact hrec₃_le

theorem extract_isPartition (l : List ℕ) (hreg : IsThreeRegular l) :
    let v := nonzeroResSeq l
    let A := residueCore v
    let q := (List.range A.length).map (fun i =>
      ((l[i]?.getD 0) - (A[i]?.getD 0)) / 3)
    IsPartition q := by
  intro v A q
  have hv_12 : ∀ x ∈ v, x = 1 ∨ x = 2 := nonzeroResSeq_in_one_two l
  have hnrs_eq : v = l.map (· % 3) := nonzeroResSeq_of_threeRegular' l hreg
  have hAl : A.length = l.length := by
    have h1 := residueCore_length v hv_12
    have h2 : v.length = l.length := by rw [hnrs_eq]; simp
    linarith
  have hAflat := residueCore_isThreeFlat v hv_12
  have hAgaps : ∀ (i : ℕ) (hi : i + 1 < A.length),
      A[i]'(by omega) - A[i + 1]'hi < 3 := hAflat.2.1
  have hAlast : ∀ (h : A ≠ []), A.getLast h < 3 := hAflat.2.2
  have hmod : ∀ (i : ℕ) (hi : i < l.length),
      A[i]'(by omega) % 3 = l[i]'hi % 3 := by
    intro i hi
    have hi' : i < A.length := by omega
    have hmap_eq : List.map (· % 3) A = l.map (· % 3) := by
      show List.map (· % 3) (residueCore v) = l.map (· % 3)
      rw [residueCore_map_mod3 _ hv_12, hnrs_eq]
    have h1 : (List.map (· % 3) A)[i]'(by simp; exact hi') = A[i]'hi' % 3 :=
      List.getElem_map ..
    have h2 : (List.map (· % 3) l)[i]'(by simp; exact hi) = l[i]'hi % 3 :=
      List.getElem_map ..
    have h3 : (List.map (· % 3) A)[i]'(by simp; exact hi') =
              (List.map (· % 3) l)[i]'(by simp; exact hi) :=
      List.getElem_of_eq hmap_eq _
    linarith
  have hdom : ∀ (i : ℕ) (hi : i < l.length), A[i]'(by omega) ≤ l[i]'hi := by
    suffices hsuff : ∀ k : ℕ, k ≤ l.length →
        (∀ i : ℕ, (hi : i < l.length) → l.length - k ≤ i → A[i]'(by omega) ≤ l[i]'hi) by
      intro i hi; exact hsuff l.length (le_refl _) i hi (by omega)
    intro k
    induction k with
    | zero => intro _ i hi hge; omega
    | succ n ih_n =>
      intro hle i hi hge
      by_cases heq : l.length - (n + 1) = i
      · by_cases hn_zero : n = 0
        · have hAne : A ≠ [] := by intro h; simp [h] at hAl; omega
          have hA_i : A[i]'(by omega) < 3 := by
            have h := hAlast hAne
            rw [List.getLast_eq_getElem] at h
            have heqi : i = A.length - 1 := by omega
            exact heqi ▸ h
          have hpos_i : 0 < l[i]'hi := hreg.1.2 _ (List.getElem_mem hi)
          have hmod_i := hmod i hi
          omega
        · have hi_next : i + 1 < l.length := by omega
          have hih_next : A[i + 1]'(by omega) ≤ l[i + 1]'hi_next :=
            ih_n (by omega) (i + 1) hi_next (by omega)
          have hgap : A[i]'(by omega) - A[i + 1]'(by omega) < 3 :=
            hAgaps i (by omega)
          have hdec_i : l[i]'hi ≥ l[i + 1]'hi_next :=
            List.pairwise_iff_getElem.mp hreg.1.1 i (i + 1) hi (by omega) (by omega)
          have hmod_i := hmod i hi
          omega
      · exact ih_n (by omega) i hi (by omega)
  unfold IsPartition
  apply List.IsChain.pairwise
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [q, List.getElem_map, List.getElem_range, List.length_map, List.length_range] at hi ⊢
  have hiA : i < A.length := by omega
  have hi1A : i + 1 < A.length := by omega
  have hiL : i < l.length := by omega
  have hi1L : i + 1 < l.length := by omega
  rw [List.getElem?_eq_getElem (h := hiL), Option.getD_some,
      List.getElem?_eq_getElem (h := hiA), Option.getD_some,
      List.getElem?_eq_getElem (h := hi1L), Option.getD_some,
      List.getElem?_eq_getElem (h := hi1A), Option.getD_some]
  have hdom_i := hdom i hiL
  have hdom_i1 := hdom (i + 1) hi1L
  have hmod_i := hmod i hiL
  have hmod_i1 := hmod (i + 1) hi1L
  have hdec : l[i]'hiL ≥ l[i + 1]'hi1L :=
    List.pairwise_iff_getElem.mp hreg.1.1 i (i + 1) hiL hi1L (by omega)
  have hAdec : A[i]'hiA ≥ A[i + 1]'hi1A :=
    List.pairwise_iff_getElem.mp hAflat.1.1 i (i + 1) hiA hi1A (by omega)
  have hAgap' : A[i]'hiA - A[i + 1]'hi1A < 3 := hAgaps i hi1A
  omega

private lemma isThreeFlatBool_implies (l : List ℕ) (h : isThreeFlatBool l = true) :
    IsThreeFlat l := by
  unfold isThreeFlatBool isPositivePartitionBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hpw, hall⟩, hgaps⟩, hlast⟩ := h
  refine ⟨⟨hpw, ?_⟩, ?_, ?_⟩
  · intro x hx; exact hall x hx
  · intro i hi
    have hgi := hgaps i (by omega)
    rw [getElem!_pos l i (by omega), getElem!_pos l (i+1) (by omega)] at hgi
    exact hgi
  · intro hne
    rw [List.getLast?_eq_some_getLast hne] at hlast
    simpa using hlast

private lemma tryHardInsertion_isThreeFlatBool {A : List ℕ} {p h : ℕ} {result : List ℕ}
    (hsome : tryHardInsertion A p h = some result) :
    isThreeFlatBool result = true := by
  simp only [tryHardInsertion] at hsome
  split at hsome
  · simp at hsome
  · split at hsome
    · next hcond =>
      have heq := Option.some.inj hsome.symm
      rw [heq]
      simp only [Bool.and_eq_true] at hcond
      exact hcond.1
    · simp at hsome

private lemma findHardInsertion_isThreeFlatBool {A : List ℕ} {p h : ℕ} {result : List ℕ}
    (hsome : findHardInsertion A p h = some result) :
    isThreeFlatBool result = true := by
  unfold findHardInsertion at hsome
  split at hsome
  · simp at hsome
  · split at hsome
    · next r heq =>
      have hrr := Option.some.inj hsome
      rw [← hrr]
      exact tryHardInsertion_isThreeFlatBool heq
    · exact findHardInsertion_isThreeFlatBool hsome
termination_by p + A.length + 1 - h

private lemma tryEasyInsertion_isThreeFlatBool {A : List ℕ} {p : ℕ} {result : List ℕ}
    (hsome : tryEasyInsertion A p = some result) :
    isThreeFlatBool result = true := by
  simp only [tryEasyInsertion] at hsome
  split at hsome
  · next hcond =>
    have heq := Option.some.inj hsome.symm
    rw [heq]
    simp only [Bool.and_eq_true] at hcond
    exact hcond.1
  · simp at hsome

private theorem performInsertion_preserves_flat (A : List ℕ) (p : ℕ) (hflat : IsThreeFlat A) :
    IsThreeFlat (performInsertion A p) := by
  unfold performInsertion
  split
  · next result heq =>
    exact isThreeFlatBool_implies result (findHardInsertion_isThreeFlatBool heq)
  · split
    · next result heq =>
      exact isThreeFlatBool_implies result (tryEasyInsertion_isThreeFlatBool heq)
    · exact hflat

theorem no_raise_labels (l : List ℕ) :
    let v := nonzeroResSeq l
    let A := residueCore v
    let q := (List.range A.length).map (fun i =>
      ((l[i]?.getD 0) - (A[i]?.getD 0)) / 3)
    let ν := conjugate q
    IsThreeFlat (processInsertions ν A) := by
  intro v A q ν
  have hA_flat : IsThreeFlat A := residueCore_isThreeFlat v (nonzeroResSeq_in_one_two l)
  suffices h : ∀ (parts : List ℕ) (B : List ℕ), IsThreeFlat B →
      IsThreeFlat (processInsertions parts B) from h ν A hA_flat
  intro parts
  induction parts with
  | nil => intro B hB; exact hB
  | cons p rest ih =>
    intro B hB
    simp only [processInsertions]
    apply ih
    exact performInsertion_preserves_flat B p hB

/-! ## Main Statement: Proposition (prop:phi) -/

-- The main proposition: $\Phi_3$ is a weight-preserving, residue-preserving bijection
-- from 3-flat partitions to 3-regular partitions, with inverse $\Phi_3^{-1}$.
-- Conditioned on Glaisher's theorem (Theorem 1) as a hypothesis parameter.

/-! ### Glue lemmas connecting `phi3Forward` to its components -/

/-- The full sum of the records produced by S2 then S3 is `(wt α − wt core)/3`. -/
private lemma sum_eraseIdx_add' (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    l.sum = (l.eraseIdx i).sum + l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp [List.sum_cons]; omega
    | succ j =>
      simp only [List.sum_cons, List.eraseIdx_cons_succ, List.getElem_cons_succ]
      have hj : j < t.length := by simp at hi; omega
      have := ih j hj
      omega

private lemma scanFromSmallest_weight_inv' (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ) :
    let (A', rec') := scanFromSmallest fuel A idx rec
    partWeight A' + 3 * rec'.sum = partWeight A + 3 * rec.sum := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromSmallest]
  | succ fuel' ih =>
    simp only [scanFromSmallest]
    split
    · simp
    · rename_i h
      push_neg at h
      split
      · rename_i hfr
        set actualIdx := A.length - 1 - idx
        set val := A[actualIdx]!
        have hact : actualIdx < A.length := by omega
        have ih_step := ih (A.eraseIdx actualIdx) idx (rec ++ [val / 3])
        suffices h_step : partWeight (A.eraseIdx actualIdx) + 3 * (rec ++ [val / 3]).sum =
            partWeight A + 3 * rec.sum by
          simp only at ih_step ⊢; linarith
        have hmod : A[actualIdx] % 3 = 0 := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          have hfr12 := hfr.1.2
          rwa [getElem!_pos A actualIdx hact] at hfr12
        have hval_eq : val = A[actualIdx] := getElem!_pos A actualIdx hact
        have hdiv3 : 3 * (val / 3) = val := by
          rw [hval_eq]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
        have hsum_erase : partWeight A = partWeight (A.eraseIdx actualIdx) + val := by
          unfold partWeight; rw [hval_eq]; exact sum_eraseIdx_add' A actualIdx hact
        have hrec_sum : (rec ++ [val / 3]).sum = rec.sum + val / 3 := by
          simp [List.sum_append]
        rw [hrec_sum, Nat.mul_add, hdiv3]; omega
      · exact ih A (idx + 1) rec

/-- Count of positive multiples of 3 at positions ≥ idx in A. -/
private def numMultsGe (A : List ℕ) (idx : ℕ) : ℕ :=
  (A.drop idx).filter (fun x => x % 3 == 0 && decide (0 < x)) |>.length

private lemma sum_map_zipIdx_sub3 (l : List ℕ) (n : ℕ) (hn : n ≤ l.length)
    (hge : ∀ j : ℕ, (hj : j < l.length) → j < n → l[j] ≥ 3) :
    (l.zipIdx |>.map (fun (x, j) => if j < n then x - 3 else x)).sum + 3 * n = l.sum := by
  induction l generalizing n with
  | nil => simp at hn; subst hn; simp
  | cons a t ih =>
    cases n with
    | zero => simp [List.zipIdx_cons, List.zipIdx_map_fst]
    | succ m =>
      rw [List.zipIdx_cons, List.map_cons]
      simp only [List.sum_cons, show (0 : ℕ) < m + 1 from by omega, ite_true]
      have hage3 : a ≥ 3 := hge 0 (by simp) (by omega)
      have hm_le : m ≤ t.length := by simp at hn; omega
      have hge_t : ∀ j : ℕ, (hj : j < t.length) → j < m → t[j] ≥ 3 := by
        intro j hj hjm
        have := hge (j + 1) (by simp; omega) (by omega)
        simpa using this
      have hshift : (t.zipIdx (0 + 1)).map (fun x => if x.2 < m + 1 then x.1 - 3 else x.1) =
                    (t.zipIdx).map (fun (x, j) => if j < m then x - 3 else x) := by
        rw [show (0 : ℕ) + 1 = 1 from rfl, List.zipIdx_succ]
        rw [List.map_map]
        congr 1
        ext ⟨x, j⟩
        simp [Function.comp]
      rw [hshift]
      have ih_step := ih m hm_le hge_t
      omega

/-- Weight invariant for scanFromLargest: each step removes A[idx] (a mult of 3, value 3a),
    subtracts 3 from idx elements above, and records a+idx. Net change:
    -(3a + 3·idx) + 3·(a+idx) = 0.

    The hypothesis `hall` asserts that every element is ≥ 3 times the count of
    positive multiples of 3 strictly after it. This is the correct invariant
    that is maintained through both fire and skip steps of S3:
    - Fire at idx: elements at j<idx lose 3, but numMultsGe decreases by 1.
    - Skip: the list is unchanged, idx advances.
    - Elements at j<idx are never positive mults of 3 (mod-3 preserved by -3).

    The hypothesis is satisfied for post-S2 3-flat partitions (proved separately
    as `post_s2_numMultsGe_bound`). -/
private lemma scanFromLargest_weight_inv' (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j])) :
    let (A', rec') := scanFromLargest fuel A idx rec
    partWeight A' + 3 * rec'.sum = partWeight A + 3 * rec.sum := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromLargest]
  | succ fuel' ih =>
    simp only [scanFromLargest]
    split
    · simp
    · rename_i h
      push_neg at h
      split
      · rename_i hfire
        set val := A[idx]! with hval_def
        set a := val / 3
        set A' := A.eraseIdx idx
        set A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x) with hA''_def
        have hmod : val % 3 = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfire; exact hfire.1
        have hpos : val > 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfire; exact hfire.2
        have hdiv3 : 3 * a = val := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
        have hval_eq : val = A[idx] := getElem!_pos A idx h
        -- Hall maintenance for recursive call
        have hall' : ∀ j : ℕ, (hj : j < A''.length) → A''[j] ≥ 3 * numMultsGe A'' (j + 1) := by
          have hA''_len : A''.length = A'.length := by
            show (A'.zipIdx |>.map _).length = A'.length
            simp [List.length_map, List.length_zipIdx]
          have hA'_len : A'.length = A.length - 1 := by
            show (A.eraseIdx idx).length = A.length - 1
            simp [List.length_eraseIdx, show idx < A.length from h]
          intro j hj
          by_cases hjidx : j ≥ idx
          · -- Case j ≥ idx: A''[j] = A[j+1] (shifted by eraseIdx, no subtraction)
            have hj_A' : j < A'.length := by omega
            have hjp1_A : j + 1 < A.length := by omega
            have hA'j_eq : A'[j]'hj_A' = A[j + 1]'hjp1_A := by
              show (A.eraseIdx idx)[j] = A[j + 1]
              rw [List.getElem_eraseIdx]
              have : ¬(j < idx) := by omega
              simp [this]
            have hA''j_eq : A''[j]'hj = A[j + 1]'hjp1_A := by
              show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j + 1]
              rw [show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A'[j] from by
                rw [List.getElem_map, List.getElem_zipIdx]; simp [show ¬(j < idx) from by omega]]
              exact hA'j_eq
            -- numMultsGe A'' (j+1) ≤ numMultsGe A (j+2)
            have hcount_le : numMultsGe A'' (j + 1) ≤ numMultsGe A (j + 2) := by
              unfold numMultsGe
              -- A''.drop(j+1) = A.drop(j+2) since j ≥ idx: all elements at positions ≥ j+1 ≥ idx
              -- in A'' are unmodified (no -3) and correspond to A[k+1] from eraseIdx
              suffices heq : A''.drop (j + 1) = A.drop (j + 2) by rw [heq]
              apply List.ext_getElem
              · simp only [List.length_drop]; omega
              · intro k hk1 hk2
                have hk2' : j + 2 + k < A.length := by
                  simp [List.length_drop] at hk2; omega
                rw [List.getElem_drop, List.getElem_drop]
                show (A'.zipIdx |>.map (fun (x, i) => if i < idx then x - 3 else x))[j + 1 + k]'(by
                  simp [List.length_map, List.length_zipIdx]
                  simp [List.length_drop] at hk1; omega) = A[j + 2 + k]'hk2'
                rw [List.getElem_map, List.getElem_zipIdx]
                simp [show ¬(j + 1 + k < idx) from by omega]
                show (A.eraseIdx idx)[j + 1 + k]'(by
                  show j + 1 + k < (A.eraseIdx idx).length
                  simp [List.length_eraseIdx, h]; omega) = A[j + 2 + k]'hk2'
                rw [List.getElem_eraseIdx]
                simp [show ¬(j + 1 + k < idx) from by omega]
                congr 1; omega
            have hfrom_hall := hall (j + 1) hjp1_A
            rw [hA''j_eq]
            calc A[j + 1] ≥ 3 * numMultsGe A (j + 2) := hfrom_hall
              _ ≥ 3 * numMultsGe A'' (j + 1) := by omega
          · -- Case j < idx: A''[j] = A[j] - 3
            push_neg at hjidx
            have hj_A' : j < A'.length := by omega
            have hj_A : j < A.length := by omega
            have hA'j_eq : A'[j]'hj_A' = A[j]'hj_A := by
              show (A.eraseIdx idx)[j] = A[j]
              rw [List.getElem_eraseIdx]
              simp [show ¬(j ≥ idx) from by omega]
            have hA''j_eq : A''[j]'hj = A[j]'hj_A - 3 := by
              show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j] - 3
              rw [show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A'[j] - 3 from by
                rw [List.getElem_map, List.getElem_zipIdx]; simp [hjidx]]
              exact congrArg (· - 3) hA'j_eq
            -- numMultsGe A'' (j+1) ≤ numMultsGe A (j+1) - 1
            -- The fired element at idx was counted in numMultsGe A (j+1) but is removed in A''
            -- Elements between j+1 and idx-1 in A'' are A[k]-3 where k < idx,
            -- and by hno_mult_below these were NOT positive mults of 3, and remain non-mults after -3
            have hcount_eq : numMultsGe A'' (j + 1) ≤ numMultsGe A (j + 1) - 1 := by
              -- Part 1: numMultsGe A'' (j+1) ≤ numMultsGe A (idx+1)
              have hpart1 : numMultsGe A'' (j + 1) ≤ numMultsGe A (idx + 1) := by
                unfold numMultsGe
                suffices hsuff : (A''.drop (j + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) =
                                 (A.drop (idx + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) by
                  rw [hsuff]
                have hdrop_split : A''.drop (j + 1) = (A''.drop (j + 1)).take (idx - (j + 1)) ++ A''.drop idx := by
                  conv_lhs => rw [← List.take_append_drop (idx - (j + 1)) (A''.drop (j + 1))]
                  congr 1
                  rw [List.drop_drop]; congr 1; omega
                rw [hdrop_split, List.filter_append]
                have hprefix_empty : ((A''.drop (j + 1)).take (idx - (j + 1))).filter (fun x => x % 3 == 0 && decide (0 < x)) = [] := by
                  rw [List.filter_eq_nil_iff]
                  intro x hx
                  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]
                  intro hxmod hxpos
                  rw [List.mem_iff_getElem] at hx
                  obtain ⟨i, hi_len, hxi⟩ := hx
                  have hi_bound : i < idx - (j + 1) := by
                    simp [List.length_take, List.length_drop, hA''_len, hA'_len] at hi_len; omega
                  have hpos_in_A'' : j + 1 + i < A''.length := by omega
                  have hget_eq : ((A''.drop (j + 1)).take (idx - (j + 1)))[i]'hi_len = A''[j + 1 + i]'hpos_in_A'' := by
                    simp only [List.getElem_take, List.getElem_drop]
                  rw [hget_eq] at hxi
                  have hlt_idx : j + 1 + i < idx := by omega
                  have hlt_A : j + 1 + i < A.length := by omega
                  have hA''_val : A''[j + 1 + i]'hpos_in_A'' = A[j + 1 + i]'hlt_A - 3 := by
                    show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j + 1 + i] = A[j + 1 + i] - 3
                    rw [List.getElem_map, List.getElem_zipIdx]
                    simp [hlt_idx]; congr 1
                    show (A.eraseIdx idx)[j + 1 + i] = A[j + 1 + i]
                    rw [List.getElem_eraseIdx]
                    simp [show ¬(j + 1 + i ≥ idx) from by omega]
                  rw [hA''_val] at hxi; subst hxi
                  have hge4 : A[j + 1 + i] ≥ 4 := by omega
                  have hAmod : A[j + 1 + i] % 3 = 0 := by omega
                  have hApos : 0 < A[j + 1 + i] := by omega
                  exact absurd ⟨hAmod, hApos⟩ (hno_mult_below (j + 1 + i) hlt_A hlt_idx)
                rw [hprefix_empty, List.nil_append]
                suffices hsuffix : A''.drop idx = A.drop (idx + 1) by rw [hsuffix]
                apply List.ext_getElem
                · simp only [List.length_drop]; omega
                · intro k hk1 hk2
                  have hk_bound : k < A'.length - idx := by
                    simp [List.length_drop, hA''_len] at hk1; omega
                  rw [List.getElem_drop, List.getElem_drop]
                  show (A'.zipIdx |>.map (fun (x, i) => if i < idx then x - 3 else x))[idx + k]'(by simp; omega) = A[idx + 1 + k]'(by omega)
                  rw [List.getElem_map, List.getElem_zipIdx]
                  simp [show ¬(idx + k < idx) from by omega]
                  show (A.eraseIdx idx)[idx + k]'(by simp [List.length_eraseIdx, h]; omega) = A[idx + 1 + k]'(by omega)
                  rw [List.getElem_eraseIdx]
                  simp [show ¬(idx + k < idx) from by omega]
                  congr 1; omega
              -- Part 2: numMultsGe A (j+1) ≥ numMultsGe A (idx+1) + 1
              have hpart2 : numMultsGe A (j + 1) ≥ numMultsGe A (idx + 1) + 1 := by
                unfold numMultsGe
                have hdrop_split : A.drop (j + 1) = (A.drop (j + 1)).take (idx - (j + 1)) ++ A.drop idx := by
                  conv_lhs => rw [← List.take_append_drop (idx - (j + 1)) (A.drop (j + 1))]
                  congr 1
                  rw [List.drop_drop]; congr 1; omega
                rw [hdrop_split, List.filter_append, List.length_append]
                have helem : A.drop idx = A[idx] :: A.drop (idx + 1) := by
                  exact List.drop_eq_getElem_cons h
                rw [helem, List.filter_cons]
                simp [← hval_eq, hmod, hpos]
              omega
            have hfrom_hall := hall j hj_A
            rw [hA''j_eq]
            -- Need: A[j] - 3 ≥ 3 * numMultsGe A'' (j+1)
            -- From hall: A[j] ≥ 3 * numMultsGe A (j+1)
            -- From hcount_eq: numMultsGe A'' (j+1) ≤ numMultsGe A (j+1) - 1
            -- So 3 * numMultsGe A'' (j+1) ≤ 3 * (numMultsGe A (j+1) - 1) = 3 * numMultsGe A (j+1) - 3 ≤ A[j] - 3
            -- But we need numMultsGe A (j+1) ≥ 1 for this to work
            have hcount_ge1 : numMultsGe A (j + 1) ≥ 1 := by
              unfold numMultsGe
              have hidx_in_drop : idx - (j + 1) < (A.drop (j + 1)).length := by
                simp [List.length_drop]; omega
              have hget : (A.drop (j + 1))[idx - (j + 1)] = A[idx] := by
                rw [List.getElem_drop]; congr 1; omega
              suffices hmem : A[idx] ∈ (A.drop (j + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) by
                exact Nat.one_le_iff_ne_zero.mpr (by
                  intro h0
                  rw [List.length_eq_zero_iff] at h0
                  rw [h0] at hmem
                  exact List.not_mem_nil hmem)
              rw [List.mem_filter]
              constructor
              · exact hget ▸ List.getElem_mem hidx_in_drop
              · simp [← hval_eq, hmod, hpos]
            omega
        -- hno_mult_below maintenance for recursive call
        have hno_mult_below' : ∀ j : ℕ, (hj : j < A''.length) → j < idx → ¬(A''[j] % 3 = 0 ∧ 0 < A''[j]) := by
          intro j hj hjidx
          have hA''_len : A''.length = A'.length := by
            show (A'.zipIdx |>.map _).length = A'.length
            simp [List.length_map, List.length_zipIdx]
          have hj_A' : j < A'.length := by omega
          have hj_A : j < A.length := by
            have hlen : A'.length = A.length - 1 := by
              show (A.eraseIdx idx).length = A.length - 1
              simp [List.length_eraseIdx, show idx < A.length from h]
            omega
          -- Key fact: A''[j] = A[j] - 3 (both via eraseIdx and zipIdx-map)
          have hA'j : A'[j]'hj_A' = A[j]'hj_A := by
            show (A.eraseIdx idx)[j] = A[j]
            rw [List.getElem_eraseIdx]
            simp [show ¬(j ≥ idx) from by omega]
          have hA''j_val : A''[j]'hj = A[j]'hj_A - 3 := by
            show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j] - 3
            rw [show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A'[j] - 3 from by
              rw [List.getElem_map, List.getElem_zipIdx]; simp [hjidx]]
            exact congrArg (· - 3) hA'j
          -- From hno_mult_below: ¬(A[j] % 3 = 0 ∧ 0 < A[j])
          have hnmb := hno_mult_below j hj_A hjidx
          rw [hA''j_val]
          intro ⟨hm, hp⟩
          apply hnmb
          constructor
          · -- (A[j] - 3) % 3 = 0 implies A[j] % 3 = 0
            have : A[j]'hj_A ≥ 3 := by omega
            omega
          · -- 0 < A[j] - 3 implies 0 < A[j]
            omega
        have ih_step := ih A'' idx (rec ++ [a + idx]) hall' hno_mult_below'
        -- Weight step
        suffices hsuff : partWeight A'' + 3 * (rec ++ [a + idx]).sum =
            partWeight A + 3 * rec.sum by
          simp only at ih_step ⊢; linarith
        -- Arithmetic
        have hrec_sum : (rec ++ [a + idx]).sum = rec.sum + (a + idx) := by
          simp [List.sum_append]
        rw [hrec_sum]
        unfold partWeight
        have hsum_erase : A.sum = A'.sum + val := by
          show A.sum = (A.eraseIdx idx).sum + val
          rw [hval_eq]; exact sum_eraseIdx_add' A idx h
        have hidx_le : idx ≤ A'.length := by
          show idx ≤ (A.eraseIdx idx).length
          simp only [List.length_eraseIdx, show idx < A.length from h, ite_true]; omega
        have hge3 : ∀ j : ℕ, (hj : j < A'.length) → j < idx → A'[j] ≥ 3 := by
          intro j hj hjidx
          have hj_A : j < A.length := by
            have hlen : A'.length = A.length - 1 := by
              show (A.eraseIdx idx).length = A.length - 1
              simp [List.length_eraseIdx, show idx < A.length from h]
            omega
          have hA'j_eq : A'[j] = A[j] := by
            show (A.eraseIdx idx)[j] = A[j]
            rw [List.getElem_eraseIdx]
            simp [show ¬ (j ≥ idx) from by omega]
          rw [hA'j_eq]
          have hcount : numMultsGe A (j + 1) ≥ 1 := by
            unfold numMultsGe
            have hidx_in_drop : idx - (j + 1) < (A.drop (j + 1)).length := by
              simp [List.length_drop]; omega
            have hget : (A.drop (j + 1))[idx - (j + 1)] = A[idx] := by
              rw [List.getElem_drop]; congr 1; omega
            suffices hmem : A[idx] ∈ (A.drop (j + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) by
              exact Nat.one_le_iff_ne_zero.mpr (by
                intro h0
                rw [List.length_eq_zero_iff] at h0
                rw [h0] at hmem
                exact List.not_mem_nil hmem)
            rw [List.mem_filter]
            constructor
            · exact hget ▸ List.getElem_mem hidx_in_drop
            · simp [← hval_eq, hmod, hpos]
          have := hall j hj_A
          omega
        have hA''_sum : A''.sum + 3 * idx = A'.sum :=
          sum_map_zipIdx_sub3 A' idx hidx_le hge3
        omega
      · -- Skip case: A[idx] is NOT a positive mult of 3
        rename_i hskip
        have hno_mult_below_ext : ∀ j : ℕ, (hj : j < A.length) → j < idx + 1 → ¬(A[j] % 3 = 0 ∧ 0 < A[j]) := by
          intro j hj hjlt
          by_cases hjidx : j < idx
          · exact hno_mult_below j hj hjidx
          · -- j = idx
            have hjeq : j = idx := by omega
            subst hjeq
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hskip
            rw [getElem!_pos A j hj] at hskip
            push_neg at hskip
            intro ⟨hmod3, hpos⟩
            omega
        exact ih A (idx + 1) rec hall hno_mult_below_ext

/-- scanFromSmallest preserves the nonzero residue sequence: it only removes elements
    that are multiples of 3, so the filter for non-multiples is unchanged. -/
private lemma nonzeroResSeq_eraseIdx_of_mult3 (A : List ℕ) (i : ℕ) (hi : i < A.length)
    (hmod : A[i] % 3 = 0) :
    nonzeroResSeq (A.eraseIdx i) = nonzeroResSeq A := by
  unfold nonzeroResSeq
  congr 1
  induction A generalizing i with
  | nil => simp at hi
  | cons a t iht =>
    cases i with
    | zero =>
      simp only [List.eraseIdx_cons_zero, List.getElem_cons_zero] at hmod ⊢
      rw [List.filter_cons]
      simp [hmod]
    | succ j =>
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, List.length_cons] at hmod hi ⊢
      simp only [List.filter_cons]
      split
      · congr 1; exact iht j (by omega) hmod
      · exact iht j (by omega) hmod

private lemma scanFromSmallest_preserves_nonzeroResSeq (fuel : ℕ) (A : List ℕ) (idx : ℕ)
    (rec : List ℕ) (hflat : IsThreeFlat A) :
    nonzeroResSeq (scanFromSmallest fuel A idx rec).1 = nonzeroResSeq A := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromSmallest]
  | succ fuel' ih =>
    simp only [scanFromSmallest]
    split
    · rfl
    · rename_i hidx_lt
      push_neg at hidx_lt
      split
      · -- Flat-removable case
        rename_i hfr
        set actualIdx := A.length - 1 - idx
        have hact : actualIdx < A.length := by omega
        have hmod : A[actualIdx] % 3 = 0 := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          rw [getElem!_pos A actualIdx hact] at hfr
          exact hfr.1.2
        have hflat' : IsThreeFlat (A.eraseIdx actualIdx) := by
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          exact isThreeFlatBool_implies _ hfr.2
        rw [ih (A.eraseIdx actualIdx) idx _ hflat']
        exact nonzeroResSeq_eraseIdx_of_mult3 A actualIdx hact hmod
      · -- Skip case
        exact ih A (idx + 1) rec hflat

/-- Removing a flat-removable element at position k does not make elements at positions j > k
    become flat-removable, provided A is 3-flat. Key transfer lemma for scanFromSmallest. -/
private lemma eraseIdx_preserves_not_flat_removable_right (A : List ℕ) (k j : ℕ)
    (hA_flat : IsThreeFlat A)
    (hkj : k < j) (hj : j < A.length)
    (hk_rem : isFlatRemovableBool A k = true)
    (hj_not_rem : isFlatRemovableBool A j = false) :
    isFlatRemovableBool (A.eraseIdx k) (j - 1) = false := by
  obtain ⟨⟨hpw, hpos_all⟩, hgaps, hlast⟩ := hA_flat
  have hk_lt : k < A.length := Nat.lt_trans hkj hj
  -- Extract A[k] % 3 = 0 from hk_rem
  have hk_mod : A[k]'hk_lt % 3 = 0 := by
    unfold isFlatRemovableBool at hk_rem
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk_rem
    rw [getElem!_pos A k hk_lt] at hk_rem
    exact hk_rem.1.2
  -- Unfold isFlatRemovableBool in hypothesis and goal
  unfold isFlatRemovableBool at hj_not_rem ⊢
  -- Simplify the length conditions
  have hj1_lt : j - 1 < (A.eraseIdx k).length := by
    simp [List.length_eraseIdx, hk_lt]; omega
  simp only [show (decide (j < A.length) : Bool) = true from by simp [hj],
             show (decide (j - 1 < (A.eraseIdx k).length) : Bool) = true from by simp [hj1_lt],
             Bool.true_and] at hj_not_rem ⊢
  -- Show (A.eraseIdx k)[j-1]! = A[j]!
  have hval_eq : (A.eraseIdx k)[j - 1]! = A[j]! := by
    rw [getElem!_pos (A.eraseIdx k) (j - 1) hj1_lt, getElem!_pos A j hj]
    rw [List.getElem_eraseIdx]
    simp [show ¬ (j - 1 < k) from by omega]
    congr 1; omega
  -- Rewrite the goal using hval_eq and the double-eraseIdx commutation
  have h_comm : (A.eraseIdx k).eraseIdx (j - 1) = (A.eraseIdx j).eraseIdx k := by
    apply List.ext_getElem
    · simp [List.length_eraseIdx, hk_lt, hj, show j - 1 < A.length - 1 from by omega,
            show k < A.length - 1 from by omega]
    · intro n h1 h2
      simp only [List.getElem_eraseIdx]
      split_ifs <;> (first | rfl | exfalso; omega)
  rw [hval_eq, h_comm]
  -- Now goal: (A[j]! % 3 == 0 && isThreeFlatBool ((A.eraseIdx j).eraseIdx k)) = false
  -- And hj_not_rem: (A[j]! % 3 == 0 && isThreeFlatBool (A.eraseIdx j)) = false
  -- Case split on A[j]! % 3 == 0
  by_cases hmod : (A[j]! % 3 == 0) = true
  · -- A[j] % 3 = 0 → isThreeFlatBool (A.eraseIdx j) = false
    simp only [hmod, Bool.true_and] at hj_not_rem ⊢
    -- Need: isThreeFlatBool ((A.eraseIdx j).eraseIdx k) = false
    -- hj_not_rem : isThreeFlatBool (A.eraseIdx j) = false
    -- Since A is 3-flat with A[j]%3=0, j cannot be the last index:
    have hj_mod : A[j]'hj % 3 = 0 := by
      rw [← getElem!_pos A j hj]; simpa using hmod
    have hj_not_last : j < A.length - 1 := by
      by_contra h; push_neg at h
      have hj_last : j = A.length - 1 := by omega
      have hne : A ≠ [] := by intro hh; simp [hh] at hj
      have hlast' := hlast hne
      rw [List.getLast_eq_getElem] at hlast'
      have : A[A.length - 1] = A[j] := by congr 1; omega
      rw [this] at hlast'
      have hpos_j : 0 < A[j] := hpos_all _ (List.getElem_mem hj)
      omega
    have hj1 : j + 1 < A.length := by omega
    -- The gap at position j-1 in A.eraseIdx j: A[j-1] - A[j+1] ≥ 3
    have hgap_fail : A[j - 1]'(by omega) - A[j + 1]'hj1 ≥ 3 := by
      by_contra hlt; push_neg at hlt
      have hgap_small : A[j - 1]'(by omega) - A[j + 1]'hj1 < 3 := by omega
      -- Show isThreeFlatBool (A.eraseIdx j) = true, contradicting hj_not_rem
      have hflatBool : isThreeFlatBool (A.eraseIdx j) = true := by
        unfold isThreeFlatBool isPositivePartitionBool
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
        refine ⟨⟨⟨hpw.sublist (List.eraseIdx_sublist A j), ?_⟩, ?_⟩, ?_⟩
        · intro x hx; exact hpos_all x (List.mem_of_mem_eraseIdx hx)
        · intro i hi
          have hlen_e : (A.eraseIdx j).length = A.length - 1 := by
            simp [List.length_eraseIdx, hj]
          rw [hlen_e] at hi
          rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) (by omega)]
          by_cases h1 : i + 1 < j
          · rw [List.getElem_eraseIdx, List.getElem_eraseIdx]
            simp [show i < j from by omega, h1]
            exact hgaps i (by omega)
          · by_cases h2 : i + 1 = j
            · rw [List.getElem_eraseIdx, List.getElem_eraseIdx]
              simp [show i < j from by omega, show ¬(i + 1 < j) from by omega]
              convert hgap_small using 2 <;> (congr 1; omega)
            · rw [List.getElem_eraseIdx, List.getElem_eraseIdx]
              simp [show ¬(i < j) from by omega, show ¬(i + 1 < j) from by omega]
              exact hgaps (i + 1) (by omega)
        · cases hl : (A.eraseIdx j).getLast? with
          | none => simp
          | some x =>
            simp
            have hne : A.eraseIdx j ≠ [] := by intro hh; simp [hh] at hl
            have hne_A : A ≠ [] := by intro hh; simp [hh] at hj
            rw [List.getLast?_eq_some_getLast hne] at hl
            have heq := Option.some.inj hl
            rw [← heq, List.getLast_eq_getElem, List.getElem_eraseIdx]
            have hlen_e : (A.eraseIdx j).length = A.length - 1 := by
              simp [List.length_eraseIdx, hj]
            simp [show ¬((A.eraseIdx j).length - 1 < j) from by rw [hlen_e]; omega]
            have hlast_A := hlast hne_A
            rw [List.getLast_eq_getElem] at hlast_A
            convert hlast_A using 2
            rw [hlen_e]; omega
      rw [hj_not_rem] at hflatBool; exact absurd hflatBool (by decide)
    -- Now show isThreeFlatBool ((A.eraseIdx j).eraseIdx k) = false by contradiction
    by_contra h_true
    rw [Bool.not_eq_false] at h_true
    unfold isThreeFlatBool isPositivePartitionBool at h_true
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h_true
    obtain ⟨⟨⟨_, _⟩, hgaps_de⟩, _⟩ := h_true
    have hlen_ej : (A.eraseIdx j).length = A.length - 1 := by simp [List.length_eraseIdx, hj]
    have hk_lt_ej : k < (A.eraseIdx j).length := by rw [hlen_ej]; omega
    have hlen_de : ((A.eraseIdx j).eraseIdx k).length = A.length - 2 := by
      rw [List.length_eraseIdx_of_lt hk_lt_ej, hlen_ej]; omega
    -- Case split on k vs j-1
    by_cases hkj1 : k < j - 1
    · -- Case k < j-1: gap at j-2 = A[j-1] - A[j+1] ≥ 3
      have hpos_j2 : j - 2 < ((A.eraseIdx j).eraseIdx k).length - 1 := by omega
      have hgap_j2 := hgaps_de (j - 2) hpos_j2
      rw [getElem!_pos _ (j - 2) (by omega), getElem!_pos _ (j - 2 + 1) (by omega)] at hgap_j2
      -- Compute (double-erased)[j-2] and (double-erased)[j-1] via getElem_eraseIdx
      have hv1 : ((A.eraseIdx j).eraseIdx k)[j - 2]'(by omega) = A[j - 1]'(by omega) := by
        simp only [List.getElem_eraseIdx]
        split_ifs <;> (first | omega | congr 1; omega)
      have hv2 : ((A.eraseIdx j).eraseIdx k)[j - 2 + 1]'(by omega) = A[j + 1]'hj1 := by
        simp only [List.getElem_eraseIdx]
        split_ifs <;> (first | omega | congr 1; omega)
      rw [hv1, hv2] at hgap_j2
      omega
    · -- Case k = j-1
      have hk_eq : k = j - 1 := by omega
      have hk_mod' : A[j - 1]'(by omega) % 3 = 0 := by
        have : A[k]'hk_lt = A[j - 1]'(by omega) := by congr 1
        rw [← this]; exact hk_mod
      -- A[j-1] - A[j] < 3 (from hgaps at position j-1)
      have hgap_jm1 : A[j - 1]'(by omega) - A[j]'hj < 3 := by
        have := hgaps (j - 1) (by omega)
        convert this using 2; congr 1; omega
      -- A[j-1] ≥ A[j] (from pairwise)
      have hge_jm1 : A[j - 1]'(by omega) ≥ A[j]'hj :=
        List.pairwise_iff_getElem.mp hpw (j-1) j (by omega) hj (by omega)
      -- A[j-1] - A[j] ≡ 0 mod 3
      have hdiff_mod : (A[j - 1]'(by omega) - A[j]'hj) % 3 = 0 := by omega
      -- A[j-1] - A[j] < 3 and ≥ 0 and ≡ 0 mod 3 → A[j-1] - A[j] = 0
      have hdiff_zero : A[j - 1]'(by omega) - A[j]'hj = 0 := by omega
      -- So A[j-1] = A[j]
      have heq_jm1_j : A[j - 1]'(by omega) = A[j]'hj := by omega
      -- A[j] - A[j+1] < 3 (from hgaps at position j)
      have hgap_j : A[j]'hj - A[j + 1]'hj1 < 3 := hgaps j hj1
      -- A[j-1] - A[j+1] = A[j] - A[j+1] < 3
      have : A[j - 1]'(by omega) - A[j + 1]'hj1 < 3 := by rw [heq_jm1_j]; exact hgap_j
      -- Contradicts hgap_fail ≥ 3
      omega
  · -- A[j]! % 3 ≠ 0 → first conjunct is false → whole conjunction is false
    simp only [show (A[j]! % 3 == 0) = false from by simpa using hmod, Bool.false_and]

/-- After scanFromSmallest with sufficient fuel starting from idx=0,
    no position in the output is flat-removable. -/
private lemma scanFromSmallest_no_flat_removable (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hA_flat : IsThreeFlat A)
    (hfuel : fuel + idx ≥ A.length)
    (hprev : ∀ i : ℕ, (hi : i < A.length) → i ≥ A.length - idx →
      isFlatRemovableBool A i = false) :
    let A₂ := (scanFromSmallest fuel A idx rec).1
    ∀ i : ℕ, (hi : i < A₂.length) → isFlatRemovableBool A₂ i = false := by
  induction fuel generalizing A idx rec with
  | zero =>
    simp only [scanFromSmallest]
    intro i hi
    exact hprev i hi (by omega)
  | succ fuel' ih =>
    simp only [scanFromSmallest]
    split
    · -- idx ≥ A.length
      rename_i hidx_ge
      intro i hi
      exact hprev i hi (by omega)
    · -- idx < A.length
      rename_i hidx_lt
      push_neg at hidx_lt
      split
      · -- flat-removable: remove and recurse with same idx
        rename_i hrem
        -- A.eraseIdx(actualIdx) is 3-flat since actualIdx is flat-removable
        have hA'_flat : IsThreeFlat (A.eraseIdx (A.length - 1 - idx)) := by
          have hfr := hrem
          unfold isFlatRemovableBool at hfr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hfr
          exact isThreeFlatBool_implies _ hfr.2
        apply ih _ _ _ hA'_flat
        · simp [List.length_eraseIdx, show A.length - 1 - idx < A.length from by omega]; omega
        · intro i hi hge
          have hlen_e : (A.eraseIdx (A.length - 1 - idx)).length = A.length - 1 := by
            simp [List.length_eraseIdx, show A.length - 1 - idx < A.length from by omega]
          have hi_A : i + 1 < A.length := by omega
          have hge_A : i + 1 ≥ A.length - idx := by omega
          have hj_not_rem : isFlatRemovableBool A (i + 1) = false := hprev (i + 1) hi_A hge_A
          have hkj : A.length - 1 - idx < i + 1 := by omega
          exact eraseIdx_preserves_not_flat_removable_right A (A.length - 1 - idx) (i + 1)
            hA_flat hkj hi_A hrem hj_not_rem
      · -- not flat-removable: skip and recurse with idx+1
        rename_i hnotrem
        apply ih _ _ _ hA_flat
        · omega
        · intro i hi hge
          by_cases h : i ≥ A.length - idx
          · exact hprev i hi h
          · have : i = A.length - 1 - idx := by omega
            rw [this]
            exact eq_false_of_ne_true hnotrem

set_option maxHeartbeats 400000 in
/-- In a 3-flat list, if a positive multiple of 3 at an interior position i
    (0 < i < length - 1) is NOT flat-removable, then removing it would break 3-flatness,
    which means the gap A[i-1] - A[i+1] ≥ 3. -/
private lemma not_flat_removable_interior_gap (A : List ℕ) (i : ℕ)
    (hflat : IsThreeFlat A)
    (hi : i < A.length) (hi_pos : 0 < i) (hi_not_last : i < A.length - 1)
    (hmod : A[i] % 3 = 0) (hpos : 0 < A[i])
    (hnotrem : isFlatRemovableBool A i = false) :
    A[i - 1]'(by omega) - A[i + 1]'(by omega) ≥ 3 := by
  -- From hnotrem, extract that isThreeFlatBool (A.eraseIdx i) = false
  have hnotflat : isThreeFlatBool (A.eraseIdx i) = false := by
    unfold isFlatRemovableBool at hnotrem
    have h1 : (decide (i < A.length) : Bool) = true := by simp [hi]
    have h2 : (A[i]! % 3 == 0) = true := by
      rw [getElem!_pos A i hi]; simp [hmod]
    simp only [h1, h2, Bool.true_and] at hnotrem
    exact hnotrem
  -- Proof by contradiction: assume A[i-1] - A[i+1] < 3
  by_contra hlt
  push_neg at hlt
  have hgap_small : A[i - 1]'(by omega) - A[i + 1]'(by omega) < 3 := by omega
  -- Show isThreeFlatBool (A.eraseIdx i) = true, contradicting hnotflat
  obtain ⟨⟨hpw, hpos_all⟩, hgaps, hlast⟩ := hflat
  have hflatBool : isThreeFlatBool (A.eraseIdx i) = true := by
    unfold isThreeFlatBool isPositivePartitionBool
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨hpw.sublist (List.eraseIdx_sublist A i), ?_⟩, ?_⟩, ?_⟩
    · intro x hx
      exact hpos_all x (List.mem_of_mem_eraseIdx hx)
    · intro j hj
      have hlen_erased : (A.eraseIdx i).length = A.length - 1 := by
        simp [List.length_eraseIdx, hi]
      rw [hlen_erased] at hj
      by_cases h1 : j + 1 < i
      · -- Both j and j+1 are before i
        have hv1 : (A.eraseIdx i)[j]! = A[j] := by
          rw [getElem!_pos _ j (by omega)]
          rw [List.getElem_eraseIdx]; simp [show j < i from by omega]
        have hv2 : (A.eraseIdx i)[j+1]! = A[j+1] := by
          rw [getElem!_pos _ (j+1) (by omega)]
          rw [List.getElem_eraseIdx]; simp [h1]
        rw [hv1, hv2]
        exact hgaps j (by omega)
      · by_cases h2 : j + 1 = i
        · -- j = i-1, j+1 = i: the splice point
          have hv1 : (A.eraseIdx i)[j]! = A[i-1] := by
            rw [getElem!_pos _ j (by omega)]
            rw [List.getElem_eraseIdx]; simp [show j < i from by omega]
            congr 1; omega
          have hv2 : (A.eraseIdx i)[j+1]! = A[i+1] := by
            rw [getElem!_pos _ (j+1) (by omega)]
            rw [List.getElem_eraseIdx]; simp [show ¬(j + 1 < i) from by omega]
            congr 1; omega
          rw [hv1, hv2]
          exact hgap_small
        · -- Both j and j+1 are at or after i
          have hv1 : (A.eraseIdx i)[j]! = A[j+1] := by
            rw [getElem!_pos _ j (by omega)]
            rw [List.getElem_eraseIdx]; simp [show ¬(j < i) from by omega]
          have hv2 : (A.eraseIdx i)[j+1]! = A[j+2] := by
            rw [getElem!_pos _ (j+1) (by omega)]
            rw [List.getElem_eraseIdx]; simp [show ¬(j+1 < i) from by omega]
          rw [hv1, hv2]
          exact hgaps (j+1) (by omega)
    · -- Last element condition
      cases hl : (A.eraseIdx i).getLast? with
      | none => simp
      | some x =>
        simp
        have hne : A.eraseIdx i ≠ [] := by
          intro h; simp [h] at hl
        have hne_A : A ≠ [] := by intro h; simp [h] at hi
        rw [List.getLast?_eq_some_getLast hne] at hl
        have heq := Option.some.inj hl
        rw [← heq]
        rw [List.getLast_eq_getElem]
        have hlen_erased : (A.eraseIdx i).length = A.length - 1 := by
          simp [List.length_eraseIdx, hi]
        rw [List.getElem_eraseIdx]
        have hlast_A := hlast hne_A
        rw [List.getLast_eq_getElem] at hlast_A
        have h_not_last : ¬((A.eraseIdx i).length - 1 < i) := by
          rw [hlen_erased]; omega
        simp [h_not_last]
        convert hlast_A using 1
        congr 1
        rw [hlen_erased]
        omega
  rw [hnotflat] at hflatBool
  exact absurd hflatBool (by decide)

/-- In a 3-flat list with no flat-removable elements, no two consecutive positions
    can both be positive multiples of 3. -/
private lemma no_consecutive_pos_mults (A : List ℕ) (j : ℕ)
    (hflat : IsThreeFlat A)
    (hj : j + 1 < A.length)
    (hnotrem : ∀ i : ℕ, (hi : i < A.length) → isFlatRemovableBool A i = false)
    (hmod1 : A[j]'(by omega) % 3 = 0) (hpos1 : 0 < A[j]'(by omega))
    (hmod2 : A[j + 1] % 3 = 0) (hpos2 : 0 < A[j + 1]) :
    False := by
  obtain ⟨⟨hpw, hposA⟩, hgap, hlast⟩ := hflat
  -- Case split: is j+1 the last index?
  by_cases hlast_idx : j + 1 = A.length - 1
  · -- j+1 is last: A[j+1] is the last element, so < 3, but ≥ 3 since positive mult of 3
    have hne : A ≠ [] := by intro h; simp [h] at hj
    have hlast2 := hlast hne
    rw [List.getLast_eq_getElem] at hlast2
    have heq : A[A.length - 1] = A[j + 1] := by congr 1; omega
    rw [heq] at hlast2
    -- A[j+1] % 3 = 0 and A[j+1] > 0 implies A[j+1] >= 3
    omega
  · -- j+1 is not last: show isFlatRemovableBool A (j+1) = true
    have hj1_lt : j + 1 < A.length := hj
    have hj1_not_last : j + 1 < A.length - 1 := by omega
    have hj2_lt : j + 2 < A.length := by omega
    -- Show A[j] = A[j+1] (both positive multiples of 3 with gap < 3 and A[j] >= A[j+1])
    have hgap_j := hgap j (by omega : j + 1 < A.length)
    have hge : A[j]'(by omega) ≥ A[j + 1] := by
      exact List.pairwise_iff_getElem.mp hpw j (j + 1) (by omega) hj1_lt (by omega)
    -- A[j] - A[j+1] < 3, and both are multiples of 3 with A[j] >= A[j+1]
    -- So A[j] = A[j+1]
    have heq_vals : A[j]'(by omega) = A[j + 1] := by
      have h3_div1 : 3 ∣ A[j]'(by omega) := Nat.dvd_of_mod_eq_zero hmod1
      have h3_div2 : 3 ∣ A[j + 1] := Nat.dvd_of_mod_eq_zero hmod2
      obtain ⟨k1, hk1⟩ := h3_div1
      obtain ⟨k2, hk2⟩ := h3_div2
      rw [hk1, hk2] at hgap_j hge ⊢
      omega
    -- Now show isFlatRemovableBool A (j+1) = true
    have hrem : isFlatRemovableBool A (j + 1) = true := by
      unfold isFlatRemovableBool
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨hj1_lt, ?_⟩, ?_⟩
      · rw [getElem!_pos A (j + 1) hj1_lt]; exact hmod2
      · -- Show isThreeFlatBool (A.eraseIdx (j+1)) = true
        unfold isThreeFlatBool isPositivePartitionBool
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
        have hlen_e : (A.eraseIdx (j + 1)).length = A.length - 1 := by
          simp [List.length_eraseIdx, hj1_lt]
        refine ⟨⟨⟨hpw.sublist (List.eraseIdx_sublist A (j + 1)), ?_⟩, ?_⟩, ?_⟩
        · -- positivity
          intro x hx; exact hposA x (List.mem_of_mem_eraseIdx hx)
        · -- gap condition
          intro i hi
          have hi_lt : i + 1 < (A.eraseIdx (j + 1)).length := by omega
          -- Three cases: i+1 < j+1, i = j (the splice), i >= j+1
          by_cases h1 : i + 1 < j + 1
          · -- Both i and i+1 are before the erased index
            have hv1 : (A.eraseIdx (j + 1))[i]! = A[i]'(by omega) := by
              rw [getElem!_pos _ i (by omega), List.getElem_eraseIdx]
              simp [show i < j + 1 from by omega]
            have hv2 : (A.eraseIdx (j + 1))[i + 1]! = A[i + 1]'(by omega) := by
              rw [getElem!_pos _ (i + 1) (by omega), List.getElem_eraseIdx]
              simp [h1]
            rw [hv1, hv2]; exact hgap i (by omega)
          · by_cases h2 : i = j
            · -- i = j: splice position. erased[j] = A[j], erased[j+1] = A[j+2]
              have hv1 : (A.eraseIdx (j + 1))[i]! = A[j]'(by omega) := by
                rw [getElem!_pos _ i (by omega), List.getElem_eraseIdx]
                simp [show i < j + 1 from by omega, h2]
              have hv2 : (A.eraseIdx (j + 1))[i + 1]! = A[j + 2]'(by omega) := by
                rw [getElem!_pos _ (i + 1) (by omega), List.getElem_eraseIdx]
                simp [show ¬(i + 1 < j + 1) from by omega]
                congr 1; omega
              rw [hv1, hv2, heq_vals]
              exact hgap (j + 1) (by omega)
            · -- i+1 > j+1: both shifted
              have hi_ge : i ≥ j + 1 := by omega
              have hv1 : (A.eraseIdx (j + 1))[i]! = A[i + 1]'(by omega) := by
                rw [getElem!_pos _ i (by omega), List.getElem_eraseIdx]
                simp [show ¬(i < j + 1) from by omega]
              have hv2 : (A.eraseIdx (j + 1))[i + 1]! = A[i + 2]'(by omega) := by
                rw [getElem!_pos _ (i + 1) (by omega), List.getElem_eraseIdx]
                simp [show ¬(i + 1 < j + 1) from by omega]
              rw [hv1, hv2]; exact hgap (i + 1) (by omega)
        · -- last element condition
          cases hl : (A.eraseIdx (j + 1)).getLast? with
          | none => simp
          | some x =>
            simp
            have hne : A.eraseIdx (j + 1) ≠ [] := by
              intro h; simp [h] at hl
            have hne_A : A ≠ [] := by intro h; simp [h] at hj
            have hlast_A := hlast hne_A
            rw [List.getLast_eq_getElem] at hlast_A
            rw [List.getLast?_eq_some_getLast hne] at hl
            have heq_x := Option.some.inj hl
            rw [← heq_x]
            simp only [List.getLast_eq_getElem, hlen_e]
            rw [List.getElem_eraseIdx]
            have hnotlt : ¬(A.length - 1 - 1 < j + 1) := by omega
            simp [hnotlt]
            convert hlast_A using 2
            omega
    -- Now derive contradiction from hnotrem
    have hcontra := hnotrem (j + 1) hj1_lt
    simp [hrem] at hcontra

private lemma post_s2_numMultsGe_bound (l : List ℕ) (hflat : IsThreeFlat l) :
    let A₂ := (scanFromSmallest (l.length + 1) l 0 []).1
    ∀ j : ℕ, (hj : j < A₂.length) → A₂[j] ≥ 3 * numMultsGe A₂ (j + 1) := by
  set A₂ := (scanFromSmallest (l.length + 1) l 0 []).1
  have hflat2 : IsThreeFlat A₂ := scanFromSmallest_isThreeFlat (l.length + 1) l 0 [] hflat
  obtain ⟨⟨hpw, hpos⟩, hgap, hlast⟩ := hflat2
  -- Key property: no flat-removable elements remain
  have hno_rem : ∀ i : ℕ, (hi : i < A₂.length) → isFlatRemovableBool A₂ i = false :=
    scanFromSmallest_no_flat_removable (l.length + 1) l 0 [] hflat (by omega)
      (fun i hi hgt => absurd hgt (by omega))
  -- Prove by strong induction on suffix length
  suffices hsuff : ∀ d : ℕ, ∀ j : ℕ, (hj : j < A₂.length) → A₂.length - 1 - j ≤ d →
      A₂[j] ≥ 3 * numMultsGe A₂ (j + 1) from
    fun j hj => hsuff (A₂.length - 1 - j) j hj (Nat.le_refl _)
  intro d
  induction d with
  | zero =>
    intro j hj hd
    unfold numMultsGe
    have hdrop : A₂.drop (j + 1) = [] := by rw [List.drop_eq_nil_iff]; omega
    rw [hdrop]; simp
  | succ d ih =>
    intro j hj hd
    -- If j is last, handle directly
    by_cases hj_last : j = A₂.length - 1
    · unfold numMultsGe
      have hdrop : A₂.drop (j + 1) = [] := by rw [List.drop_eq_nil_iff]; omega
      rw [hdrop]; simp
    · have hj1 : j + 1 < A₂.length := by omega
      have ih_j1 := ih (j + 1) hj1 (by omega)
      have hdrop_cons : A₂.drop (j + 1) = A₂[j + 1] :: A₂.drop (j + 2) :=
        List.drop_eq_getElem_cons hj1
      have hge : A₂[j] ≥ A₂[j + 1] :=
        List.pairwise_iff_getElem.mp hpw j (j + 1) (by omega) hj1 (by omega)
      by_cases hmult : A₂[j + 1] % 3 = 0 ∧ 0 < A₂[j + 1]
      · -- A₂[j+1] is a positive mult of 3
        have h_count : numMultsGe A₂ (j + 1) = numMultsGe A₂ (j + 2) + 1 := by
          unfold numMultsGe; rw [hdrop_cons, List.filter_cons]
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          simp [hmult.1, hmult.2]
        rw [h_count]
        -- j+1 is at an interior position
        by_cases hj1_last : j + 1 = A₂.length - 1
        · -- j+1 is last: numMultsGe A₂ (j+2) = 0, need A₂[j] ≥ 3
          unfold numMultsGe
          have hdrop2 : A₂.drop (j + 2) = [] := by rw [List.drop_eq_nil_iff]; omega
          rw [hdrop2]; simp
          -- A₂[j] ≥ A₂[j+1] ≥ 3 (since A₂[j+1] is a positive mult of 3)
          omega
        · -- j+1 is not last: use gap witness
          have hj2_lt : j + 2 < A₂.length := by omega
          -- Gap property from not_flat_removable_interior_gap
          have hgap3 : A₂[j]'(by omega) - A₂[j + 2]'hj2_lt ≥ 3 :=
            not_flat_removable_interior_gap A₂ (j + 1) ⟨⟨hpw, hpos⟩, hgap, hlast⟩
              hj1 (by omega) (by omega) hmult.1 hmult.2 (hno_rem (j + 1) hj1)
          -- No two consecutive positions can both be positive mults of 3
          have hj2_not_mult : ¬(A₂[j + 2]'hj2_lt % 3 = 0 ∧ 0 < A₂[j + 2]'hj2_lt) := by
            intro ⟨hmod2, hpos2⟩
            exact no_consecutive_pos_mults A₂ (j + 1) ⟨⟨hpw, hpos⟩, hgap, hlast⟩
              (by omega) hno_rem hmult.1 hmult.2 hmod2 hpos2
          -- numMultsGe A₂ (j+2) = numMultsGe A₂ (j+3) since A₂[j+2] is not a positive mult
          have h_count2 : numMultsGe A₂ (j + 2) = numMultsGe A₂ (j + 3) := by
            unfold numMultsGe
            have hdrop2 : A₂.drop (j + 2) = A₂[j + 2]'hj2_lt :: A₂.drop (j + 3) :=
              List.drop_eq_getElem_cons hj2_lt
            rw [hdrop2, List.filter_cons]
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
            simp [hj2_not_mult]
          -- IH at j+2: A₂[j+2] ≥ 3 * numMultsGe A₂ (j+3)
          have ih_j2 : A₂[j + 2] ≥ 3 * numMultsGe A₂ (j + 3) :=
            ih (j + 2) hj2_lt (by omega)
          -- Combine: A₂[j] ≥ A₂[j+2] + 3 ≥ 3*numMultsGe A₂(j+3) + 3 = 3*(numMultsGe A₂(j+2)+1)
          omega
      · -- A₂[j+1] is NOT a positive mult of 3
        have h_count : numMultsGe A₂ (j + 1) = numMultsGe A₂ (j + 2) := by
          unfold numMultsGe; rw [hdrop_cons, List.filter_cons]
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          simp [hmult]
        rw [h_count]; linarith

private lemma map_zipIdx_shift' (l : List ℕ) (k start : ℕ) :
    List.map (fun x : ℕ × ℕ => if x.2 < k + 1 then x.1 - 3 else x.1) (l.zipIdx (start + 1)) =
    List.map (fun x : ℕ × ℕ => if x.2 < k then x.1 - 3 else x.1) (l.zipIdx start) := by
  induction l generalizing start with
  | nil => simp
  | cons a t ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    congr 1
    · simp only [show start + 1 < k + 1 ↔ start < k from by omega]
    · exact ih (start + 1)

private lemma nonzeroResSeq_zipIdx_map_eraseIdx (A : List ℕ) (idx : ℕ) (hidx : idx < A.length)
    (hval_mod : A[idx] % 3 = 0)
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j]))
    (hge3 : ∀ j : ℕ, (hj : j < A.length) → j < idx → A[j] ≥ 3) :
    nonzeroResSeq ((A.eraseIdx idx).zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x))
    = nonzeroResSeq A := by
  induction A generalizing idx with
  | nil => simp at hidx
  | cons a t ih =>
    cases idx with
    | zero =>
      simp only [List.getElem_cons_zero] at hval_mod
      simp only [List.eraseIdx_cons_zero, Nat.not_lt_zero, ite_false, List.zipIdx_map_fst]
      unfold nonzeroResSeq; rw [List.filter_cons]; simp [beq_iff_eq, hval_mod]
    | succ k =>
      have ha_not_mult : ¬(a % 3 = 0 ∧ 0 < a) := hno_mult_below 0 (by omega) (by omega)
      have ha_ge3 : a ≥ 3 := hge3 0 (by omega) (by omega)
      have ha_mod : ¬(a % 3 = 0) := fun h => ha_not_mult ⟨h, by omega⟩
      simp only [List.eraseIdx_cons_succ]
      rw [show (a :: t.eraseIdx k).zipIdx = (a :: t.eraseIdx k).zipIdx 0 from rfl,
          List.zipIdx_cons]
      simp only [List.map_cons, show (0 : ℕ) < k + 1 from by omega, ite_true]
      rw [map_zipIdx_shift' (t.eraseIdx k) k 0]
      have hk_lt : k < t.length := by simpa using hidx
      have hval_mod' : t[k] % 3 = 0 := by simpa using hval_mod
      have hno_mult' : ∀ j : ℕ, (hj : j < t.length) → j < k → ¬(t[j] % 3 = 0 ∧ 0 < t[j]) := by
        intro j hj hjk; exact hno_mult_below (j + 1) (by simp; omega) (by omega)
      have hge3' : ∀ j : ℕ, (hj : j < t.length) → j < k → t[j] ≥ 3 := by
        intro j hj hjk; exact hge3 (j + 1) (by simp; omega) (by omega)
      have ih_result := ih k hk_lt hval_mod' hno_mult' hge3'
      unfold nonzeroResSeq at ih_result ⊢
      rw [List.filter_cons, List.filter_cons]
      have ha_sub_mod : ¬((a - 3) % 3 = 0) := by omega
      simp only [beq_iff_eq, ha_sub_mod, ha_mod, not_false_eq_true, decide_not, decide_eq_true_eq,
                 ite_true, List.map_cons]
      rw [show (a - 3) % 3 = a % 3 from by omega]
      congr 1
      convert ih_result using 2 <;> ext x <;> simp [beq_iff_eq]

set_option maxHeartbeats 800000 in
/-- Hall maintenance: after erasing a positive mult-of-3 at idx and subtracting 3
    from positions below idx, the hall bound is preserved. -/
private lemma scanFromLargest_fire_hall_maintenance (A : List ℕ) (idx : ℕ)
    (hidx : idx < A.length)
    (hmod : A[idx] % 3 = 0) (hpos : 0 < A[idx])
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j])) :
    let A' := A.eraseIdx idx
    let A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
    ∀ j : ℕ, (hj : j < A''.length) → A''[j] ≥ 3 * numMultsGe A'' (j + 1) := by
  intro A' A'' j hj
  have hA''_len : A''.length = A'.length := by
    show (A'.zipIdx |>.map _).length = A'.length
    simp [List.length_map, List.length_zipIdx]
  have hA'_len : A'.length = A.length - 1 := by
    show (A.eraseIdx idx).length = A.length - 1
    simp [List.length_eraseIdx, show idx < A.length from hidx]
  by_cases hjidx : j ≥ idx
  · -- Case j ≥ idx: A''[j] = A[j+1] (shifted by eraseIdx, no subtraction)
    have hj_A' : j < A'.length := by omega
    have hjp1_A : j + 1 < A.length := by omega
    have hA'j_eq : A'[j]'hj_A' = A[j + 1]'hjp1_A := by
      show (A.eraseIdx idx)[j] = A[j + 1]
      rw [List.getElem_eraseIdx]
      have : ¬(j < idx) := by omega
      simp [this]
    have hA''j_eq : A''[j]'hj = A[j + 1]'hjp1_A := by
      show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j + 1]
      rw [show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A'[j] from by
        rw [List.getElem_map, List.getElem_zipIdx]; simp [show ¬(j < idx) from by omega]]
      exact hA'j_eq
    have hcount_le : numMultsGe A'' (j + 1) ≤ numMultsGe A (j + 2) := by
      unfold numMultsGe
      suffices heq : A''.drop (j + 1) = A.drop (j + 2) by rw [heq]
      apply List.ext_getElem
      · simp only [List.length_drop]; omega
      · intro k hk1 hk2
        have hk2' : j + 2 + k < A.length := by
          simp [List.length_drop] at hk2; omega
        rw [List.getElem_drop, List.getElem_drop]
        show (A'.zipIdx |>.map (fun (x, i) => if i < idx then x - 3 else x))[j + 1 + k]'(by
          simp [List.length_map, List.length_zipIdx]
          simp [List.length_drop] at hk1; omega) = A[j + 2 + k]'hk2'
        rw [List.getElem_map, List.getElem_zipIdx]
        simp [show ¬(j + 1 + k < idx) from by omega]
        show (A.eraseIdx idx)[j + 1 + k]'(by
          show j + 1 + k < (A.eraseIdx idx).length
          simp [List.length_eraseIdx, hidx]; omega) = A[j + 2 + k]'hk2'
        rw [List.getElem_eraseIdx]
        simp [show ¬(j + 1 + k < idx) from by omega]
        congr 1; omega
    have hfrom_hall := hall (j + 1) hjp1_A
    rw [hA''j_eq]
    calc A[j + 1] ≥ 3 * numMultsGe A (j + 2) := hfrom_hall
      _ ≥ 3 * numMultsGe A'' (j + 1) := by omega
  · -- Case j < idx: A''[j] = A[j] - 3
    push_neg at hjidx
    have hj_A' : j < A'.length := by omega
    have hj_A : j < A.length := by omega
    have hA'j_eq : A'[j]'hj_A' = A[j]'hj_A := by
      show (A.eraseIdx idx)[j] = A[j]
      rw [List.getElem_eraseIdx]
      simp [show ¬(j ≥ idx) from by omega]
    have hA''j_eq : A''[j]'hj = A[j]'hj_A - 3 := by
      show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j] - 3
      rw [show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A'[j] - 3 from by
        rw [List.getElem_map, List.getElem_zipIdx]; simp [hjidx]]
      exact congrArg (· - 3) hA'j_eq
    have hcount_eq : numMultsGe A'' (j + 1) ≤ numMultsGe A (j + 1) - 1 := by
      have hpart1 : numMultsGe A'' (j + 1) ≤ numMultsGe A (idx + 1) := by
        unfold numMultsGe
        suffices hsuff : (A''.drop (j + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) =
                         (A.drop (idx + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) by
          rw [hsuff]
        have hdrop_split : A''.drop (j + 1) = (A''.drop (j + 1)).take (idx - (j + 1)) ++ A''.drop idx := by
          conv_lhs => rw [← List.take_append_drop (idx - (j + 1)) (A''.drop (j + 1))]
          congr 1
          rw [List.drop_drop]; congr 1; omega
        rw [hdrop_split, List.filter_append]
        have hprefix_empty : ((A''.drop (j + 1)).take (idx - (j + 1))).filter (fun x => x % 3 == 0 && decide (0 < x)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]
          intro hxmod hxpos
          rw [List.mem_iff_getElem] at hx
          obtain ⟨i, hi_len, hxi⟩ := hx
          have hi_bound : i < idx - (j + 1) := by
            simp [List.length_take, List.length_drop, hA''_len, hA'_len] at hi_len; omega
          have hpos_in_A'' : j + 1 + i < A''.length := by omega
          have hget_eq : ((A''.drop (j + 1)).take (idx - (j + 1)))[i]'hi_len = A''[j + 1 + i]'hpos_in_A'' := by
            simp only [List.getElem_take, List.getElem_drop]
          rw [hget_eq] at hxi
          have hlt_idx : j + 1 + i < idx := by omega
          have hlt_A : j + 1 + i < A.length := by omega
          have hA''_val : A''[j + 1 + i]'hpos_in_A'' = A[j + 1 + i]'hlt_A - 3 := by
            show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j + 1 + i] = A[j + 1 + i] - 3
            rw [List.getElem_map, List.getElem_zipIdx]
            simp [hlt_idx]; congr 1
            show (A.eraseIdx idx)[j + 1 + i] = A[j + 1 + i]
            rw [List.getElem_eraseIdx]
            simp [show ¬(j + 1 + i ≥ idx) from by omega]
          rw [hA''_val] at hxi; subst hxi
          have hge4 : A[j + 1 + i] ≥ 4 := by omega
          have hAmod : A[j + 1 + i] % 3 = 0 := by omega
          have hApos : 0 < A[j + 1 + i] := by omega
          exact absurd ⟨hAmod, hApos⟩ (hno_mult_below (j + 1 + i) hlt_A hlt_idx)
        rw [hprefix_empty, List.nil_append]
        suffices hsuffix : A''.drop idx = A.drop (idx + 1) by rw [hsuffix]
        apply List.ext_getElem
        · simp only [List.length_drop]; omega
        · intro k hk1 hk2
          have hk_bound : k < A'.length - idx := by
            simp [List.length_drop, hA''_len] at hk1; omega
          rw [List.getElem_drop, List.getElem_drop]
          show (A'.zipIdx |>.map (fun (x, i) => if i < idx then x - 3 else x))[idx + k]'(by simp; omega) = A[idx + 1 + k]'(by omega)
          rw [List.getElem_map, List.getElem_zipIdx]
          simp [show ¬(idx + k < idx) from by omega]
          show (A.eraseIdx idx)[idx + k]'(by simp [List.length_eraseIdx, hidx]; omega) = A[idx + 1 + k]'(by omega)
          rw [List.getElem_eraseIdx]
          simp [show ¬(idx + k < idx) from by omega]
          congr 1; omega
      have hpart2 : numMultsGe A (j + 1) ≥ numMultsGe A (idx + 1) + 1 := by
        unfold numMultsGe
        have hdrop_split : A.drop (j + 1) = (A.drop (j + 1)).take (idx - (j + 1)) ++ A.drop idx := by
          conv_lhs => rw [← List.take_append_drop (idx - (j + 1)) (A.drop (j + 1))]
          congr 1
          rw [List.drop_drop]; congr 1; omega
        rw [hdrop_split, List.filter_append, List.length_append]
        have helem : A.drop idx = A[idx] :: A.drop (idx + 1) := by
          exact List.drop_eq_getElem_cons hidx
        rw [helem, List.filter_cons]
        simp [hmod, hpos]
      omega
    have hfrom_hall := hall j hj_A
    rw [hA''j_eq]
    have hcount_ge1 : numMultsGe A (j + 1) ≥ 1 := by
      unfold numMultsGe
      have hidx_in_drop : idx - (j + 1) < (A.drop (j + 1)).length := by
        simp [List.length_drop]; omega
      have hget : (A.drop (j + 1))[idx - (j + 1)] = A[idx] := by
        rw [List.getElem_drop]; congr 1; omega
      suffices hmem : A[idx] ∈ (A.drop (j + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) by
        exact Nat.one_le_iff_ne_zero.mpr (by
          intro h0
          rw [List.length_eq_zero_iff] at h0
          rw [h0] at hmem
          exact List.not_mem_nil hmem)
      rw [List.mem_filter]
      constructor
      · exact hget ▸ List.getElem_mem hidx_in_drop
      · simp [hmod, hpos]
    omega

set_option maxHeartbeats 800000 in
/-- scanFromLargest produces a 3-flat result when started on a 3-flat input
    satisfying the `hall` bound and where no remaining mult-of-3 is flat-removable. -/
private lemma fire_step_isThreeFlat (A : List ℕ) (idx : ℕ)
    (hflat : IsThreeFlat A)
    (hidx : idx < A.length)
    (hmod : A[idx] % 3 = 0) (hpos : 0 < A[idx])
    (hnoFR : ∀ j : ℕ, (hj : j < A.length) → isFlatRemovableBool A j = false)
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j])) :
    let A' := A.eraseIdx idx
    let A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
    IsThreeFlat A'' := by
  intro A' A''
  have hflat' := hflat
  obtain ⟨⟨hpw, hpos_all⟩, hgaps, hlast⟩ := hflat
  have hA'_len : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx, hidx]
  have hA''_len : A''.length = A.length - 1 := by
    simp [A'', List.length_map, List.length_zipIdx, hA'_len]
  have hidx_not_last : idx < A.length - 1 := by
    by_contra h
    push_neg at h
    have hidx_eq : idx = A.length - 1 := by omega
    have hne : A ≠ [] := by intro h; simp [h] at hidx
    have hlast_val := hlast hne
    rw [List.getLast_eq_getElem] at hlast_val
    have : A[A.length - 1] = A[idx] := by congr 1; omega
    rw [this] at hlast_val
    omega
  have hidx_pos_gap : idx > 0 → A[idx - 1]'(by omega) - A[idx + 1]'(by omega) ≥ 3 := by
    intro hidx_pos
    exact not_flat_removable_interior_gap A idx hflat' hidx (by omega) hidx_not_last hmod hpos (hnoFR idx hidx)
  have hge3 : ∀ j : ℕ, (hj : j < A.length) → j < idx → A[j]'hj ≥ 3 := by
    intro j hj hjidx
    have hcount : numMultsGe A (j + 1) ≥ 1 := by
      unfold numMultsGe
      have hidx_in_drop : idx - (j + 1) < (A.drop (j + 1)).length := by
        simp [List.length_drop]; omega
      have hget : (A.drop (j + 1))[idx - (j + 1)] = A[idx] := by
        rw [List.getElem_drop]; congr 1; omega
      suffices hmem : A[idx] ∈ (A.drop (j + 1)).filter (fun x => x % 3 == 0 && decide (0 < x)) by
        exact Nat.one_le_iff_ne_zero.mpr (by
          intro h0
          rw [List.length_eq_zero_iff] at h0
          rw [h0] at hmem
          exact List.not_mem_nil hmem)
      rw [List.mem_filter]
      exact ⟨hget ▸ List.getElem_mem hidx_in_drop, by simp [hmod, hpos]⟩
    have := hall j hj
    omega
  have hpw_ge : ∀ (a b : ℕ) (ha : a < A.length) (hb : b < A.length),
      a < b → A[a] ≥ A[b] := by
    intro a b ha hb hab
    exact List.pairwise_iff_getElem.mp hpw a b ha hb hab
  have hA''_val_lt : ∀ j : ℕ, (hj : j < A''.length) → j < idx →
      A''[j]'hj = A[j]'(by omega) - 3 := by
    intro j hj hjidx
    show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j] - 3
    rw [List.getElem_map, List.getElem_zipIdx]
    simp [hjidx]
    congr 1
    show (A.eraseIdx idx)[j] = A[j]
    rw [List.getElem_eraseIdx]
    simp [show ¬(j ≥ idx) from by omega]
  have hA''_val_ge : ∀ j : ℕ, (hj : j < A''.length) → j ≥ idx →
      A''[j]'hj = A[j + 1]'(by omega) := by
    intro j hj hjidx
    show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j + 1]
    rw [List.getElem_map, List.getElem_zipIdx]
    simp [show ¬(j < idx) from by omega]
    show (A.eraseIdx idx)[j]'(by simp [List.length_eraseIdx, hidx]; omega) = A[j + 1]
    rw [List.getElem_eraseIdx]
    simp [show ¬(j < idx) from by omega]
  -- Part 1: Weakly decreasing
  have hpw'' : A''.Pairwise (· ≥ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    by_cases hi_lt_idx : i < idx
    · by_cases hj_lt_idx : j < idx
      · rw [hA''_val_lt i hi hi_lt_idx, hA''_val_lt j hj hj_lt_idx]
        have hge := hpw_ge i j (by omega) (by omega) hij
        have hge3_j := hge3 j (by omega) hj_lt_idx
        omega
      · push_neg at hj_lt_idx
        rw [hA''_val_lt i hi hi_lt_idx, hA''_val_ge j hj hj_lt_idx]
        have hidx_pos : idx > 0 := by omega
        have hgap := hidx_pos_gap hidx_pos
        have hA_i_ge_idxm1 : A[i]'(by omega) ≥ A[idx - 1]'(by omega) := by
          by_cases hi_eq : i = idx - 1
          · subst hi_eq; exact Nat.le_refl _
          · exact hpw_ge i (idx - 1) (by omega) (by omega) (by omega)
        have hA_idxp1_ge_jp1 : A[idx + 1]'(by omega) ≥ A[j + 1]'(by omega) := by
          by_cases hj_eq : j = idx
          · subst hj_eq; exact Nat.le_refl _
          · exact hpw_ge (idx + 1) (j + 1) (by omega) (by omega) (by omega)
        omega
    · push_neg at hi_lt_idx
      have hj_ge_idx : j ≥ idx := by omega
      rw [hA''_val_ge i hi hi_lt_idx, hA''_val_ge j hj hj_ge_idx]
      exact hpw_ge (i + 1) (j + 1) (by omega) (by omega) (by omega)
  -- Part 2: All positive
  have hpos'' : ∀ x ∈ A'', 0 < x := by
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    by_cases hjidx : j < idx
    · rw [hA''_val_lt j hj hjidx] at hxj
      rw [← hxj]
      have hge := hge3 j (by omega) hjidx
      have hpos_j : 0 < A[j]'(by omega) := hpos_all _ (List.getElem_mem (by omega))
      have hnmb := hno_mult_below j (by omega) hjidx
      have hmod_ne : ¬(A[j]'(by omega) % 3 = 0) := by
        intro hmod3; exact hnmb ⟨hmod3, hpos_j⟩
      omega
    · push_neg at hjidx
      rw [hA''_val_ge j hj hjidx] at hxj
      rw [← hxj]
      exact hpos_all _ (List.getElem_mem (by omega))
  -- Part 3: Consecutive gaps < 3
  have hgaps'' : ∀ (i : ℕ) (hi : i + 1 < A''.length),
      A''[i]'(by omega) - A''[i + 1]'hi < 3 := by
    intro i hi
    have hi' : i < A''.length := by omega
    by_cases hi_lt_idx_m1 : i + 1 < idx
    · rw [hA''_val_lt i hi' (by omega), hA''_val_lt (i + 1) hi (by omega)]
      have hgap_orig := hgaps i (by omega : i + 1 < A.length)
      have hge3_ip1 := hge3 (i + 1) (by omega) (by omega)
      omega
    · by_cases hi_eq : i + 1 = idx
      · have hidx_pos : idx > 0 := by omega
        rw [hA''_val_lt i hi' (by omega : i < idx)]
        rw [hA''_val_ge (i + 1) hi (by omega : i + 1 ≥ idx)]
        have hgap1 := hgaps i (by omega : i + 1 < A.length)
        have hgap2 := hgaps (i + 1) (by omega : i + 1 + 1 < A.length)
        have hge_i_ip1 : A[i]'(by omega) ≥ A[i + 1]'(by omega) :=
          hpw_ge i (i + 1) (by omega) (by omega) (by omega)
        have hge_ip1_ip2 : A[i + 1]'(by omega) ≥ A[i + 1 + 1]'(by omega) :=
          hpw_ge (i + 1) (i + 1 + 1) (by omega) (by omega) (by omega)
        omega
      · push_neg at hi_lt_idx_m1
        have hi_ge : i ≥ idx := by omega
        have hip1_ge : i + 1 ≥ idx := by omega
        rw [hA''_val_ge i hi' hi_ge, hA''_val_ge (i + 1) hi hip1_ge]
        exact hgaps (i + 1) (by omega)
  -- Part 4: Last element < 3
  have hlast'' : ∀ h : A'' ≠ [], A''.getLast h < 3 := by
    intro hne
    have hne_A : A ≠ [] := by intro h; simp [h] at hidx
    have hlast_A := hlast hne_A
    rw [List.getLast_eq_getElem] at hlast_A ⊢
    have hlast_pos : A''.length - 1 ≥ idx := by rw [hA''_len]; omega
    rw [hA''_val_ge (A''.length - 1) (by omega) hlast_pos]
    convert hlast_A using 2
    omega
  exact ⟨⟨hpw'', hpos''⟩, hgaps'', hlast''⟩

private lemma fire_step_no_mult_below (A : List ℕ) (idx : ℕ)
    (hflat : IsThreeFlat A)
    (hidx : idx < A.length)
    (hmod : A[idx] % 3 = 0) (hpos : 0 < A[idx])
    (hnoFR : ∀ j : ℕ, (hj : j < A.length) → isFlatRemovableBool A j = false)
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j])) :
    let A' := A.eraseIdx idx
    let A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
    ∀ j : ℕ, (hj : j < A''.length) → j < idx → ¬(A''[j] % 3 = 0 ∧ 0 < A''[j]) := by
  intro A' A'' j hj hjidx
  have hA'_len : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx, hidx]
  have hA''_len : A''.length = A.length - 1 := by
    simp [A'', List.length_map, List.length_zipIdx, hA'_len]
  have hj_lt_A : j < A.length := by omega
  have hj_lt_A' : j < A'.length := by omega
  intro ⟨hmod_j, hpos_j⟩
  have hA''_val : A''[j] = A[j]'hj_lt_A - 3 := by
    show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j] - 3
    rw [List.getElem_map, List.getElem_zipIdx]
    simp [show j < idx from hjidx]
    congr 1
    show (A.eraseIdx idx)[j] = A[j]
    rw [List.getElem_eraseIdx]
    simp [show ¬(j ≥ idx) from by omega]
  rw [hA''_val] at hmod_j hpos_j
  have hAmod : A[j]'hj_lt_A % 3 = 0 := by omega
  have hApos : 0 < A[j]'hj_lt_A := by omega
  exact hno_mult_below j hj_lt_A hjidx ⟨hAmod, hApos⟩

set_option maxHeartbeats 800000 in
private lemma fire_step_noFR (A : List ℕ) (idx : ℕ)
    (hflat : IsThreeFlat A)
    (hidx : idx < A.length)
    (hmod : A[idx] % 3 = 0) (hpos : 0 < A[idx])
    (hnoFR : ∀ j : ℕ, (hj : j < A.length) → isFlatRemovableBool A j = false)
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j])) :
    let A' := A.eraseIdx idx
    let A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
    ∀ j : ℕ, (hj : j < A''.length) → isFlatRemovableBool A'' j = false := by
  intro A' A''
  have hflat' := hflat
  obtain ⟨⟨hpw, hpos_all⟩, hgaps, hlast⟩ := hflat
  have hA'_len : A'.length = A.length - 1 := by
    simp [A', List.length_eraseIdx, hidx]
  have hA''_len : A''.length = A.length - 1 := by
    simp [A'', List.length_map, List.length_zipIdx, hA'_len]
  have hflat'' : IsThreeFlat A'' :=
    fire_step_isThreeFlat A idx hflat' hidx hmod hpos hnoFR hall hno_mult_below
  have hno_mult_below'' : ∀ j : ℕ, (hj : j < A''.length) → j < idx → ¬(A''[j] % 3 = 0 ∧ 0 < A''[j]) :=
    fire_step_no_mult_below A idx hflat' hidx hmod hpos hnoFR hno_mult_below
  have hidx_not_last : idx < A.length - 1 := by
    by_contra h
    push_neg at h
    have hidx_eq : idx = A.length - 1 := by omega
    have hne : A ≠ [] := by intro h; simp [h] at hidx
    have hlast_val := hlast hne
    rw [List.getLast_eq_getElem] at hlast_val
    have : A[A.length - 1] = A[idx] := by congr 1; omega
    rw [this] at hlast_val
    omega
  have hA''_val_lt : ∀ j : ℕ, (hj : j < A''.length) → j < idx →
      A''[j]'hj = A[j]'(by omega) - 3 := by
    intro j hj hjidx
    show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j] - 3
    rw [List.getElem_map, List.getElem_zipIdx]
    simp [hjidx]
    congr 1
    show (A.eraseIdx idx)[j] = A[j]
    rw [List.getElem_eraseIdx]
    simp [show ¬(j ≥ idx) from by omega]
  have hA''_val_ge : ∀ j : ℕ, (hj : j < A''.length) → j ≥ idx →
      A''[j]'hj = A[j + 1]'(by omega) := by
    intro j hj hjidx
    show (A'.zipIdx |>.map (fun (x, k) => if k < idx then x - 3 else x))[j] = A[j + 1]
    rw [List.getElem_map, List.getElem_zipIdx]
    simp [show ¬(j < idx) from by omega]
    show (A.eraseIdx idx)[j]'(by simp [List.length_eraseIdx, hidx]; omega) = A[j + 1]
    rw [List.getElem_eraseIdx]
    simp [show ¬(j < idx) from by omega]
  have hpw_ge : ∀ (a b : ℕ) (ha : a < A.length) (hb : b < A.length),
      a < b → A[a] ≥ A[b] := by
    intro a b ha hb hab
    exact List.pairwise_iff_getElem.mp hpw a b ha hb hab
  -- Main proof: for each j, isFlatRemovableBool A'' j = false
  intro j hj
  by_cases hjidx : j < idx
  · -- Case j < idx: A''[j] % 3 ≠ 0, so first condition fails
    have hA''_mod : ¬(A''[j]'hj % 3 = 0 ∧ 0 < A''[j]'hj) :=
      hno_mult_below'' j hj hjidx
    unfold isFlatRemovableBool
    have h1 : (decide (j < A''.length) : Bool) = true := by simp [hj]
    simp only [h1, Bool.true_and]
    have hmod_ne : ¬(A''[j]'hj % 3 = 0) ∨ ¬(0 < A''[j]'hj) := by
      exact not_and_or.mp hA''_mod
    cases hmod_ne with
    | inl hmod_ne =>
      have : (A''[j]! % 3 == 0) = false := by
        rw [getElem!_pos A'' j hj]
        simp [hmod_ne]
      simp only [this, Bool.false_and]
    | inr hpos_ne =>
      -- A''[j] = 0, so A''[j]! % 3 = 0 but we need to show the erased list isn't 3-flat
      -- Actually if A''[j] = 0, it can't be in A'' because all elements are positive in a 3-flat list
      exfalso
      have hpos_j := hflat''.1.2 (A''[j]'hj) (List.getElem_mem hj)
      omega
  · -- Case j ≥ idx: A''[j] = A[j+1], transfer from hnoFR (j+1)
    push_neg at hjidx
    have hj1_lt : j + 1 < A.length := by omega
    have hnoFR_j1 := hnoFR (j + 1) hj1_lt
    -- Unfold isFlatRemovableBool in both
    unfold isFlatRemovableBool at hnoFR_j1 ⊢
    have h1_orig : (decide (j + 1 < A.length) : Bool) = true := by simp [hj1_lt]
    have h1_new : (decide (j < A''.length) : Bool) = true := by simp [hj]
    simp only [h1_orig, Bool.true_and] at hnoFR_j1
    simp only [h1_new, Bool.true_and]
    -- Now hnoFR_j1 : (A[j+1]! % 3 == 0) && isThreeFlatBool (A.eraseIdx (j+1)) = false
    -- Goal: (A''[j]! % 3 == 0) && isThreeFlatBool (A''.eraseIdx j) = false
    have hval : A''[j]'hj = A[j + 1]'hj1_lt := hA''_val_ge j hj hjidx
    rw [getElem!_pos A'' j hj, getElem!_pos A (j + 1) hj1_lt] at *
    rw [hval]
    -- Now goal: (A[j+1] % 3 == 0) && isThreeFlatBool (A''.eraseIdx j) = false
    by_cases hmod_j1 : (A[j + 1]'hj1_lt % 3 == 0) = true
    · -- A[j+1] % 3 = 0, so need to show isThreeFlatBool (A''.eraseIdx j) = false
      simp only [hmod_j1, Bool.true_and]
      -- From hnoFR_j1 with hmod_j1:
      simp only [hmod_j1, Bool.true_and] at hnoFR_j1
      -- hnoFR_j1 : isThreeFlatBool (A.eraseIdx (j+1)) = false
      -- Need: isThreeFlatBool (A''.eraseIdx j) = false
      by_contra h_flat
      push_neg at h_flat
      -- h_flat : isThreeFlatBool (A''.eraseIdx j) = true
      have h_flat_t : isThreeFlatBool (A''.eraseIdx j) = true := by
        cases h : isThreeFlatBool (A''.eraseIdx j) <;> simp_all
      -- Derive contradiction: get a gap ≥ 3 in A''.eraseIdx j
      -- From hnoFR_j1, isThreeFlatBool (A.eraseIdx (j+1)) = false
      -- The key fact: A[j] - A[j+2] ≥ 3 (from not_flat_removable_interior_gap)
      -- We need j+1 to be an interior position in A
      have hj1_pos : 0 < j + 1 := by omega
      have hj1_not_last : j + 1 < A.length - 1 := by
        -- If j + 1 = A.length - 1 (last), then A[j+1] < 3 by hlast
        -- But A[j+1] % 3 = 0 and A[j+1] > 0 (from hpos_all) implies A[j+1] ≥ 3
        by_contra habs
        push_neg at habs
        have hj1_last : j + 1 = A.length - 1 := by omega
        have hne : A ≠ [] := by intro h; simp [h] at hidx
        have hlast_val := hlast hne
        rw [List.getLast_eq_getElem] at hlast_val
        have : A[A.length - 1] = A[j + 1] := by congr 1; omega
        rw [this] at hlast_val
        have hmod_val : A[j + 1]'hj1_lt % 3 = 0 := by
          have := beq_iff_eq.mp hmod_j1; exact_mod_cast this
        have hpos_val : 0 < A[j + 1]'hj1_lt := hpos_all _ (List.getElem_mem hj1_lt)
        omega
      have hmod_val : A[j + 1]'hj1_lt % 3 = 0 := by
        have := beq_iff_eq.mp hmod_j1; exact_mod_cast this
      have hpos_val : 0 < A[j + 1]'hj1_lt := hpos_all _ (List.getElem_mem hj1_lt)
      have hgap_big := not_flat_removable_interior_gap A (j + 1) hflat' hj1_lt hj1_pos hj1_not_last
        hmod_val hpos_val (hnoFR (j + 1) hj1_lt)
      -- hgap_big : A[j] - A[j+2] ≥ 3
      -- Now we need to find this gap in A''.eraseIdx j and get contradiction with h_flat_t
      -- A''.eraseIdx j has length A.length - 2
      have hA''_erase_len : (A''.eraseIdx j).length = A.length - 2 := by
        rw [List.length_eraseIdx, if_pos hj, hA''_len]; omega
      by_cases hjgt : j > idx
      · -- j > idx case
        -- (A''.eraseIdx j)[j-1] = A''[j-1] = A[j] (since j-1 ≥ idx)
        -- (A''.eraseIdx j)[j] = A''[j+1] = A[j+2] (since j+1 ≥ idx)
        -- Gap = A[j] - A[j+2] ≥ 3, contradicting 3-flat of A''.eraseIdx j
        have hj_pos : j ≥ 1 := by omega
        have hjm1_lt_erase : j - 1 < (A''.eraseIdx j).length := by
          rw [hA''_erase_len]; omega
        have hj_lt_erase : j < (A''.eraseIdx j).length := by
          rw [hA''_erase_len]; omega
        -- isThreeFlatBool means gaps < 3
        have hgaps_e : ∀ i < (A''.eraseIdx j).length - 1,
            (A''.eraseIdx j)[i]! - (A''.eraseIdx j)[i + 1]! < 3 := by
          have h_flat_bool := h_flat_t
          unfold isThreeFlatBool isPositivePartitionBool at h_flat_bool
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h_flat_bool
          exact h_flat_bool.1.2
        have hj_eq : j - 1 + 1 = j := by omega
        have hjm1_range : j - 1 < (A''.eraseIdx j).length - 1 := by
          rw [hA''_erase_len]; omega
        have hgap_e := hgaps_e (j - 1) hjm1_range
        -- hgap_e : (A''.eraseIdx j)[j-1]! - (A''.eraseIdx j)[j-1+1]! < 3
        rw [hj_eq] at hgap_e
        -- Now: (A''.eraseIdx j)[j-1]! - (A''.eraseIdx j)[j]! < 3
        rw [getElem!_pos _ (j - 1) hjm1_lt_erase, getElem!_pos _ j hj_lt_erase] at hgap_e
        -- Compute values
        have hv1 : (A''.eraseIdx j)[j - 1]'hjm1_lt_erase = A''[j - 1]'(by rw [hA''_len]; omega) := by
          rw [List.getElem_eraseIdx]
          simp [show j - 1 < j from by omega]
        have hv2 : (A''.eraseIdx j)[j]'hj_lt_erase = A''[j + 1]'(by rw [hA''_len]; omega) := by
          rw [List.getElem_eraseIdx]
          simp [show ¬(j < j) from by omega]
        have hv1' : A''[j - 1]'(by rw [hA''_len]; omega) = A[j]'(by omega) := by
          have h := hA''_val_ge (j - 1) (by rw [hA''_len]; omega) (by omega)
          convert h using 2; omega
        have hv2' : A''[j + 1]'(by rw [hA''_len]; omega) = A[j + 2]'(by omega) := by
          have := hA''_val_ge (j + 1) (by rw [hA''_len]; omega) (by omega : j + 1 ≥ idx)
          convert this using 2
        rw [hv1, hv2, hv1', hv2'] at hgap_e
        -- hgap_big : A[j + 1 - 1] - A[j + 1 + 1] ≥ 3, normalize indices
        have hgap_big' : A[j]'(by omega) - A[j + 2]'(by omega) ≥ 3 := by
          convert hgap_big using 2 <;> omega
        omega
      · -- j = idx case
        have hjeq : j = idx := by omega
        -- (A''.eraseIdx j)[j-1] if j > 0: A''[j-1]
        --   if j-1 < idx: A[j-1] - 3 = A[idx-1] - 3
        --   but j = idx, so j-1 = idx-1 < idx: A[idx-1] - 3
        -- (A''.eraseIdx j)[j] = A''[j+1] = A[j+2] = A[idx+2] (since j+1 > idx)
        -- But wait, need j > 0 for the splice gap at j-1
        by_cases hidx_zero : idx = 0
        · -- idx = 0, j = 0
          exfalso
          have hlen_gt1 : A.length > 1 := by omega
          have hnoFR_0 := hnoFR 0 (by omega : 0 < A.length)
          unfold isFlatRemovableBool at hnoFR_0
          simp only [show (decide (0 < A.length) : Bool) = true from by simp [show 0 < A.length from by omega],
            Bool.true_and] at hnoFR_0
          have hmod0 : (A[0]! % 3 == 0) = true := by
            rw [getElem!_pos A 0 (by omega)]; simp [show A[0]'(by omega) = A[idx] from by congr 1; omega, hmod]
          simp only [hmod0, Bool.true_and] at hnoFR_0
          -- hnoFR_0 : isThreeFlatBool (A.eraseIdx 0) = false
          -- But A.eraseIdx 0 = A.tail is 3-flat
          have htail_flat : IsThreeFlat (A.eraseIdx 0) := by
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
            · exact hpw.sublist (List.eraseIdx_sublist A 0)
            · intro x hx; exact hpos_all x (List.mem_of_mem_eraseIdx hx)
            · intro i hi
              have hlen_e : (A.eraseIdx 0).length = A.length - 1 := by
                rw [List.length_eraseIdx, if_pos (by omega : 0 < A.length)]
              rw [hlen_e] at hi
              have hv1 : (A.eraseIdx 0)[i]'(by rw [hlen_e]; omega) = A[i + 1]'(by omega) := by
                rw [List.getElem_eraseIdx]; simp
              have hv2 : (A.eraseIdx 0)[i + 1]'(by rw [hlen_e]; omega) = A[i + 2]'(by omega) := by
                rw [List.getElem_eraseIdx]; simp
              rw [hv1, hv2]; exact hgaps (i + 1) (by omega)
            · intro hne
              have hne_A : A ≠ [] := by intro h; simp [h] at hidx
              rw [List.getLast_eq_getElem]
              have hlen_e : (A.eraseIdx 0).length = A.length - 1 := by
                rw [List.length_eraseIdx, if_pos (by omega : 0 < A.length)]
              have hv : (A.eraseIdx 0)[(A.eraseIdx 0).length - 1]'(by omega) = A[A.length - 1]'(by omega) := by
                rw [List.getElem_eraseIdx]
                have hcond : ¬((A.eraseIdx 0).length - 1 < 0) := by omega
                simp only [hcond, ↓reduceDIte]
                congr 1; omega
              rw [hv]
              have := hlast hne_A
              rw [List.getLast_eq_getElem] at this
              exact this
          -- Now htail_flat contradicts hnoFR_0
          have htail_bool : isThreeFlatBool (A.eraseIdx 0) = true := by
            unfold isThreeFlatBool isPositivePartitionBool
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
            obtain ⟨⟨hpw_t, hpos_t⟩, hgaps_t, hlast_t⟩ := htail_flat
            refine ⟨⟨⟨hpw_t, ?_⟩, ?_⟩, ?_⟩
            · intro x hx; exact hpos_t x hx
            · intro i hi
              have hi' : i + 1 < (A.eraseIdx 0).length := by omega
              rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']
              exact hgaps_t i hi'
            · cases hl : (A.eraseIdx 0).getLast? with
              | none => simp
              | some x =>
                simp
                have hne : A.eraseIdx 0 ≠ [] := by intro h; simp [h] at hl
                rw [List.getLast?_eq_some_getLast hne] at hl
                have := Option.some.inj hl
                rw [← this]
                exact hlast_t hne
          rw [htail_bool] at hnoFR_0
          exact absurd hnoFR_0 (by decide)
        · -- idx > 0, j = idx > 0
          exfalso
          have hidx_pos : 0 < idx := by omega
          have hmod_j1_val : A[j + 1]'hj1_lt % 3 = 0 := by
            have := beq_iff_eq.mp hmod_j1; exact_mod_cast this
          -- A[idx] = A[idx+1] because both are mult of 3 and gap < 3
          have hgap_idx : A[idx]'hidx - A[idx + 1]'(by omega) < 3 := by
            have := hgaps idx (by omega : idx + 1 < A.length)
            convert this using 2 <;> omega
          have hA_idx_eq : A[idx]'hidx = A[idx + 1]'(by omega) := by
            have h1 : A[idx]'hidx % 3 = 0 := hmod
            have h2 : A[idx + 1]'(by omega) % 3 = 0 := by
              subst hjeq; exact hmod_j1_val
            have hge : A[idx]'hidx ≥ A[idx + 1]'(by omega) := hpw_ge idx (idx + 1) hidx (by omega) (by omega)
            omega
          -- From not_flat_removable_interior_gap: A[idx-1] - A[idx+1] ≥ 3
          have hbig_gap := not_flat_removable_interior_gap A idx hflat' hidx hidx_pos hidx_not_last hmod hpos (hnoFR idx hidx)
          -- hbig_gap : A[idx-1] - A[idx+1] ≥ 3
          -- From hA_idx_eq: A[idx] = A[idx+1], so A[idx-1] - A[idx] ≥ 3
          have hgap_small := hgaps (idx - 1) (by omega : idx - 1 + 1 < A.length)
          -- hgap_small : A[idx-1] - A[idx] < 3
          have h_idx_m1 : idx - 1 + 1 = idx := by omega
          have hval1 : A[idx - 1]'(by omega) = A[idx - 1]'(by omega) := rfl
          have : A[idx - 1]'(by omega) - A[idx]'(by omega : idx < A.length) < 3 := by
            have := hgaps (idx - 1) (by omega : idx - 1 + 1 < A.length)
            convert this using 2
            congr 1; omega
          omega
    · -- A[j+1] % 3 ≠ 0
      have hmod_false : (A[j + 1]'hj1_lt % 3 == 0) = false := by
        cases h : (A[j + 1]'hj1_lt % 3 == 0) <;> simp_all
      simp only [hmod_false, Bool.false_and]

set_option maxHeartbeats 400000 in
private lemma scanFromLargest_isThreeFlat (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hflat : IsThreeFlat A)
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j]))
    (hnoFR : ∀ j : ℕ, (hj : j < A.length) → isFlatRemovableBool A j = false) :
    IsThreeFlat (scanFromLargest fuel A idx rec).1 := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromLargest]; exact hflat
  | succ fuel' ih =>
    simp only [scanFromLargest]
    split
    · -- idx >= A.length
      exact hflat
    · -- idx < A.length
      rename_i hidx_ge
      push_neg at hidx_ge
      split
      · -- Fire case: val % 3 == 0 && val > 0
        rename_i hfire
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfire
        rw [getElem!_pos A idx hidx_ge] at hfire
        obtain ⟨hmod, hpos⟩ := hfire
        set A' := A.eraseIdx idx
        set A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
        have hflat'' : IsThreeFlat A'' :=
          fire_step_isThreeFlat A idx hflat hidx_ge hmod hpos hnoFR hall hno_mult_below
        have hall'' : ∀ j : ℕ, (hj : j < A''.length) → A''[j] ≥ 3 * numMultsGe A'' (j + 1) :=
          scanFromLargest_fire_hall_maintenance A idx hidx_ge hmod hpos hall hno_mult_below
        have hno_mult'' : ∀ j : ℕ, (hj : j < A''.length) → j < idx → ¬(A''[j] % 3 = 0 ∧ 0 < A''[j]) :=
          fire_step_no_mult_below A idx hflat hidx_ge hmod hpos hnoFR hno_mult_below
        have hnoFR'' : ∀ j : ℕ, (hj : j < A''.length) → isFlatRemovableBool A'' j = false :=
          fire_step_noFR A idx hflat hidx_ge hmod hpos hnoFR hall hno_mult_below
        show IsThreeFlat (scanFromLargest fuel' A'' idx (rec ++ [A[idx]! / 3 + idx])).1
        rw [getElem!_pos A idx hidx_ge]
        exact ih A'' idx (rec ++ [A[idx] / 3 + idx]) hflat'' hall'' hno_mult'' hnoFR''
      · -- Skip case: not (val % 3 == 0 && val > 0)
        rename_i hfire
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and_or] at hfire
        rw [getElem!_pos A idx hidx_ge] at hfire
        have hno_mult_ext : ∀ j : ℕ, (hj : j < A.length) → j < idx + 1 → ¬(A[j] % 3 = 0 ∧ 0 < A[j]) := by
          intro j hj hjidx1
          by_cases hjidx : j < idx
          · exact hno_mult_below j hj hjidx
          · -- j = idx
            have hjeq : j = idx := by omega
            subst hjeq
            intro ⟨hmod_j, hpos_j⟩
            cases hfire with
            | inl h => exact absurd hmod_j h
            | inr h => omega
        exact ih A (idx + 1) rec hflat hall hno_mult_ext hnoFR

set_option maxHeartbeats 400000 in
/-- scanFromLargest removes all remaining multiples of 3, producing a 3-regular result. -/
private lemma scanFromLargest_isThreeRegular (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hflat : IsThreeFlat A)
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j]))
    (hnoFR : ∀ j : ℕ, (hj : j < A.length) → isFlatRemovableBool A j = false)
    (hfuel : fuel + idx ≥ A.length) :
    IsThreeRegular (scanFromLargest fuel A idx rec).1 := by
  induction fuel generalizing A idx rec with
  | zero =>
    simp [scanFromLargest]
    have hidx_ge : idx ≥ A.length := by omega
    constructor
    · exact hflat.1
    · intro x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      intro hdvd
      have hmod : A[j] % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      have hpos_j : 0 < A[j] := hflat.1.2 _ (List.getElem_mem hj)
      exact hno_mult_below j hj (by omega) ⟨hmod, hpos_j⟩
  | succ fuel' ih =>
    simp only [scanFromLargest]
    split
    · -- idx >= A.length
      rename_i hidx_ge
      show IsThreeRegular A
      constructor
      · exact hflat.1
      · intro x hx
        rw [List.mem_iff_getElem] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        intro hdvd
        have hmod : A[j] % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
        have hpos_j : 0 < A[j] := hflat.1.2 _ (List.getElem_mem hj)
        exact hno_mult_below j hj (by omega) ⟨hmod, hpos_j⟩
    · -- idx < A.length
      rename_i hidx_ge
      push_neg at hidx_ge
      split
      · -- Fire case: val % 3 == 0 && val > 0
        rename_i hfire
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfire
        rw [getElem!_pos A idx hidx_ge] at hfire
        obtain ⟨hmod, hpos⟩ := hfire
        set A' := A.eraseIdx idx
        set A'' := A'.zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
        have hflat'' : IsThreeFlat A'' :=
          fire_step_isThreeFlat A idx hflat hidx_ge hmod hpos hnoFR hall hno_mult_below
        have hall'' : ∀ j : ℕ, (hj : j < A''.length) → A''[j] ≥ 3 * numMultsGe A'' (j + 1) :=
          scanFromLargest_fire_hall_maintenance A idx hidx_ge hmod hpos hall hno_mult_below
        have hno_mult'' : ∀ j : ℕ, (hj : j < A''.length) → j < idx → ¬(A''[j] % 3 = 0 ∧ 0 < A''[j]) :=
          fire_step_no_mult_below A idx hflat hidx_ge hmod hpos hnoFR hno_mult_below
        have hnoFR'' : ∀ j : ℕ, (hj : j < A''.length) → isFlatRemovableBool A'' j = false :=
          fire_step_noFR A idx hflat hidx_ge hmod hpos hnoFR hall hno_mult_below
        have hlen_A'' : A''.length = A.length - 1 := by
          simp [A'', A', List.length_map, List.length_zipIdx, List.length_eraseIdx, hidx_ge]
        have hfuel'' : fuel' + idx ≥ A''.length := by omega
        show IsThreeRegular (scanFromLargest fuel' A'' idx (rec ++ [A[idx]! / 3 + idx])).1
        rw [getElem!_pos A idx hidx_ge]
        exact ih A'' idx (rec ++ [A[idx] / 3 + idx]) hflat'' hall'' hno_mult'' hnoFR'' hfuel''
      · -- Skip case: not (val % 3 == 0 && val > 0)
        rename_i hfire
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and_or] at hfire
        rw [getElem!_pos A idx hidx_ge] at hfire
        have hno_mult_ext : ∀ j : ℕ, (hj : j < A.length) → j < idx + 1 → ¬(A[j] % 3 = 0 ∧ 0 < A[j]) := by
          intro j hj hjidx1
          by_cases hjidx : j < idx
          · exact hno_mult_below j hj hjidx
          · -- j = idx
            have hjeq : j = idx := by omega
            subst hjeq
            intro ⟨hmod_j, hpos_j⟩
            cases hfire with
            | inl h => exact absurd hmod_j h
            | inr h => omega
        have hfuel_ext : fuel' + (idx + 1) ≥ A.length := by omega
        exact ih A (idx + 1) rec hflat hall hno_mult_ext hnoFR hfuel_ext

set_option maxHeartbeats 800000 in
/-- scanFromLargest preserves the nonzero residue sequence: in each step it removes
    a multiple of 3 and subtracts 3 from elements above (preserving their residues mod 3
    and their non-divisibility by 3). -/
private lemma scanFromLargest_preserves_nonzeroResSeq (fuel : ℕ) (A : List ℕ) (idx : ℕ)
    (rec : List ℕ)
    (hall : ∀ j : ℕ, (hj : j < A.length) → A[j] ≥ 3 * numMultsGe A (j + 1))
    (hno_mult_below : ∀ j : ℕ, (hj : j < A.length) → j < idx → ¬(A[j] % 3 = 0 ∧ 0 < A[j])) :
    nonzeroResSeq (scanFromLargest fuel A idx rec).1 = nonzeroResSeq A := by
  induction fuel generalizing A idx rec with
  | zero => simp [scanFromLargest]
  | succ fuel' ih =>
    simp only [scanFromLargest]
    split
    · rfl
    · rename_i hidx_ge; push_neg at hidx_ge
      split
      · -- Fire case: val % 3 == 0 && val > 0
        rename_i hfire
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfire
        rw [getElem!_pos A idx hidx_ge] at hfire
        have hge3 : ∀ j : ℕ, (hj : j < A.length) → j < idx → A[j] ≥ 3 := by
          intro j hj hjidx
          have hball := hall j hj
          suffices numMultsGe A (j + 1) ≥ 1 by omega
          unfold numMultsGe
          have hlen : idx - (j + 1) < (A.drop (j + 1)).length := by
            simp [List.length_drop]; omega
          have heq : (A.drop (j + 1))[idx - (j + 1)]'hlen = A[idx] := by
            rw [List.getElem_drop]; congr 1; omega
          have h_in : A[idx] ∈ A.drop (j + 1) := by rw [← heq]; exact List.getElem_mem hlen
          have h_pred : (fun x => x % 3 == 0 && decide (0 < x)) A[idx] = true := by
            simp [hfire.1, hfire.2]
          exact List.length_pos_of_mem (List.mem_filter.mpr ⟨h_in, h_pred⟩)
        set A'' := (A.eraseIdx idx).zipIdx |>.map (fun (x, j) => if j < idx then x - 3 else x)
        have htransform : nonzeroResSeq A'' = nonzeroResSeq A :=
          nonzeroResSeq_zipIdx_map_eraseIdx A idx hidx_ge hfire.1 hno_mult_below hge3
        have hno_mult_A'' : ∀ j : ℕ, (hj : j < A''.length) → j < idx → ¬(A''[j] % 3 = 0 ∧ 0 < A''[j]) := by
          intro j hj hjidx
          have hA''_len : A''.length = A.length - 1 := by
            simp [A'', List.length_map, List.length_zipIdx, List.length_eraseIdx, hidx_ge]
          have hj_lt_A : j < A.length := by omega
          have hmult := hno_mult_below j hj_lt_A hjidx
          have hA''_val : A''[j] = A[j] - 3 := by
            simp only [A'', List.getElem_map, List.getElem_zipIdx, show j < idx from hjidx, ite_true]
            congr 1
            rw [List.getElem_eraseIdx]
            simp [show j < idx from hjidx]
          rw [hA''_val]
          intro ⟨hmod3, hpos⟩
          have hmod_A : A[j] % 3 = 0 := by omega
          exact hmult ⟨hmod_A, by omega⟩
        have hall_A'' : ∀ j : ℕ, (hj : j < A''.length) → A''[j] ≥ 3 * numMultsGe A'' (j + 1) :=
          scanFromLargest_fire_hall_maintenance A idx hidx_ge hfire.1 hfire.2 hall hno_mult_below
        rw [← htransform]
        exact ih A'' idx _ hall_A'' hno_mult_A''
      · -- Skip case: val % 3 ≠ 0 or val ≤ 0
        rename_i hskip
        apply ih
        · exact hall
        · intro j hj hjidx1
          by_cases hjidx : j < idx
          · exact hno_mult_below j hj hjidx
          · have hj_eq : j = idx := by omega
            subst hj_eq
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hskip
            rw [getElem!_pos A j hidx_ge] at hskip
            exact hskip

/-- After both scans, the final residual A₃ equals residueCore(nonzeroResSeq l).
    This is the algorithm correctness fact: both scans strip all multiples of 3
    while preserving residues. -/
private lemma scans_residual_eq_core' (l : List ℕ) (hflat : IsThreeFlat l) :
    let (A₂, rec₂) := scanFromSmallest (l.length + 1) l 0 []
    let (A₃, _) := scanFromLargest (A₂.length + 1) A₂ 0 rec₂
    A₃ = residueCore (nonzeroResSeq l) := by
  set p₂ := scanFromSmallest (l.length + 1) l 0 [] with hp₂_def
  set A₂ := p₂.1
  set rec₂ := p₂.2
  set p₃ := scanFromLargest (A₂.length + 1) A₂ 0 rec₂ with hp₃_def
  set A₃ := p₃.1
  show A₃ = residueCore (nonzeroResSeq l)
  -- Step 1: A₂ is 3-flat
  have hflat₂ : IsThreeFlat A₂ := scanFromSmallest_isThreeFlat (l.length + 1) l 0 [] hflat
  -- Step 2: A₂ satisfies the hall bound
  have hall₂ : ∀ j : ℕ, (hj : j < A₂.length) → A₂[j] ≥ 3 * numMultsGe A₂ (j + 1) :=
    post_s2_numMultsGe_bound l hflat
  -- Step 3: no mults of 3 below index 0
  have hno_mult₂ : ∀ j : ℕ, (hj : j < A₂.length) → j < 0 → ¬(A₂[j] % 3 = 0 ∧ 0 < A₂[j]) := by
    intro j _ hj; omega
  -- Step 3b: no flat-removable elements in A₂
  have hnoFR₂ : ∀ j : ℕ, (hj : j < A₂.length) → isFlatRemovableBool A₂ j = false :=
    scanFromSmallest_no_flat_removable (l.length + 1) l 0 [] hflat (by omega)
      (fun _ hi hge => absurd hi (by omega))
  -- Step 4: A₃ is 3-flat
  have hflat₃ : IsThreeFlat A₃ :=
    scanFromLargest_isThreeFlat (A₂.length + 1) A₂ 0 rec₂ hflat₂ hall₂ hno_mult₂ hnoFR₂
  -- Step 5: A₃ is 3-regular
  have hreg₃ : IsThreeRegular A₃ :=
    scanFromLargest_isThreeRegular (A₂.length + 1) A₂ 0 rec₂ hflat₂ hall₂ hno_mult₂ hnoFR₂
      (by omega)
  -- Step 6: nonzeroResSeq is preserved through both scans
  have hres_s2 : nonzeroResSeq A₂ = nonzeroResSeq l :=
    scanFromSmallest_preserves_nonzeroResSeq (l.length + 1) l 0 [] hflat
  have hres_s3 : nonzeroResSeq A₃ = nonzeroResSeq A₂ :=
    scanFromLargest_preserves_nonzeroResSeq (A₂.length + 1) A₂ 0 rec₂ hall₂ hno_mult₂
  have hres : nonzeroResSeq A₃ = nonzeroResSeq l := by rw [hres_s3, hres_s2]
  -- Step 7: Apply uniqueness of residueCore
  exact residueCore_unique (nonzeroResSeq l) (nonzeroResSeq_in_one_two l) A₃ hflat₃ hreg₃ hres

theorem forward_record_weight (l : List ℕ) (hflat : IsThreeFlat l) :
    let (A₂, rec₂) := scanFromSmallest (l.length + 1) l 0 []
    let (_, rec₃) := scanFromLargest (A₂.length + 1) A₂ 0 rec₂
    partWeight l =
      partWeight (residueCore (nonzeroResSeq l)) + 3 * rec₃.sum := by
  -- Use the two key invariants:
  -- 1) Weight is preserved through both scans: partWeight A₃ + 3 * rec₃.sum = partWeight l
  -- 2) The final residual A₃ = residueCore(nonzeroResSeq l)
  have hs2 := scanFromSmallest_weight_inv' (l.length + 1) l 0 []
  set p₂ := scanFromSmallest (l.length + 1) l 0 [] with hp₂
  have hs3 := scanFromLargest_weight_inv' (p₂.1.length + 1) p₂.1 0 p₂.2
    (post_s2_numMultsGe_bound l hflat)
    (fun j _ hjlt => absurd hjlt (Nat.not_lt_zero j))
  have hres := scans_residual_eq_core' l hflat
  -- Combine: partWeight l = partWeight A₂ + 3 * rec₂.sum (from hs2, noting rec starts empty)
  --        = partWeight A₃ + 3 * rec₃.sum (from hs3)
  --        = partWeight (residueCore ...) + 3 * rec₃.sum (from hres)
  simp only [List.sum_nil, Nat.mul_zero, Nat.add_zero] at hs2
  simp only at hs3 hres ⊢
  rw [← hres]; linarith

/-- After both scans, the record list has length at most the number of nonzero residue
parts of `l`, i.e. the length of `residueCore (nonzeroResSeq l)`. -/
theorem forward_record_length_le (l : List ℕ) (hflat : IsThreeFlat l) :
    let (A₂, rec₂) := scanFromSmallest (l.length + 1) l 0 []
    let (_, rec₃) := scanFromLargest (A₂.length + 1) A₂ 0 rec₂
    let core := residueCore (nonzeroResSeq l)
    (conjugate (rec₃.mergeSort (· ≥ ·))).length ≤ core.length := by
  show (conjugate ((scanFromLargest
    ((scanFromSmallest (l.length + 1) l 0 []).1.length + 1)
    (scanFromSmallest (l.length + 1) l 0 []).1 0
    (scanFromSmallest (l.length + 1) l 0 []).2).2.mergeSort (· ≥ ·))).length ≤
    (residueCore (nonzeroResSeq l)).length
  set rec₃ := (scanFromLargest
    ((scanFromSmallest (l.length + 1) l 0 []).1.length + 1)
    (scanFromSmallest (l.length + 1) l 0 []).1 0
    (scanFromSmallest (l.length + 1) l 0 []).2).2
  -- record_bound gives ∀ x ∈ rec₃, x ≤ k
  have hrb : ∀ x ∈ rec₃, x ≤ (l.filter (fun x => ¬(x % 3 == 0))).length :=
    record_bound l hflat
  -- core.length = filter.length
  have hv_12 : ∀ x ∈ nonzeroResSeq l, x = 1 ∨ x = 2 := nonzeroResSeq_in_one_two l
  have hcore_len : (residueCore (nonzeroResSeq l)).length =
      (l.filter (fun x => ¬(x % 3 == 0))).length := by
    have h1 := residueCore_length (nonzeroResSeq l) hv_12
    simp only [nonzeroResSeq, List.length_map] at h1
    exact h1
  -- conjugate length bounded by max of input
  suffices h : (conjugate (rec₃.mergeSort (· ≥ ·))).length ≤
      (l.filter (fun x => ¬(x % 3 == 0))).length by omega
  cases hrec₃_sorted : rec₃.mergeSort (· ≥ ·) with
  | nil => simp [conjugate]
  | cons a t =>
    simp only [conjugate, List.length_map, List.length_range]
    have ha_mem : a ∈ rec₃ := by
      have : a ∈ rec₃.mergeSort (· ≥ ·) := by rw [hrec₃_sorted]; exact List.mem_cons_self
      exact List.mem_mergeSort.mp this
    exact hrb a ha_mem

/-- `zipAddPad core (3·ν')` is positive and weakly decreasing whenever `core` is 3-flat
and `ν'` is a partition of length ≤ `core.length` (so the pad ν' lines up with core
position-by-position).  This is the structural "well-formed sum" lemma. -/
theorem zipAddPad_isPositivePartition_of_core_3flat
    (core : List ℕ) (ν' : List ℕ)
    (hcore_flat : IsThreeFlat core) (hν'_part : IsPartition ν')
    (hlen : ν'.length ≤ core.length) :
    IsPositivePartition (zipAddPad core (ν'.map (· * 3))) := by
  unfold IsPositivePartition zipAddPad
  have hlen_map : (ν'.map (· * 3)).length = ν'.length := by simp
  have hmax : max core.length (ν'.map (· * 3)).length = core.length := by
    simp [hlen_map]; omega
  constructor
  · -- Pairwise (· ≥ ·)
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map, List.length_range] at hi hj ⊢
    simp only [List.getElem_map, List.getElem_range]
    have hi_lt : i < core.length := by omega
    have hj_lt : j < core.length := by omega
    rw [List.getElem?_eq_getElem (h := hi_lt), Option.getD_some]
    rw [List.getElem?_eq_getElem (h := hj_lt), Option.getD_some]
    have hcore_sorted : core.Pairwise (· ≥ ·) := hcore_flat.1.1
    have hcore_ge : core[i] ≥ core[j] :=
      List.pairwise_iff_getElem.mp hcore_sorted i j hi_lt hj_lt hij
    by_cases hi_ν : i < ν'.length
    · by_cases hj_ν : j < ν'.length
      · have hν'_ge : ν'[i] ≥ ν'[j] :=
          List.pairwise_iff_getElem.mp hν'_part i j hi_ν hj_ν hij
        have hi_map : i < (ν'.map (· * 3)).length := by simp; exact hi_ν
        have hj_map : j < (ν'.map (· * 3)).length := by simp; exact hj_ν
        rw [List.getElem?_eq_getElem (h := hi_map), Option.getD_some,
            List.getElem?_eq_getElem (h := hj_map), Option.getD_some]
        simp only [List.getElem_map]
        omega
      · have hi_map : i < (ν'.map (· * 3)).length := by simp; exact hi_ν
        rw [List.getElem?_eq_getElem (h := hi_map), Option.getD_some]
        have hj_none : (ν'.map (· * 3))[j]? = none := by
          apply List.getElem?_eq_none
          simp; omega
        rw [hj_none, Option.getD_none]
        simp only [List.getElem_map]
        omega
    · have hj_ν : ¬(j < ν'.length) := by omega
      have hi_none : (ν'.map (· * 3))[i]? = none := by
        apply List.getElem?_eq_none
        simp; omega
      have hj_none : (ν'.map (· * 3))[j]? = none := by
        apply List.getElem?_eq_none
        simp; omega
      rw [hi_none, hj_none]
      simp only [Option.getD_none]
      omega
  · -- ∀ x ∈ l, 0 < x
    intro x hx
    simp only [List.length_map, List.length_range, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi_lt : i < core.length := by omega
    rw [List.getElem?_eq_getElem (h := hi_lt), Option.getD_some]
    have hpos : 0 < core[i] := hcore_flat.1.2 core[i] (List.getElem_mem hi_lt)
    omega

/-- The componentwise sum `zipAddPad core (3ν')` carries the residues of `core`
through unchanged: filtering out multiples of 3 and reading mod 3 gives back the
nonzero residue sequence of `core`. -/
private lemma getElem?_map_mul3_mod3 (ν' : List ℕ) (i : ℕ) :
    ((ν'.map (· * 3))[i]?.getD 0) % 3 = 0 := by
  by_cases hi : i < ν'.length
  · have hlen : i < (ν'.map (· * 3)).length := by simp; exact hi
    rw [List.getElem?_eq_getElem (h := hlen), Option.getD_some, List.getElem_map]
    omega
  · have hlen : (ν'.map (· * 3)).length ≤ i := by simp; omega
    rw [List.getElem?_eq_none hlen, Option.getD_none]

theorem sortedRec_length_le (l : List ℕ) (hflat : IsThreeFlat l) :
    (conjugate (sortedRec l)).length ≤ (residueCore (nonzeroResSeq l)).length := by
  unfold sortedRec
  exact forward_record_length_le l hflat

/-- Structural decomposition of `phi3Forward`: it equals `core + 3·conjugate(sortedRec)`,
where `core = residueCore (nonzeroResSeq l)`. -/
theorem phi3Forward_decomposition (l : List ℕ) :
    phi3Forward l =
      zipAddPad (residueCore (nonzeroResSeq l)) ((conjugate (sortedRec l)).map (· * 3)) := by
  unfold phi3Forward sortedRec
  rfl

theorem phi3_well_defined (l : List ℕ) (hflat : IsThreeFlat l) :
    IsThreeRegular (phi3Forward l) := by
  -- Abbreviations
  set v := nonzeroResSeq l
  set core := residueCore v
  set ν := sortedRec l
  set ν' := conjugate ν
  -- Key hypotheses
  have hv : ∀ x ∈ v, x = 1 ∨ x = 2 := nonzeroResSeq_in_one_two l
  have hcore_flat : IsThreeFlat core := residueCore_isThreeFlat v hv
  have hcore_reg : IsThreeRegular core := residueCore_isThreeRegular v hv
  have hlen : ν'.length ≤ core.length := sortedRec_length_le l hflat
  -- Decomposition: phi3Forward l = zipAddPad core (ν'.map (· * 3))
  have hdecomp : phi3Forward l = zipAddPad core (ν'.map (· * 3)) :=
    phi3Forward_decomposition l
  -- Part 1: IsPositivePartition (phi3Forward l)
  -- Need IsPartition ν', i.e., ν'.Pairwise (· ≥ ·)
  have hν'_part : IsPartition ν' := by
    show (conjugate (sortedRec l)).Pairwise (· ≥ ·)
    cases h : sortedRec l with
    | nil => simp [conjugate]
    | cons a rest => exact conj_pairwise a rest
  have hpos_part : IsPositivePartition (zipAddPad core (ν'.map (· * 3))) :=
    zipAddPad_isPositivePartition_of_core_3flat core ν' hcore_flat hν'_part hlen
  -- Part 2: ∀ x ∈ phi3Forward l, ¬(3 ∣ x)
  have hndiv3 : ∀ x ∈ zipAddPad core (ν'.map (· * 3)), ¬(3 ∣ x) := by
    intro x hx
    unfold zipAddPad at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i < core.length := by simp [List.length_map] at hi; omega
    have hmod_mul3 := getElem?_map_mul3_mod3 ν' i
    have hgetD : core[i]?.getD 0 = core[i] := by
      rw [List.getElem?_eq_getElem (h := hi'), Option.getD_some]
    rw [hgetD]
    have hcore_not_div := hcore_reg.2 (core[i]) (List.getElem_mem hi')
    intro hdvd
    apply hcore_not_div
    have h3 : (core[i] + ((ν'.map (· * 3))[i]?.getD 0)) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hdvd
    omega
  -- Combine
  rw [hdecomp]
  exact ⟨hpos_part, hndiv3⟩

private lemma sum_getElem?_range (l : List ℕ) (n : ℕ) (hn : l.length ≤ n) :
    (List.map (fun i => l[i]?.getD 0) (List.range n)).sum = l.sum := by
  have h1 : List.map (fun i => l[i]?.getD 0) (List.range n) =
      l ++ List.replicate (n - l.length) 0 := by
    apply List.ext_getElem
    · simp [Nat.add_sub_cancel' hn]
    · intro i hi₁ hi₂
      simp only [List.getElem_map, List.getElem_range, List.getElem_append]
      split
      · next h => rw [List.getElem?_eq_getElem h, Option.getD_some]
      · next h =>
        push_neg at h; rw [List.getElem?_eq_none h, Option.getD_none]
        simp [List.getElem_replicate]
  rw [h1, List.sum_append, List.sum_replicate, smul_zero, Nat.add_zero]

private lemma zipAddPad_weight (l₁ l₂ : List ℕ) :
    partWeight (zipAddPad l₁ l₂) = partWeight l₁ + partWeight l₂ := by
  unfold partWeight zipAddPad
  simp only [List.sum_map_add]
  congr 1
  · exact sum_getElem?_range l₁ _ (Nat.le_max_left _ _)
  · exact sum_getElem?_range l₂ _ (Nat.le_max_right _ _)

private lemma sum_map_mul3 (l : List ℕ) :
    (l.map (· * 3)).sum = 3 * l.sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.sum_cons, ih]; ring

/-- The sorted record list is a (weakly decreasing) partition. -/
theorem sortedRec_isPartition (l : List ℕ) :
    IsPartition (sortedRec l) := by
  show List.Pairwise (· ≥ ·) (sortedRec l)
  suffices h : ∀ (xs : List ℕ), List.Pairwise (· ≥ ·) (xs.mergeSort (· ≥ ·)) by
    exact h _
  intro xs
  have h := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≥ b))
    (fun _ _ _ hab hbc => by simp_all; omega)
    (fun a b => by simp; omega) xs
  simpa using h

private lemma scanFromSmallest_rec_pos (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hA_pos : ∀ x ∈ A, 0 < x)
    (hrec : ∀ x ∈ rec, 0 < x) :
    ∀ x ∈ (scanFromSmallest fuel A idx rec).2, 0 < x := by
  induction fuel generalizing A idx rec with
  | zero => simpa [scanFromSmallest]
  | succ n ih =>
    simp only [scanFromSmallest]
    split
    · exact hrec
    · next h_not_ge =>
      split
      · next hcond =>
        apply ih
        · intro x hx
          exact hA_pos x (List.mem_of_mem_eraseIdx hx)
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact hrec x hx
          · subst hx
            simp only [isFlatRemovableBool, Bool.and_eq_true, decide_eq_true_eq,
                       beq_iff_eq] at hcond
            have hi : A.length - 1 - idx < A.length := hcond.1.1
            have hmod : A[A.length - 1 - idx]! % 3 = 0 := hcond.1.2
            rw [getElem!_pos A _ hi] at hmod
            have hpos := hA_pos (A[A.length - 1 - idx]) (List.getElem_mem hi)
            rw [getElem!_pos A _ hi]
            omega
      · apply ih (hA_pos := hA_pos); exact hrec

private lemma scanFromLargest_rec_pos (fuel : ℕ) (A : List ℕ) (idx : ℕ) (rec : List ℕ)
    (hrec : ∀ x ∈ rec, 0 < x) :
    ∀ x ∈ (scanFromLargest fuel A idx rec).2, 0 < x := by
  induction fuel generalizing A idx rec with
  | zero => simpa [scanFromLargest]
  | succ n ih =>
    simp only [scanFromLargest]
    split
    · exact hrec
    · next h_not_ge =>
      split
      · next hcond =>
        apply ih
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact hrec x hx
        · subst hx
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          have hval_pos : A[idx]! > 0 := hcond.2
          have hmod : A[idx]! % 3 = 0 := hcond.1
          have : A[idx]! / 3 ≥ 1 := by omega
          omega
      · apply ih; exact hrec

private lemma sortedRec_pos (l : List ℕ) (hflat : IsThreeFlat l) :
    ∀ x ∈ sortedRec l, 0 < x := by
  unfold sortedRec
  set sfs := scanFromSmallest (l.length + 1) l 0 []
  set sfl := scanFromLargest (sfs.1.length + 1) sfs.1 0 sfs.2
  intro x hx
  have hperm := List.mergeSort_perm sfl.2 (· ≥ ·)
  have hx_in_sfl : x ∈ sfl.2 := hperm.mem_iff.mp hx
  have hA_pos : ∀ y ∈ l, 0 < y := hflat.1.2
  have hrec₂_pos : ∀ y ∈ sfs.2, 0 < y :=
    scanFromSmallest_rec_pos _ l 0 [] hA_pos (by simp)
  exact scanFromLargest_rec_pos _ sfs.1 0 sfs.2 hrec₂_pos x hx_in_sfl

theorem phi3_weight_preserving (l : List ℕ) (hflat : IsThreeFlat l) :
    partWeight (phi3Forward l) = partWeight l := by
  set core := residueCore (nonzeroResSeq l)
  set ν := sortedRec l
  set ν' := conjugate ν
  rw [phi3Forward_decomposition l, zipAddPad_weight]
  have hmap_sum : partWeight (ν'.map (· * 3)) = 3 * partWeight ν' := by
    unfold partWeight; exact sum_map_mul3 ν'
  rw [hmap_sum]
  have hν_pos : IsPositivePartition ν :=
    ⟨sortedRec_isPartition l, sortedRec_pos l hflat⟩
  have hconj : partWeight ν' = partWeight ν := conjugate_weight ν hν_pos
  rw [hconj]
  -- Now goal is: partWeight core + 3 * partWeight ν = partWeight l
  -- forward_record_weight gives: partWeight l = partWeight core + 3 * rec₃.sum
  -- where rec₃.sum = ν.sum = partWeight ν (by mergeSort permutation)
  have hfrw := forward_record_weight l hflat
  -- The let-bound rec₃ in hfrw is (scanFromLargest ...).2, and
  -- sortedRec l = rec₃.mergeSort, so rec₃.sum = (sortedRec l).sum = partWeight ν
  suffices h : partWeight ν = (scanFromLargest
    ((scanFromSmallest (l.length + 1) l 0 []).1.length + 1)
    (scanFromSmallest (l.length + 1) l 0 []).1 0
    (scanFromSmallest (l.length + 1) l 0 []).2).2.sum by
    simp only at hfrw ⊢; linarith
  unfold partWeight
  show (sortedRec l).sum = _
  unfold sortedRec
  exact (List.mergeSort_perm _ _).sum_eq

theorem phi3_inverse_well_defined (l : List ℕ)
 :
    IsThreeFlat (phi3Inverse l) := by
  -- Definitional unfolding + cite no_raise_labels (A7).
  exact no_raise_labels l

/-! #### Helper lemmas for (C1) `phi3Inverse_residue_preserved` -/

private lemma filter_insertIdx_false' {α : Type*} (pr : α → Bool) (l : List α) (i : ℕ) (a : α)
    (ha : pr a = false) : (l.insertIdx i a).filter pr = l.filter pr := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => simp [List.insertIdx_zero, ha]
    | succ n => simp [List.insertIdx_of_length_lt (by simp : ([] : List α).length < n + 1)]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.insertIdx_zero, List.filter_cons, ha]
    | succ n =>
      rw [List.insertIdx_succ_cons]; simp only [List.filter_cons]
      split
      · congr 1; exact ih n
      · exact ih n

private lemma nonzeroResSeq_raised_aux' (A : List ℕ) (h start : ℕ) :
    nonzeroResSeq ((A.zipIdx start).map (fun (x, j) => if j < h then x + 3 else x)) =
    nonzeroResSeq A := by
  unfold nonzeroResSeq
  induction A generalizing start with
  | nil => simp
  | cons a as ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.filter_cons]
    by_cases hstart : start < h
    · simp only [hstart, ite_true]
      have hmod : (a + 3) % 3 = a % 3 := by omega
      have hfilt : (decide (¬((a + 3) % 3 == 0) = true)) = (decide (¬(a % 3 == 0) = true)) := by
        cases Nat.decEq (a % 3) 0 with
        | isTrue hh => simp [hh, hmod]
        | isFalse hh =>
          have hh2 : (a + 3) % 3 ≠ 0 := by omega
          simp [hh]
      simp only [hfilt]
      split
      · simp only [List.map_cons, hmod]; exact congrArg _ (ih (start + 1))
      · exact ih (start + 1)
    · simp only [hstart, ite_false]
      split
      · simp only [List.map_cons]; exact congrArg _ (ih (start + 1))
      · exact ih (start + 1)

private lemma nonzeroResSeq_insertIdx_mul3' (l : List ℕ) (i : ℕ) (k : ℕ) :
    nonzeroResSeq (l.insertIdx i (3 * k)) = nonzeroResSeq l := by
  unfold nonzeroResSeq; congr 1; apply filter_insertIdx_false'; simp

private lemma nonzeroResSeq_tryHard' (A : List ℕ) (p h : ℕ) (result : List ℕ)
    (hr : tryHardInsertion A p h = some result) :
    nonzeroResSeq result = nonzeroResSeq A := by
  simp only [tryHardInsertion] at hr
  split at hr
  · exact absurd hr (by simp)
  · split at hr
    · have heq := (Option.some.inj hr).symm; rw [heq]
      exact (nonzeroResSeq_insertIdx_mul3' _ _ _).trans (nonzeroResSeq_raised_aux' A h 0)
    · exact absurd hr (by simp)

private lemma nonzeroResSeq_findHard' (A : List ℕ) (p : ℕ) (h0 : ℕ) (result : List ℕ)
    (hr : findHardInsertion A p h0 = some result) :
    nonzeroResSeq result = nonzeroResSeq A := by
  unfold findHardInsertion at hr
  split at hr
  · exact absurd hr (by simp)
  · split at hr
    · exact nonzeroResSeq_tryHard' A p h0 _ (by rename_i h_try; exact h_try ▸ hr)
    · exact nonzeroResSeq_findHard' A p (h0 + 1) result hr
termination_by p + A.length + 1 - h0

private lemma nonzeroResSeq_tryEasy' (A : List ℕ) (p : ℕ) (result : List ℕ)
    (hr : tryEasyInsertion A p = some result) :
    nonzeroResSeq result = nonzeroResSeq A := by
  simp only [tryEasyInsertion] at hr
  split at hr
  · have heq := (Option.some.inj hr).symm; rw [heq]
    exact nonzeroResSeq_insertIdx_mul3' _ _ _
  · exact absurd hr (by simp)

/-- (C1.a) Per-step residue preservation: a single `performInsertion` step
preserves the nonzero residue sequence.  This is the substantive helper. -/
theorem nonzeroResSeq_performInsertion (A : List ℕ) (p : ℕ) :
    nonzeroResSeq (performInsertion A p) = nonzeroResSeq A := by
  unfold performInsertion
  split
  · exact nonzeroResSeq_findHard' A p 0 _ (by assumption)
  · split
    · exact nonzeroResSeq_tryEasy' A p _ (by assumption)
    · rfl

/-- (C1.b) Induction-step extension of (C1.a): a full `processInsertions ν A`
preserves the nonzero residue sequence.  Routine induction on `ν` using (C1.a). -/
theorem nonzeroResSeq_processInsertions (ν : List ℕ) (A : List ℕ) :
    nonzeroResSeq (processInsertions ν A) = nonzeroResSeq A := by
  induction ν generalizing A with
  | nil => rfl
  | cons p rest ih => simp [processInsertions]; rw [ih, nonzeroResSeq_performInsertion]

/-- (C1) Residue preservation under `processInsertions`: the inverse algorithm
preserves the nonzero residue sequence carried by the residue core, since every
insertion adds a multiple of 3 to existing parts (S2 inserts `3p`, S3 inserts
`3(p-h)` and adds 3 to `h` larger parts) and the residue core itself is
3-regular by `residueCore_isThreeRegular`. -/
theorem phi3Inverse_residue_preserved (l : List ℕ) :
    nonzeroResSeq (phi3Inverse l) = nonzeroResSeq l := by
  unfold phi3Inverse
  simp only [nonzeroResSeq_processInsertions]
  exact residueCore_residues (nonzeroResSeq l) (nonzeroResSeq_in_one_two l)

/-- (C1') Corollary of (C1) — the residue core of `phi3Inverse l` equals
the residue core of `l`. -/
theorem phi3Inverse_residueCore_eq (l : List ℕ) :
    residueCore (nonzeroResSeq (phi3Inverse l)) =
      residueCore (nonzeroResSeq l) := by
  exact congrArg residueCore (phi3Inverse_residue_preserved l)

/-- (C2) The substantive lemma: applying S2+S3 to `α := phi3Inverse l`
recovers exactly the `ν = conjugate q` that was extracted from `l`.
This is the right-inverse analog of `process_reverses_deletions`.
Substance of Andrews–Dhar Lemma "Compatibility with deletion algorithm". -/
theorem phi3Inverse_sortedRec_eq_nu (l : List ℕ) :
    let A_init := residueCore (nonzeroResSeq l)
    let q := (List.range A_init.length).map (fun i =>
      ((l[i]?.getD 0) - (A_init[i]?.getD 0)) / 3)
    let ν := conjugate q
    sortedRec (phi3Inverse l) = ν := by
  exact Labeled.phi3Inverse_sortedRec_eq_nu_via_labels l

/-- (C3') `zipAddPad`-equivalence replacing the false involution
`conjugate (conjugate q) = q` (which fails when `q` has trailing zeros, since
`conjugate` strips them). The trailing zeros sit at indices ≥ `A_init.length`,
where `zipAddPad A_init` pads with 0, so they don't affect the chain. -/

private lemma dropWhile_pos_zero_aux (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) :
    ∀ x ∈ l.dropWhile (fun a => decide (a > 0)), x = 0 := by
  induction l with
  | nil => simp [List.dropWhile]
  | cons a t ih =>
    simp [List.dropWhile]; split
    · exact ih (List.Pairwise.of_cons hl)
    · rename_i ha; simp at ha; intro x hx
      cases hx with
      | head => omega
      | tail _ hm => have : a ≥ x := List.rel_of_pairwise_cons hl hm; omega

private lemma filter_eq_filter_takeWhile_aux (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) (j : ℕ) :
    l.filter (fun x => decide (x ≥ j + 1)) =
    (l.takeWhile (fun a => decide (a > 0))).filter (fun x => decide (x ≥ j + 1)) := by
  conv_lhs => rw [show l = l.takeWhile (fun a => decide (a > 0)) ++ l.dropWhile (fun a => decide (a > 0))
    from (List.takeWhile_append_dropWhile ..).symm]
  rw [List.filter_append]
  suffices (l.dropWhile (fun a => decide (a > 0))).filter (fun x => decide (x ≥ j + 1)) = [] by
    rw [this, List.append_nil]
  apply List.filter_eq_nil_iff.mpr
  intro x hx; simp; have : x = 0 := dropWhile_pos_zero_aux l hl x hx; omega

private lemma conjugate_eq_conjugate_takeWhile_aux (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) :
    conjugate l = conjugate (l.takeWhile (fun a => decide (a > 0))) := by
  simp only [conjugate]
  cases l with
  | nil => simp [List.takeWhile]
  | cons a rest =>
    by_cases ha : 0 < a
    · have htw : (a :: rest).takeWhile (fun a => decide (a > 0)) =
          a :: rest.takeWhile (fun a => decide (a > 0)) := by
        simp [List.takeWhile, ha]
      rw [htw]
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        simp only [List.getElem_map, List.getElem_range]
        have h1 := filter_eq_filter_takeWhile_aux (a :: rest) hl i
        rw [htw] at h1
        exact congrArg List.length h1
    · push_neg at ha
      have ha_zero : a = 0 := by omega
      have htw : (a :: rest).takeWhile (fun x => decide (x > 0)) = [] := by
        simp [List.takeWhile, ha_zero]
      rw [htw, ha_zero]; simp

private lemma getElem_zero_past_takeWhile_aux (l : List ℕ) (hl : l.Pairwise (· ≥ ·))
    (i : ℕ) (hi : i < l.length) (hge : (l.takeWhile (fun a => decide (a > 0))).length ≤ i) :
    l[i] = 0 := by
  set tw := l.takeWhile (fun a => decide (a > 0))
  set dw := l.dropWhile (fun a => decide (a > 0))
  have hsplit : l = tw ++ dw := (List.takeWhile_append_dropWhile ..).symm
  have hlen : tw.length + dw.length = l.length := by
    rw [← List.length_append]; congr 1; exact List.takeWhile_append_dropWhile ..
  have hval : l[i] = (tw ++ dw)[i]'(by rw [List.length_append]; omega) := by congr 1
  rw [hval, List.getElem_append_right (by omega : tw.length ≤ i)]
  exact dropWhile_pos_zero_aux l hl _ (List.getElem_mem _)

private lemma getElem_map_mul3_agree_aux (q : List ℕ) (hq : q.Pairwise (· ≥ ·)) (i : ℕ) :
    (List.map (· * 3) (q.takeWhile (fun a => decide (a > 0))))[i]?.getD 0
    = (List.map (· * 3) q)[i]?.getD 0 := by
  simp only [List.getElem?_map]
  set qp := q.takeWhile (fun a => decide (a > 0))
  by_cases hiqp : i < qp.length
  · have hiq : i < q.length := Nat.lt_of_lt_of_le hiqp
      (List.IsPrefix.sublist (List.takeWhile_prefix _)).length_le
    rw [List.getElem?_eq_getElem hiqp, List.getElem?_eq_getElem hiq]
    simp
    exact List.IsPrefix.getElem (List.takeWhile_prefix _) hiqp
  · push_neg at hiqp
    rw [List.getElem?_eq_none (by omega)]
    simp
    by_cases hiq : i < q.length
    · rw [List.getElem?_eq_getElem hiq]; simp
      have : q[i] = 0 := getElem_zero_past_takeWhile_aux q hq i hiq hiqp
      simp [this]
    · rw [List.getElem?_eq_none (by omega)]; simp

theorem conjugate_conjugate_zipAddPad_q (l : List ℕ) (hreg : IsThreeRegular l) :
    let A_init := residueCore (nonzeroResSeq l)
    let q := (List.range A_init.length).map (fun i =>
      ((l[i]?.getD 0) - (A_init[i]?.getD 0)) / 3)
    zipAddPad A_init ((conjugate (conjugate q)).map (· * 3))
      = zipAddPad A_init (q.map (· * 3)) := by
  intro A_init q
  have hq_part : IsPartition q := extract_isPartition l hreg
  have hq_len : q.length = A_init.length := by simp [q]
  set qp := q.takeWhile (fun a => decide (a > 0)) with hqp_def
  have hconj_eq : conjugate q = conjugate qp :=
    conjugate_eq_conjugate_takeWhile_aux q hq_part
  have hqp_pos : IsPositivePartition qp := ⟨
    List.Pairwise.sublist (List.IsPrefix.sublist (List.takeWhile_prefix _)) hq_part,
    fun x hx => by have := List.mem_takeWhile_imp hx; simp at this; exact this⟩
  have hcc_eq : conjugate (conjugate q) = qp := by
    rw [hconj_eq, conjugate_involution qp hqp_pos]
  have hqp_le : qp.length ≤ q.length :=
    (List.IsPrefix.sublist (List.takeWhile_prefix _)).length_le
  show zipAddPad A_init ((conjugate (conjugate q)).map (· * 3))
      = zipAddPad A_init (q.map (· * 3))
  simp only [zipAddPad, hcc_eq]
  have hrange_eq : max A_init.length (List.map (· * 3) qp).length
      = max A_init.length (List.map (· * 3) q).length := by
    simp only [List.length_map]; omega
  rw [hrange_eq]
  congr 1
  funext i
  congr 1
  exact getElem_map_mul3_agree_aux q hq_part i

/-- (C4) The 3-regular reconstruction: every 3-regular partition `l` equals
`zipAddPad A (3·q)` where `A` is its residue core and `q_i = (l_i - A_i)/3`.
This holds because `l_i ≡ A_i (mod 3)` for all `i` (both have residue
sequence `nonzeroResSeq l` after stripping multiples of 3 — wait, but
`l` is 3-regular so `nonzeroResSeq l = l mod 3` literally, and
`residueCore` reconstructs it). -/
theorem zipAddPad_reconstructs_threeRegular (l : List ℕ) (hreg : IsThreeRegular l) :
    let A := residueCore (nonzeroResSeq l)
    let q := (List.range A.length).map (fun i =>
      ((l[i]?.getD 0) - (A[i]?.getD 0)) / 3)
    l = zipAddPad A (q.map (· * 3)) := by
  intro A q
  have hv_12 : ∀ x ∈ nonzeroResSeq l, x = 1 ∨ x = 2 := nonzeroResSeq_in_one_two l
  have hnrs_eq : nonzeroResSeq l = l.map (· % 3) := nonzeroResSeq_of_threeRegular' l hreg
  have hAl : A.length = l.length := by
    have h1 := residueCore_length _ hv_12
    have h2 : (nonzeroResSeq l).length = l.length := by rw [hnrs_eq]; simp
    linarith
  -- Mod 3 match
  have hmod : ∀ (i : ℕ) (hi : i < l.length),
      A[i]'(by omega) % 3 = l[i]'hi % 3 := by
    intro i hi
    have hi' : i < A.length := by omega
    have hmap_eq : List.map (· % 3) A = l.map (· % 3) := by
      show List.map (· % 3) (residueCore (nonzeroResSeq l)) = l.map (· % 3)
      rw [residueCore_map_mod3 _ hv_12, hnrs_eq]
    have h1 : (List.map (· % 3) A)[i]'(by simp; exact hi') = A[i]'hi' % 3 :=
      List.getElem_map ..
    have h2 : (List.map (· % 3) l)[i]'(by simp; exact hi) = l[i]'hi % 3 :=
      List.getElem_map ..
    have h3 : (List.map (· % 3) A)[i]'(by simp; exact hi') =
              (List.map (· % 3) l)[i]'(by simp; exact hi) :=
      List.getElem_of_eq hmap_eq _
    linarith
  -- Domination via the 3-flat property
  have hAflat := residueCore_isThreeFlat _ hv_12
  have hdom : ∀ (i : ℕ) (hi : i < l.length), A[i]'(by omega) ≤ l[i]'hi := by
    have hAgaps : ∀ (i : ℕ) (hi : i + 1 < A.length),
        A[i]'(by omega) - A[i + 1]'hi < 3 := hAflat.2.1
    have hAlast : ∀ (h : A ≠ []), A.getLast h < 3 := hAflat.2.2
    suffices hsuff : ∀ k : ℕ, k ≤ l.length →
        (∀ i : ℕ, (hi : i < l.length) → l.length - k ≤ i → A[i]'(by omega) ≤ l[i]'hi) by
      intro i hi
      exact hsuff l.length (le_refl _) i hi (by omega)
    intro k
    induction k with
    | zero => intro _ i hi hge; omega
    | succ n ih_n =>
      intro hle i hi hge
      by_cases heq : l.length - (n + 1) = i
      · by_cases hn_zero : n = 0
        · have hAne : A ≠ [] := by intro h; simp [h] at hAl; omega
          have hA_i : A[i]'(by omega) < 3 := by
            have h := hAlast hAne
            rw [List.getLast_eq_getElem] at h
            have heqi : i = A.length - 1 := by omega
            exact heqi ▸ h
          have hpos_i : 0 < l[i]'hi := hreg.1.2 _ (List.getElem_mem hi)
          have hmod_i := hmod i hi
          omega
        · have hi_next : i + 1 < l.length := by omega
          have hih_next : A[i + 1]'(by omega) ≤ l[i + 1]'hi_next :=
            ih_n (by omega) (i + 1) hi_next (by omega)
          have hgap : A[i]'(by omega) - A[i + 1]'(by omega) < 3 :=
            hAgaps i (by omega)
          have hdec_i : l[i]'hi ≥ l[i + 1]'hi_next :=
            List.pairwise_iff_getElem.mp hreg.1.1 i (i + 1) hi (by omega) (by omega)
          have hmod_i := hmod i hi
          omega
      · exact ih_n (by omega) i hi (by omega)
  -- Use List.ext_getElem
  apply List.ext_getElem
  · simp [zipAddPad, show (q.map (· * 3)).length = A.length from by simp [q], hAl]
  · intro i hi₁ hi₂
    simp only [zipAddPad, List.getElem_map, List.getElem_range] at hi₂ ⊢
    have hiA : i < A.length := by omega
    have hiq3 : i < (q.map (· * 3)).length := by simp [q]; omega
    rw [List.getElem?_eq_getElem (h := hiA), Option.getD_some,
        List.getElem?_eq_getElem (h := hiq3), Option.getD_some]
    simp only [q, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (h := hi₁), Option.getD_some,
        List.getElem?_eq_getElem (h := hiA), Option.getD_some]
    have hle := hdom i hi₁
    have hmod_i := hmod i hi₁
    omega

/-- `compatibility` — the compatibility
lemma stated and proved by chaining the four helpers
(C1')+(C2)+(C3)+(C4). -/
theorem compatibility (l : List ℕ) (hreg : IsThreeRegular l) :
    phi3Forward (phi3Inverse l) = l := by
  set A_init := residueCore (nonzeroResSeq l) with hA_def
  set q := (List.range A_init.length).map (fun i =>
    ((l[i]?.getD 0) - (A_init[i]?.getD 0)) / 3) with hq_def
  set ν := conjugate q with hν_def
  -- Step 1: phi3Inverse l is 3-flat
  have hflat_inv : IsThreeFlat (phi3Inverse l) := no_raise_labels l
  -- Step 2: decompose phi3Forward
  rw [phi3Forward_decomposition (phi3Inverse l)]
  -- Step 3: rewrite residue core using C1'
  rw [phi3Inverse_residueCore_eq l]
  -- Step 4: rewrite sortedRec using C2
  have hC2 : sortedRec (phi3Inverse l) = ν := phi3Inverse_sortedRec_eq_nu l
  rw [hC2]
  -- Now goal: zipAddPad A_init ((conjugate (conjugate q)).map (· * 3)) = l
  -- Step 5: apply C3'
  have hC3 := conjugate_conjugate_zipAddPad_q l hreg
  rw [hC3]
  -- Now goal: zipAddPad A_init (q.map (· * 3)) = l
  -- Step 6: apply C4
  exact (zipAddPad_reconstructs_threeRegular l hreg).symm

/-! Phase 4: Cardinality-based proof of phi3_bijOn (Direction L). -/

namespace Phi3LCardinality

/-- Weight preservation for `phi3Inverse`, derived from `compatibility`. -/
private theorem phi3_inverse_weight_preserving
    (hGlaisher : Glaisher3) (l : List ℕ) (hreg : IsThreeRegular l) :
    partWeight (phi3Inverse l) = partWeight l := by
  have h_comp := compatibility l hreg
  have h_fwd := phi3_weight_preserving (phi3Inverse l)
    (phi3_inverse_well_defined l)
  rw [h_comp] at h_fwd
  exact h_fwd.symm

/-- Convert a `Nat.Partition N` to a sorted (weakly decreasing) list of parts. -/
private noncomputable def listOfNatPartition {N : ℕ} (p : Nat.Partition N) : List ℕ :=
  (Multiset.toList p.parts).mergeSort (· ≥ ·)

/-- Every weakly-decreasing positive partition list of a fixed sum is the
sorted-list image of some `Nat.Partition N`.  In particular, the set of such
lists is finite. -/
private lemma sortedPositivePartitionList_finite (N : ℕ) :
    {l : List ℕ | l.Pairwise (· ≥ ·) ∧ (∀ x ∈ l, 0 < x) ∧ l.sum = N}.Finite := by
  apply Set.Finite.subset (Set.finite_range (@listOfNatPartition N))
  intro l ⟨hpair, hpos, hsum⟩
  refine ⟨⟨(↑l : Multiset ℕ), ?_, ?_⟩, ?_⟩
  · intro i hi
    exact hpos i (by simpa using hi)
  · show (↑l : Multiset ℕ).sum = N
    rw [Multiset.sum_coe]
    exact hsum
  · -- Show: listOfNatPartition ⟨↑l, _, _⟩ = l.
    show (Multiset.toList (↑l : Multiset ℕ)).mergeSort (· ≥ ·) = l
    -- mergeSort of a perm of l, both sorted by (· ≥ ·), is uniquely l.
    have hsorted := List.pairwise_mergeSort
      (le := fun a b : ℕ => decide (a ≥ b))
      (fun a b c hab hbc => by simp_all; omega)
      (fun a b => by simp; omega)
      (Multiset.toList (↑l : Multiset ℕ))
    have hperm : ((Multiset.toList (↑l : Multiset ℕ)).mergeSort (· ≥ ·)).Perm l := by
      have h1 := List.mergeSort_perm (Multiset.toList (↑l : Multiset ℕ)) (· ≥ ·)
      have h2 : (Multiset.toList (↑l : Multiset ℕ)).Perm l := by
        have := Multiset.coe_toList (↑l : Multiset ℕ)
        exact Quotient.exact this
      exact h1.trans h2
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by simp at hab hba; omega)
      (by simpa using hsorted) hpair hperm

/-- The 3-flat partitions of fixed sum form a finite set. -/
private lemma threeFlat_atSum_finite (N : ℕ) :
    {l : List ℕ | IsThreeFlat l ∧ l.sum = N}.Finite := by
  apply Set.Finite.subset (sortedPositivePartitionList_finite N)
  intro l ⟨hflat, hsum⟩
  exact ⟨hflat.1.1, hflat.1.2, hsum⟩

end Phi3LCardinality

/-- **The Φ₃ bijection, packaged as `Set.BijOn`.**  At each fixed weight `N`,
`phi3Forward` is a bijection from the 3-flat partitions of `N` onto the
3-regular partitions of `N`.  This single statement bundles:
  * well-definedness (`Set.MapsTo`, from `phi3_well_defined` + weight preservation);
  * surjectivity (`Set.SurjOn`, i.e. Direction R / `compatibility`);
  * injectivity (`Set.InjOn`, i.e. Direction L), obtained from surjectivity
    between the two *finite* equicardinal slices (`Glaisher3` gives the equal
    cardinality; finiteness comes from `Phi3LCardinality`).

Both `phi3_left_inverse` and `phi3_right_inverse` fall out as corollaries. -/
theorem phi3_bijOn (hGlaisher : Glaisher3) (N : ℕ) :
    Set.BijOn phi3Forward
      {α | IsThreeFlat α ∧ α.sum = N}
      {β | IsThreeRegular β ∧ β.sum = N} := by
  set 𝓕 : Set (List ℕ) := {α | IsThreeFlat α ∧ α.sum = N} with h𝓕
  set 𝓡 : Set (List ℕ) := {β | IsThreeRegular β ∧ β.sum = N} with h𝓡
  -- partWeight = List.sum (definitionally).
  have hpw_def : ∀ (xs : List ℕ), partWeight xs = xs.sum := fun _ => rfl
  -- phi3Forward maps 𝓕 to 𝓡.
  have hMaps : Set.MapsTo phi3Forward 𝓕 𝓡 := by
    intro α ⟨hα_flat, hα_sum⟩
    refine ⟨phi3_well_defined α hα_flat, ?_⟩
    have := phi3_weight_preserving α hα_flat
    rw [hpw_def, hpw_def] at this
    rw [this]; exact hα_sum
  -- phi3Inverse maps 𝓡 to 𝓕.
  have hInvMaps : ∀ β ∈ 𝓡, phi3Inverse β ∈ 𝓕 := by
    intro β ⟨hβ_reg, hβ_sum⟩
    refine ⟨phi3_inverse_well_defined β, ?_⟩
    have := Phi3LCardinality.phi3_inverse_weight_preserving hGlaisher β hβ_reg
    rw [hpw_def, hpw_def] at this
    rw [this]; exact hβ_sum
  -- Surjectivity: phi3Inverse β ∈ 𝓕 is a preimage of β under phi3Forward.
  have hSurjEx : ∀ β ∈ 𝓡, ∃ α, ∃ (_ : α ∈ 𝓕), phi3Forward α = β := fun β hβ =>
    ⟨phi3Inverse β, hInvMaps β hβ, compatibility β hβ.1⟩
  have hSurj : Set.SurjOn phi3Forward 𝓕 𝓡 := by
    intro β hβ
    obtain ⟨α, hα, heq⟩ := hSurjEx β hβ
    exact ⟨α, hα, heq⟩
  -- Cardinality equality from Glaisher3 (Andrews–Dhar form) + finiteness.
  have hcard : 𝓕.ncard = 𝓡.ncard := hGlaisher N
  have hFinF : 𝓕.Finite := Phi3LCardinality.threeFlat_atSum_finite N
  -- Injectivity: a surjection between equicardinal finite sets is injective.
  have hInj : Set.InjOn phi3Forward 𝓕 := by
    intro a ha b hb hab
    exact Set.inj_on_of_surj_on_of_ncard_le
      (fun α (_ : α ∈ 𝓕) => phi3Forward α) (fun α h => hMaps h)
      (fun β hβ => hSurjEx β hβ) (le_of_eq hcard) ha hb hab hFinF
  exact ⟨hMaps, hInj, hSurj⟩

#print axioms phi3_bijOn
