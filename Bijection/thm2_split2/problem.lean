import Mathlib

/-!
# Problem: Bijection L and T between D_3^(0)(n) and R(n-1) partition sets

A partition is represented as a `Multiset ℕ` (multiset of nonnegative integer parts).
Sorting weakly decreasingly is canonical for multisets.

## Definitions

- `D3 n`: partitions of `n` whose smallest part occurs exactly 3 times and any
  part strictly larger occurs at most twice. By convention this captures
  `D3 0 = {{0,0,0}}` since the unique multiset of weight 0 satisfying the
  conditions is `{0,0,0}`.
- `tau μ`: number of parts of `μ` (with multiplicity) strictly larger than its
  smallest part.
- `D3_0 n`: subset of `D3 n` with `tau μ ≡ 0 (mod 3)`.
- `R N`: positive partitions of `N` such that no part occurs three or more
  times and either `len σ ≡ 2 (mod 3)`, or `len σ ≡ 0 (mod 3)` and the smallest
  part is unique. The latter alternative presupposes `σ ≠ 0`.
- `T : R N → D3_0 (N+1)`: maps σ by adjoining 1 (if `len σ % 3 = 2`) or raising
  the unique smallest part by 1 (if `len σ % 3 = 0`); then appends `(0,0,0)` if
  the smallest part of the result does not already occur three times.
- `L : D3_0 n → R (n-1)`: maps μ by first deleting the three zeros if 0 ∈ μ,
  then lowering one copy of the smallest part of the resulting positive
  partition by 1 (deleting the new part if it becomes 0).

## Statements

For all `n ≥ 1`:
1. `μ ∈ D3_0 n → L μ ∈ R (n-1)`.
2. `σ ∈ R (n-1) → T σ ∈ D3_0 n`.
3. `σ ∈ R (n-1) → L (T σ) = σ`.
4. `μ ∈ D3_0 n → T (L μ) = μ`.

This lemma is to be proved conditional on Theorem 1 (the Andrews--Kumar--Yee
identity), even though the combinatorial proof in the source does not actually
require it.
-/

namespace AndrewsDhar

/-- Length of a partition (with multiplicity). -/
def len (μ : Multiset ℕ) : ℕ := Multiset.card μ

/-- The smallest part of a partition. Returns `0` for the empty multiset. -/
noncomputable def smallestPart (μ : Multiset ℕ) : ℕ :=
  if h : μ.toFinset.Nonempty then μ.toFinset.min' h else 0

/-- The largest part of a partition. Returns `0` for the empty multiset. -/
noncomputable def largestPart (μ : Multiset ℕ) : ℕ :=
  if h : μ.toFinset.Nonempty then μ.toFinset.max' h else 0

/-- A positive partition: all parts are positive. -/
def IsPositive (μ : Multiset ℕ) : Prop := ∀ x ∈ μ, 0 < x

/-- The set `D_3(n)`. Unified definition: the conditions automatically force
`D_3(0) = {{0,0,0}}` (and `D_3(n)` for `n ≥ 1` matches Definition 1). -/
noncomputable def D3 (n : ℕ) : Set (Multiset ℕ) :=
  {μ | μ.sum = n ∧ μ ≠ 0 ∧
       μ.count (smallestPart μ) = 3 ∧
       ∀ v, smallestPart μ < v → μ.count v ≤ 2}

/-- The statistic `τ(μ) = #{parts strictly larger than the smallest part}`. -/
noncomputable def tau (μ : Multiset ℕ) : ℕ :=
  Multiset.card (μ.filter (fun v => smallestPart μ < v))

/-- The set `D_3^{(0)}(n) = {μ ∈ D_3(n) : τ(μ) ≡ 0 (mod 3)}`. -/
noncomputable def D3_0 (n : ℕ) : Set (Multiset ℕ) :=
  {μ ∈ D3 n | tau μ % 3 = 0}

/-- The set `R(N)`. -/
noncomputable def R (N : ℕ) : Set (Multiset ℕ) :=
  {σ | σ.sum = N ∧ IsPositive σ ∧
       (∀ v, σ.count v ≤ 2) ∧
       (len σ % 3 = 2 ∨
        (len σ % 3 = 0 ∧ σ ≠ 0 ∧ σ.count (smallestPart σ) = 1))}

/-- The map `T : R(N) → D_3^{(0)}(N+1)`. -/
noncomputable def T (σ : Multiset ℕ) : Multiset ℕ :=
  let η : Multiset ℕ :=
    if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
    else (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)
  if η.count (smallestPart η) = 3 then η else η + ({0, 0, 0} : Multiset ℕ)

/-- The map `L : D_3^{(0)}(n) → R(n-1)`. -/
noncomputable def L (μ : Multiset ℕ) : Multiset ℕ :=
  let η : Multiset ℕ := if (0 : ℕ) ∈ μ then μ - ({0, 0, 0} : Multiset ℕ) else μ
  let s := smallestPart η
  if s = 1 then η.erase 1 else (η.erase s) + ({s - 1} : Multiset ℕ)

/-! ### Theorem 1 (AKY identity), used as a hypothesis. -/

/-- `A(n)`: number of partitions of `n` into distinct positive parts. -/
noncomputable def A (n : ℕ) : ℕ :=
  Set.ncard {μ : Multiset ℕ | μ.sum = n ∧ IsPositive μ ∧ μ.Nodup}

/-- `B(n)`: number of partitions of `n` into odd positive parts. -/
noncomputable def B (n : ℕ) : ℕ :=
  Set.ncard {μ : Multiset ℕ | μ.sum = n ∧ IsPositive μ ∧ ∀ x ∈ μ, Odd x}

/-- `C(n)`: number of partitions of `n` with largest part even and parts not
exceeding half of the largest part are distinct. -/
noncomputable def C (n : ℕ) : ℕ :=
  Set.ncard {μ : Multiset ℕ | μ.sum = n ∧ IsPositive μ ∧ μ ≠ 0 ∧
             Even (largestPart μ) ∧
             (∀ v, 0 < v → v ≤ largestPart μ / 2 → μ.count v ≤ 1)}

/-- `D(n)`: number of partitions of `n` into nonnegative parts wherein the
smallest part appears exactly twice and no other parts are repeated. -/
noncomputable def D (n : ℕ) : ℕ :=
  Set.ncard {μ : Multiset ℕ | μ.sum = n ∧ μ ≠ 0 ∧
             μ.count (smallestPart μ) = 2 ∧
             (∀ v, smallestPart μ < v → μ.count v ≤ 1)}

/-- The AKY identity (Theorem 1.1 of the Andrews--Kumar--Yee paper). -/
def Thm1 : Prop :=
  ∀ n : ℕ, 0 < n → A n = B n ∧ A n = C (n + 1) ∧ 2 * A n = D (n + 1)

/-! ### Main Statement: Lemma L (the bijection between `D_3^{(0)}(n)` and `R(n-1)`). -/

/-- For every `n ≥ 1`, the maps `L : D_3^{(0)}(n) → R(n-1)` and
`T : R(n-1) → D_3^{(0)}(n)` are well-defined and mutually inverse bijections. -/
theorem lem_L (thm1 : Thm1) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ μ ∈ D3_0 n, L μ ∈ R (n - 1)) ∧
      (∀ σ ∈ R (n - 1), T σ ∈ D3_0 n) ∧
      (∀ σ ∈ R (n - 1), L (T σ) = σ) ∧
      (∀ μ ∈ D3_0 n, T (L μ) = μ) := by
  sorry

end AndrewsDhar
