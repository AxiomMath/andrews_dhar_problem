import Mathlib

/-
# Problem: Andrews–Dhar D_3 partition equidistribution by τ mod 3

A partition of a nonnegative integer $n$ is a weakly decreasing finite list of
nonnegative integers $\mu = (\mu_1, \mu_2, \ldots, \mu_r)$ with $\mu_1 + \cdots + \mu_r = n$.
Parts equal to $0$ are allowed.

**Definition 1 (The Andrews–Dhar family $\mathcal{D}_3$).** For each positive integer $n$,
let $\mathcal{D}_3(n)$ be the set of partitions $\mu$ of $n$ into nonnegative parts such that
(1) the smallest part of $\mu$ occurs exactly three times, and (2) every part of $\mu$ which is
strictly greater than the smallest part of $\mu$ occurs at most twice. By convention,
$\mathcal{D}_3(0) := \{(0,0,0)\}$. Define $D_3(n) := |\mathcal{D}_3(n)|$.

**Definition 2 (The statistic $\tau$).** For $\mu \in \mathcal{D}_3(n)$, let
$\tau(\mu) := \#\{ j : \mu_j > \min_k \mu_k \}$.

**Definition 3 (Residue-class subsets).** For $i \in \{0, 1, 2\}$ and $n \ge 0$,
$\mathcal{D}_3^{(i)}(n) := \{\mu \in \mathcal{D}_3(n) : \tau(\mu) \equiv i \pmod 3\}$
and $D_3^{(i)}(n) := |\mathcal{D}_3^{(i)}(n)|$.

**Definition 4 (Triangular numbers).** $T_r := r(r+1)/2$.

# Main Statement(s)

**Theorem 1.** If $n \ge 1$ and $n \ne T_r + 1$ for every integer $r \ge 0$, then
$D_3^{(0)}(n) = D_3^{(1)}(n) = D_3^{(2)}(n) = D_3(n)/3$.
-/

namespace AndrewsDharD3

-- Main Definition(s)

/-- A list of nonnegative integers `μ` is a partition of `n` iff it is weakly decreasing
and the sum of its parts is `n`. Parts equal to `0` are allowed. -/
def IsPartition (μ : List ℕ) (n : ℕ) : Prop :=
  μ.Pairwise (· ≥ ·) ∧ μ.sum = n

/-- The smallest part of a list `μ` of natural numbers, with default value `0` for the
empty list. (For nonempty `μ`, this returns the actual minimum.) -/
def smallestPart (μ : List ℕ) : ℕ := μ.min?.getD 0

/-- A list `μ` belongs to the Andrews–Dhar set $\mathcal{D}_3(n)$ iff it is a partition of `n`,
nonempty, the smallest part of `μ` occurs exactly three times in `μ`, and every part of `μ`
strictly greater than the smallest part occurs at most twice. -/
def IsD3Partition (μ : List ℕ) (n : ℕ) : Prop :=
  IsPartition μ n ∧ μ ≠ [] ∧
  μ.count (smallestPart μ) = 3 ∧
  ∀ x ∈ μ, smallestPart μ < x → μ.count x ≤ 2

/-- The Andrews–Dhar set $\mathcal{D}_3(n)$. -/
def D3Set (n : ℕ) : Set (List ℕ) := { μ | IsD3Partition μ n }

/-- The Andrews–Dhar counting function $D_3(n) := |\mathcal{D}_3(n)|$. -/
noncomputable def D3 (n : ℕ) : ℕ := (D3Set n).ncard

/-- The statistic $\tau(\mu)$: the number of parts of `μ` strictly greater than the
smallest part of `μ` (counted with multiplicity). -/
def tau (μ : List ℕ) : ℕ := μ.countP (fun x => smallestPart μ < x)

/-- The residue-class subset $\mathcal{D}_3^{(i)}(n) := \{ \mu \in \mathcal{D}_3(n) :
\tau(\mu) \equiv i \pmod 3 \}$. -/
def D3iSet (i n : ℕ) : Set (List ℕ) := { μ | IsD3Partition μ n ∧ tau μ % 3 = i % 3 }

/-- The cardinality $D_3^{(i)}(n) := |\mathcal{D}_3^{(i)}(n)|$. -/
noncomputable def D3i (i n : ℕ) : ℕ := (D3iSet i n).ncard

/-- The `r`-th triangular number $T_r = r(r+1)/2$. -/
def triangular (r : ℕ) : ℕ := r * (r + 1) / 2

-- Main Statement(s)

/-- **Theorem 1 (Residue-class equidistribution for $\mathcal{D}_3$).**
If $n \ge 1$ and $n \ne T_r + 1$ for every integer $r \ge 0$, then
$D_3^{(0)}(n) = D_3^{(1)}(n) = D_3^{(2)}(n) = D_3(n)/3$.

We state this as: all three residue-class counts agree, and three times any of them equals
$D_3(n)$ (so in particular $3 \mid D_3(n)$ and each $D_3^{(i)}(n) = D_3(n)/3$). -/
theorem D3_equidistribution (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1) :
    D3i 0 n = D3i 1 n ∧ D3i 1 n = D3i 2 n ∧ 3 * D3i 0 n = D3 n := by
  sorry

end AndrewsDharD3
