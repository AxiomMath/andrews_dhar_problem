import Mathlib

/-
# Problem: Conjugation bijection between repetition-bounded partitions and
3-flat partitions with first nonzero residue 2

This file formalizes:

* The statement of Theorem 1 (Theorem 1.4 of the Andrews--Dhar paper):
  for every integer $m \ge 2$ and every non-negative integer $n$,
  $$ C_m(n) = \frac{D_m(n) + E_m(n)}{m}, $$
  where $C_m, D_m$ are concrete partition-counting functions and $E_m$ is the
  integer sequence defined by a specific generating function $\varepsilon_m(q)$.

* The intermediate lemma: for a positive partition $\sigma$ with conjugate
  $\alpha = \sigma'$, the multiplicity of any positive integer $k$ in $\sigma$
  equals $\alpha_k - \alpha_{k+1}$ (with $\alpha_{\ell(\alpha)+1} := 0$).

* The main lemma `lem_conj`: conjugation induces a bijection
  $\mathcal R(N) \longrightarrow \mathcal F^{(2)}(N)$, $\sigma \mapsto \sigma'$.

The lemma is stated conditionally on `thm1 : Thm1` per the task requirement.
The proof of `lem:conj` does not actually use Theorem 1, so the hypothesis is
unused (as `problem.md` explicitly notes).
-/

namespace AndrewsDhar

open scoped Classical

-- ===========================================================================
-- Main Definition(s): combinatorial / list-based partitions
-- ===========================================================================

/-- A *partition* (problem.md, Definition 1) is a weakly-decreasing finite
list of non-negative natural numbers. -/
def IsPart (l : List ℕ) : Prop := l.Pairwise (· ≥ ·)

/-- A *positive partition* (problem.md, Definition 2) is a weakly-decreasing
finite list of strictly positive natural numbers. -/
def IsPosPart (l : List ℕ) : Prop :=
  l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, 0 < x

/-- The *weight* $|\lambda|$ of a partition is the sum of its parts. -/
def weight (l : List ℕ) : ℕ := l.sum

/-- The *length* $\ell(\lambda)$ of a partition is the number of parts. -/
def length (l : List ℕ) : ℕ := l.length

/-- The *conjugate* $\lambda'$ of a partition
$\lambda = (\lambda_1, \ldots, \lambda_r)$ is the partition whose $i$-th part
(1-indexed) is $\#\{j : \lambda_j \ge i\}$. We construct it as the list of
length $\lambda_1$ whose entries (in order) are
$\#\{j : \lambda_j \ge 1\}, \ldots, \#\{j : \lambda_j \ge \lambda_1\}$. -/
def conjList (l : List ℕ) : List ℕ :=
  (List.range (l.headD 0)).map (fun i => l.countP (fun x => decide (i + 1 ≤ x)))

/-- A positive partition $\alpha = (\alpha_1, \ldots, \alpha_r)$ is *$3$-flat*
(problem.md, Definition 4) if all consecutive differences of
$(\alpha_1, \ldots, \alpha_r, 0)$ are less than $3$. Equivalently:
$\alpha_i - \alpha_{i+1} < 3$ for $1 \le i < r$ and $\alpha_r < 3$. -/
def Is3Flat (l : List ℕ) : Prop :=
  ∀ i : ℕ, i < l.length → (l.getD i 0) - (l.getD (i + 1) 0) < 3

/-- The *first nonzero residue mod $3$* (problem.md, Definition 5) of a
positive partition is the residue $\bmod\,3$ of its first part that is not
divisible by $3$. It is `none` exactly when every part is divisible by $3$
(including the empty partition). -/
def firstNonzeroRes3 (l : List ℕ) : Option ℕ :=
  (l.find? (fun x => decide (x % 3 ≠ 0))).map (fun x => x % 3)

/-- The set $\mathcal F^{(2)}(N)$ (problem.md, Definition 6): the set of
$3$-flat positive partitions of weight $N$ whose first nonzero residue equals
$2$. By convention $\mathcal F^{(2)}(0) = \varnothing$ (the empty partition
fails the residue condition). -/
def setF2 (N : ℕ) : Set (List ℕ) :=
  { α | IsPosPart α ∧ weight α = N ∧ Is3Flat α ∧ firstNonzeroRes3 α = some 2 }

/-- The set $\mathcal R(N)$ (problem.md, Definition 7): the set of positive
partitions $\sigma$ of $N$ such that
* no part of $\sigma$ occurs three or more times (multiplicities are $\le 2$);
* either $\ell(\sigma) \equiv 2 \pmod 3$, or $\ell(\sigma) \equiv 0 \pmod 3$
  *and* the smallest part of $\sigma$ is unique.

By convention $\mathcal R(0) = \varnothing$: we explicitly require
$\sigma \ne []$. -/
def setR (N : ℕ) : Set (List ℕ) :=
  { σ | IsPosPart σ ∧ weight σ = N ∧ σ ≠ [] ∧
        (∀ k, σ.count k ≤ 2) ∧
        (σ.length % 3 = 2 ∨
          (σ.length % 3 = 0 ∧ σ.count (σ.getLastD 0) = 1)) }

-- ===========================================================================
-- Definitions for Theorem 1 ($C_m$, $D_m$, $E_m$).
--
-- We avoid the buggy `List.sublists` enumeration of partitions used in
-- previous attempts and instead use a *set-based* definition together with
-- `Set.ncard`. This gives an honest mathematical definition of the partition
-- counting functions $C_m(n)$ and $D_m(n)$ from problem.md, Definition 8.
-- ===========================================================================

/-- The set of *partitions of $n$ into non-negative parts*: weakly-decreasing
finite lists of natural numbers summing to $n$. (Parts are allowed to be
zero; this matches the convention used by $D_m$.) -/
def partitionsOf (n : ℕ) : Set (List ℕ) :=
  { l | l.Pairwise (· ≥ ·) ∧ l.sum = n }

/-- The set of *positive partitions of $n$*: weakly-decreasing finite lists
of strictly positive natural numbers summing to $n$. -/
def positivePartitionsOf (n : ℕ) : Set (List ℕ) :=
  { l | IsPosPart l ∧ l.sum = n }

/-- The condition defining $C_m(n)$ for $n \ge 1$: $\sigma$ is a non-empty
positive partition of $n$ whose largest part is $m j$ for some $j$, and every
part $k$ with $1 \le k \le j$ occurs strictly fewer than $m$ times. -/
def isCmPart (m : ℕ) (σ : List ℕ) : Prop :=
  σ ≠ [] ∧
    ∃ j : ℕ, σ.headD 0 = m * j ∧ ∀ k : ℕ, 1 ≤ k → k ≤ j → σ.count k < m

/-- $C_m(n)$ (problem.md, Definition 8): the number of partitions of $n$ in
which the largest part is divisible by $m$ (say $m j$) and all parts $\le j$
repeat fewer than $m$ times. By convention $C_m(0) := 1$. -/
noncomputable def C_m (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else Set.ncard { σ ∈ positivePartitionsOf n | isCmPart m σ }

/-- The condition defining $D_m(n)$: $\sigma$ is a non-empty partition of $n$
into non-negative parts in which the smallest part (the last entry of the
weakly-decreasing list, which may be $0$) occurs exactly $m$ times and all
strictly larger parts repeat fewer than $m$ times. -/
def isDmPart (m : ℕ) (σ : List ℕ) : Prop :=
  σ ≠ [] ∧
    σ.count (σ.getLastD 0) = m ∧
    ∀ k : ℕ, σ.getLastD 0 < k → σ.count k < m

/-- $D_m(n)$ (problem.md, Definition 8): the number of partitions of $n$ into
*non-negative* parts in which the smallest part occurs exactly $m$ times and
all other parts repeat fewer than $m$ times. -/
noncomputable def D_m (m n : ℕ) : ℕ :=
  Set.ncard { σ ∈ partitionsOf n | isDmPart m σ }

/-- Primitive $m$-th root of unity $\zeta_m = e^{2\pi i / m}$. -/
noncomputable def zeta_m (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / m)

/-- The *finite* $q$-Pochhammer-style truncation
$\prod_{i=0}^{N-1}(1 - A \cdot X^i)$ in $\mathbb{C}[[q]]$. For `A` of valuation
$\ge 1$ and $N$ large enough relative to a given degree, this stabilizes to
the infinite product. -/
noncomputable def qPochFinite (A : PowerSeries ℂ) (N : ℕ) : PowerSeries ℂ :=
  ∏ i ∈ Finset.range N, (1 - A * (PowerSeries.X : PowerSeries ℂ) ^ i)

/-- The infinite $q$-Pochhammer-style product
$(A;q)_\infty = \prod_{i \ge 0}(1 - A \cdot X^i)$ in $\mathbb{C}[[q]]$,
defined coefficient-wise by reading off the (stabilized) coefficient from the
finite truncation `qPochFinite A (n+1)`. When `A` has valuation $\ge 1$, this
agrees with the genuine infinite product. -/
noncomputable def qPochInf (A : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk
    (fun n => PowerSeries.coeff (R := ℂ) n (qPochFinite A (n + 1)))

/-- The generating function $\varepsilon_m(q)$ of $E_m$ (problem.md,
Definition 8), as a formal power series in $\mathbb{C}[[q]]$:
$$ \varepsilon_m(q) = \sum_{n=0}^{\infty} q^{m n} \, (q^{m(n+1)};q)_\infty
  \sum_{j=1}^{m-1} \frac{1}{(\zeta_m^{\,j}\, q^{n+1};q)_\infty}. $$
The outer sum is degree-by-degree finite because the term indexed by $n$
contributes only to coefficients of degree $\ge m n$; we express each
coefficient $[q^N]\varepsilon_m(q)$ as a finite sum (over $n$ with
$0 \le n \le N$). -/
noncomputable def epsilon_m (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (fun N =>
    ∑ n ∈ Finset.range (N + 1),
      PowerSeries.coeff (R := ℂ) N
        ((PowerSeries.X : PowerSeries ℂ) ^ (m * n)
          * qPochInf ((PowerSeries.X : PowerSeries ℂ) ^ (m * (n + 1)))
          * ∑ j ∈ Finset.Ico 1 m,
              (qPochInf
                ((zeta_m m) ^ j • ((PowerSeries.X : PowerSeries ℂ) ^ (n + 1))))⁻¹))

/-- $E_m^{\mathbb{C}}(n)$: the $n$-th coefficient of the generating function
$\varepsilon_m(q)$, viewed in $\mathbb{C}$. The Andrews--Dhar paper proves
these coefficients are integers; this is part of the content of `Thm1`
below. -/
noncomputable def E_m_complex (m n : ℕ) : ℂ :=
  PowerSeries.coeff (R := ℂ) n (epsilon_m m)

/-- **Theorem 1** (Theorem 1.4 of the Andrews--Dhar paper, *assumed*): for
every integer $m \ge 2$ and every non-negative integer $n$, the complex
coefficient $E_m^{\mathbb{C}}(n)$ is in fact an integer $E_m(n) \in \mathbb{Z}$
and the identity
$$ m \cdot C_m(n) = D_m(n) + E_m(n) $$
holds in $\mathbb{Z}$. This packages both the integrality of $E_m$ and the
arithmetic identity that defines the theorem. -/
def Thm1 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ),
    ∃ Em : ℤ, ((Em : ℂ) = E_m_complex m n) ∧
      ((m : ℤ) * (C_m m n : ℤ) = (D_m m n : ℤ) + Em)

-- ===========================================================================
-- Main Statement(s)
-- ===========================================================================

/-- **Intermediate lemma (the conjugation dictionary).**
For any positive partition $\sigma$ with conjugate $\alpha = \sigma'$, the
multiplicity of any positive integer $k$ in $\sigma$ equals
$\alpha_k - \alpha_{k+1}$, where we set $\alpha_j := 0$ for $j$ out of range.
In 0-indexed Lean lists, this says
`σ.count k = (conjList σ).getD (k-1) 0 - (conjList σ).getD k 0`
for `1 ≤ k`. -/
lemma intermediate_lemma (thm1 : Thm1) :
    ∀ σ : List ℕ, IsPosPart σ → ∀ k : ℕ, 1 ≤ k →
      σ.count k =
        (conjList σ).getD (k - 1) 0 - (conjList σ).getD k 0 := by
  sorry

/-- **Lemma `lem:conj`.** For every non-negative integer $N$, conjugation
induces a bijection $\mathcal R(N) \to \mathcal F^{(2)}(N)$,
$\sigma \mapsto \sigma'$. -/
theorem lem_conj (thm1 : Thm1) (N : ℕ) :
    Set.BijOn conjList (setR N) (setF2 N) := by
  sorry

end AndrewsDhar
