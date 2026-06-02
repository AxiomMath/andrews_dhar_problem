import Mathlib

/-
# Problem: Bijection between $\mathcal{C}_3(n)$ partitions and $\mathcal{B}_3^{(2)}(n-1)$ via the finite Glaisher map

A partition (here) is a `Multiset ℕ` with all parts positive (i.e. `Nat.Partition n`).
The weight is the sum of its parts.

We formalize, conditional on Theorem 1 (Andrews--Kumar--Yee, Theorem 1.1 of the
arXiv paper "Andrews--Dhar"), Proposition $\gamma$ (Proposition `prop:gamma` of
`Thm2WithProof.tex`):

(a) For every $J \ge 1$, the finite Glaisher map
    $\Gamma_J : \mathcal{C}_{3,J}(n) \to \mathcal{B}_{3,J}^{(2)}(n-1)$
    is a bijection.

(b) Consequently, $\Gamma : \mathcal{C}_3(n) \to \mathcal{B}_3^{(2)}(n-1)$
    is a bijection.

The proof of Proposition $\gamma$ is independent of Theorem 1, but the
formalization shape (per `requirement.md` and `task.md`) requires a hypothesis
`thm1 : Thm1`.
-/

namespace PropGamma

open scoped Classical

/-- The largest part of a multiset of natural numbers (0 if the multiset is empty). -/
def largestPart (s : Multiset ℕ) : ℕ := s.fold max 0

/-! ## Auxiliary partition counts for Theorem 1 -/

/-- C-partitions of $n$: partitions of $n$ with even largest part such that all
parts at most half of the largest part are distinct (multiplicity $\le 1$). -/
def CPartitions (n : ℕ) : Set (Nat.Partition n) :=
  { p | p.parts ≠ 0 ∧ Even (largestPart p.parts) ∧
        ∀ t, 2 * t ≤ largestPart p.parts → p.parts.count t ≤ 1 }

/-- D-partitions of $n$ (over `Multiset ℕ`, allowing $0$ as a part):
the smallest part appears exactly twice and every other part is distinct. -/
def DPartitions (n : ℕ) : Set (Multiset ℕ) :=
  { s | s.sum = n ∧ ∃ a, s.count a = 2 ∧ (∀ b ∈ s, a ≤ b) ∧
        ∀ b ∈ s, b ≠ a → s.count b = 1 }

/-- Statement of Theorem 1 (Andrews--Kumar--Yee, Theorem 1.1 of the arXiv paper):
for every positive integer $n$,
$A(n) = B(n) = C(n+1) = \tfrac{1}{2} D(n+1)$,
where $A(n)$ counts partitions of $n$ into distinct parts, $B(n)$ counts
partitions of $n$ into odd parts, $C(n)$ counts the C-partitions of $n$, and
$D(n)$ counts the D-partitions of $n$. -/
def Thm1 : Prop := ∀ n : ℕ, 0 < n →
  (Nat.Partition.distincts n).card = (Nat.Partition.odds n).card ∧
  (Nat.Partition.distincts n).card = (CPartitions (n+1)).ncard ∧
  2 * (Nat.Partition.distincts n).card = (DPartitions (n+1)).ncard

/-! ## The Andrews--Dhar partition families -/

/-- The set $\mathcal{C}_3(n)$ of partitions of $n$ whose largest part is
divisible by $3$ (say $3J$ with $J\ge 1$), and every part at most $J$ has
multiplicity at most two. -/
def C₃ (n : ℕ) : Set (Nat.Partition n) :=
  { p | p.parts ≠ 0 ∧ ∃ J : ℕ, 1 ≤ J ∧ largestPart p.parts = 3 * J ∧
        ∀ t ≤ J, p.parts.count t ≤ 2 }

/-- The set $\mathcal{B}_3^{(2)}(N)$: partitions of $N$ into positive parts not
divisible by $3$ whose largest part is congruent to $2$ modulo $3$. By the
positivity / non-emptiness conventions in the source, this is empty for $N = 0$. -/
def B₃₂ (N : ℕ) : Set (Nat.Partition N) :=
  { p | p.parts ≠ 0 ∧ (∀ t ∈ p.parts, ¬ 3 ∣ t) ∧ largestPart p.parts % 3 = 2 }

/-- The set $\mathcal{C}_{3,J}(n)$: partitions in $\mathcal{C}_3(n)$ whose
largest part equals exactly $3J$. -/
def C₃J (n J : ℕ) : Set (Nat.Partition n) :=
  { p | p ∈ C₃ n ∧ largestPart p.parts = 3 * J }

/-- The set $\mathcal{B}_{3,J}^{(2)}(N)$: partitions in $\mathcal{B}_3^{(2)}(N)$
whose largest part equals exactly $3J - 1$. -/
def B₃₂J (N J : ℕ) : Set (Nat.Partition N) :=
  { p | p ∈ B₃₂ N ∧ largestPart p.parts = 3 * J - 1 }

/-! ## The finite Glaisher map $\Gamma$ -/

/-- Given a positive integer $t$, write $t = 3^a u$ with $3 \nmid u$, and
return the multiset of $3^a$ copies of $u$. (For $t = 0$ this returns
`{0}`, but that case is irrelevant for partitions of positive numbers.) -/
def expand3 (t : ℕ) : Multiset ℕ :=
  Multiset.replicate (3 ^ padicValNat 3 t) (t / 3 ^ padicValNat 3 t)

/-- The finite Glaisher map at the multiset level. Given a multiset $s$ with
largest entry $M = 3J$ (the case relevant for partitions in $\mathcal{C}_3(n)$):
replace one copy of $M$ by $M - 1 = 3J - 1$, and for every other part $t$,
replace $t$ by $3^{a}$ copies of $u$ where $t = 3^a u$ with $3 \nmid u$. -/
noncomputable def Γraw (s : Multiset ℕ) : Multiset ℕ :=
  let M := largestPart s
  (M - 1) ::ₘ ((s.erase M).bind expand3)

/-! ## Main statement (Proposition $\gamma$) -/

/-- Well-definedness of the finite Glaisher map $\Gamma$: for any
$\lambda \in \mathcal{C}_3(n)$, the multiset `Γraw λ.parts` underlies a
partition of $n-1$ which lies in $\mathcal{B}_3^{(2)}(n-1)$; moreover if the
largest part of $\lambda$ is exactly $3J$ then the resulting partition lies
in $\mathcal{B}_{3,J}^{(2)}(n-1)$. -/
lemma intermediate_lemma (thm1 : Thm1) {n : ℕ} (hn : 0 < n) :
    ∀ p : Nat.Partition n, p ∈ C₃ n →
      ∃ q : Nat.Partition (n - 1), q.parts = Γraw p.parts ∧ q ∈ B₃₂ (n - 1) ∧
        ∀ J : ℕ, 1 ≤ J → largestPart p.parts = 3 * J → q ∈ B₃₂J (n - 1) J := by
  sorry

/-- Proposition $\gamma$: conditional on Theorem 1,

(a) for every $J \ge 1$, the finite Glaisher map restricts to a bijection
    $\Gamma_J : \mathcal{C}_{3,J}(n) \to \mathcal{B}_{3,J}^{(2)}(n-1)$
    sending each $\lambda$ to the partition with underlying multiset
    `Γraw λ.parts`;

(b) consequently, $\Gamma : \mathcal{C}_3(n) \to \mathcal{B}_3^{(2)}(n-1)$ is
    a bijection sending each $\lambda$ to the partition with underlying multiset
    `Γraw λ.parts`. -/
theorem prop_gamma (thm1 : Thm1) {n : ℕ} (hn : 0 < n) :
    (∀ J : ℕ, 1 ≤ J → ∃ ΓJ : ↥(C₃J n J) → ↥(B₃₂J (n - 1) J),
        (∀ p : ↥(C₃J n J), (ΓJ p).1.parts = Γraw p.1.parts) ∧
        Function.Bijective ΓJ) ∧
    (∃ Γ : ↥(C₃ n) → ↥(B₃₂ (n - 1)),
        (∀ p : ↥(C₃ n), (Γ p).1.parts = Γraw p.1.parts) ∧
        Function.Bijective Γ) := by
  sorry

end PropGamma
