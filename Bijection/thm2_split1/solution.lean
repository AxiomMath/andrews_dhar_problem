import Mathlib

namespace PropGamma

open scoped Classical

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Definitions -/

/-- The largest part of a multiset of natural numbers (0 if the multiset is empty). -/
def largestPart (s : Multiset ℕ) : ℕ := s.fold max 0

/-- C-partitions of $n$: partitions of $n$ with even largest part such that all
parts at most half of the largest part are distinct (multiplicity $\le 1$). -/
def CPartitions (n : ℕ) : Set (Nat.Partition n) :=
  { p | p.parts ≠ 0 ∧ Even (largestPart p.parts) ∧
        ∀ t, 2 * t ≤ largestPart p.parts → p.parts.count t ≤ 1 }

/-- D-partitions of $n$: the smallest part appears exactly twice and every other part is distinct. -/
def DPartitions (n : ℕ) : Set (Multiset ℕ) :=
  { s | s.sum = n ∧ ∃ a, s.count a = 2 ∧ (∀ b ∈ s, a ≤ b) ∧
        ∀ b ∈ s, b ≠ a → s.count b = 1 }

/-- Statement of Theorem 1 (Andrews--Kumar--Yee). -/
def Thm1 : Prop := ∀ n : ℕ, 0 < n →
  (Nat.Partition.distincts n).card = (Nat.Partition.odds n).card ∧
  (Nat.Partition.distincts n).card = (CPartitions (n+1)).ncard ∧
  2 * (Nat.Partition.distincts n).card = (DPartitions (n+1)).ncard

def C₃ (n : ℕ) : Set (Nat.Partition n) :=
  { p | p.parts ≠ 0 ∧ ∃ J : ℕ, 1 ≤ J ∧ largestPart p.parts = 3 * J ∧
        ∀ t ≤ J, p.parts.count t ≤ 2 }

def B₃₂ (N : ℕ) : Set (Nat.Partition N) :=
  { p | p.parts ≠ 0 ∧ (∀ t ∈ p.parts, ¬ 3 ∣ t) ∧ largestPart p.parts % 3 = 2 }

def C₃J (n J : ℕ) : Set (Nat.Partition n) :=
  { p | p ∈ C₃ n ∧ largestPart p.parts = 3 * J }

def B₃₂J (N J : ℕ) : Set (Nat.Partition N) :=
  { p | p ∈ B₃₂ N ∧ largestPart p.parts = 3 * J - 1 }

def expand3 (t : ℕ) : Multiset ℕ :=
  Multiset.replicate (3 ^ padicValNat 3 t) (t / 3 ^ padicValNat 3 t)

noncomputable def Γraw (s : Multiset ℕ) : Multiset ℕ :=
  let M := largestPart s
  (M - 1) ::ₘ ((s.erase M).bind expand3)

/-! ## Basic lemmas about `largestPart` -/

/-- Every element of `s` is at most `largestPart s`. -/
lemma le_largestPart {s : Multiset ℕ} {x : ℕ} (hx : x ∈ s) :
    x ≤ largestPart s := by
  unfold largestPart
  induction s using Multiset.induction_on with
  | empty => simp at hx
  | cons a s ih =>
    rw [Multiset.fold_cons_left]
    rcases Multiset.mem_cons.mp hx with rfl | hx'
    · exact le_max_left _ _
    · exact le_trans (ih hx') (le_max_right _ _)

/-- If `s` is a non-empty multiset of natural numbers, then `largestPart s` is a member of `s`. -/
lemma largestPart_mem {s : Multiset ℕ} (hs : s ≠ 0) : largestPart s ∈ s := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hs
  | cons a s' ih =>
    unfold largestPart
    rw [Multiset.fold_cons_left]
    by_cases hs' : s' = 0
    · subst hs'; simp
    · rcases le_or_gt a (s'.fold max 0) with hle | hlt
      · rw [max_eq_right hle]; exact Multiset.mem_cons_of_mem (ih hs')
      · rw [max_eq_left hlt.le]; exact Multiset.mem_cons_self a s'

/-- Characterization of `largestPart`: if `M ∈ s` and every element of `s`
is `≤ M`, then `largestPart s = M`. -/
lemma largestPart_eq {s : Multiset ℕ} {M : ℕ}
    (hMem : M ∈ s) (hUB : ∀ x ∈ s, x ≤ M) :
    largestPart s = M :=
  have hs : s ≠ 0 := fun h => by rw [h] at hMem; simp at hMem
  le_antisymm (hUB _ (largestPart_mem hs)) (le_largestPart hMem)

/-- Every element of `expand3 t` equals `t / 3 ^ padicValNat 3 t`. -/
lemma mem_expand3 {t x : ℕ} (hx : x ∈ expand3 t) :
    x = t / 3 ^ padicValNat 3 t :=
  Multiset.eq_of_mem_replicate hx

/-- The sum of `expand3 t` equals `t`. Since `t = 3 ^ a * u` with `a = padicValNat 3 t`
    and `u = t / 3 ^ a` (using `3 ^ a ∣ t` when `t > 0`; for `t = 0`, both sides are 0). -/
lemma expand3_sum (t : ℕ) : (expand3 t).sum = t := by
  unfold expand3
  rw [Multiset.sum_replicate, smul_eq_mul]
  exact Nat.mul_div_cancel' (pow_padicValNat_dvd)

/-- For `t > 0`, every element of `expand3 t` is positive. -/
lemma expand3_pos {t : ℕ} (ht : 0 < t) {x : ℕ} (hx : x ∈ expand3 t) : 0 < x := by
  unfold expand3 at hx
  rw [Multiset.eq_of_mem_replicate hx]
  exact Nat.div_pos (Nat.le_of_dvd ht pow_padicValNat_dvd) (by positivity)

/-- A 3-free positive integer is a positive integer not divisible by 3. -/
def ThreeFree (b : ℕ) : Prop := 1 ≤ b ∧ ¬ 3 ∣ b

/-- Every positive integer `v` decomposes uniquely as `v = b * 3^k`
where `b = v / 3 ^ padicValNat 3 v` is 3-free. -/
lemma three_free_decomposition (v : ℕ) (hv : 1 ≤ v) :
    ThreeFree (v / 3 ^ padicValNat 3 v) ∧
    v = (v / 3 ^ padicValNat 3 v) * 3 ^ padicValNat 3 v := by
  set k := padicValNat 3 v
  set b := v / 3 ^ k
  have hp3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have heq : v = b * 3 ^ k := (Nat.div_mul_cancel pow_padicValNat_dvd).symm
  have hbpos : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · rw [hb0, Nat.zero_mul] at heq; omega
    · exact hbpos
  refine ⟨⟨hbpos, fun h3b => ?_⟩, heq⟩
  have hmax : ¬ 3 ^ (k + 1) ∣ v := pow_succ_padicValNat_not_dvd (by omega)
  apply hmax
  obtain ⟨c, hc⟩ := h3b
  exact ⟨c, by rw [heq, hc, pow_succ]; ring⟩

/-- For `t > 0`, every element of `expand3 t` is not divisible by 3. -/
lemma expand3_not_dvd {t : ℕ} (ht : 0 < t) {x : ℕ} (hx : x ∈ expand3 t) :
    ¬ 3 ∣ x := by
  rw [mem_expand3 hx]
  exact (three_free_decomposition t ht).1.2

/-- For `t > 0`, every element of `expand3 t` is at most `t`. -/
lemma expand3_le_self {t : ℕ} (ht : 0 < t) {x : ℕ} (hx : x ∈ expand3 t) : x ≤ t := by
  rw [mem_expand3 hx]; exact Nat.div_le_self t _

/-- For `t > 0` with `3 ∣ t`, every element of `expand3 t` is at most `t / 3`. -/
lemma expand3_le_third {t : ℕ} (ht : 0 < t) (h3 : 3 ∣ t) {x : ℕ} (hx : x ∈ expand3 t) :
    x ≤ t / 3 := by
  rw [mem_expand3 hx]
  have h1 : 1 ≤ padicValNat 3 t := one_le_padicValNat_of_dvd ht.ne' h3
  have h2 : 3 ≤ 3 ^ padicValNat 3 t :=
    (pow_one 3).symm.trans_le (Nat.pow_le_pow_right (by norm_num) h1)
  exact Nat.div_le_div_left h2 (by norm_num)

/-- The sum of `Γraw p.parts` equals `n - 1` for `p ∈ C₃ n` with `n > 0`. -/
lemma Γraw_sum {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) (hp : p ∈ C₃ n) :
    (Γraw p.parts).sum = n - 1 := by
  obtain ⟨hne, J, hJ, hM, _⟩ := hp
  set M := largestPart p.parts
  have hM_ge : 3 ≤ M := by rw [hM]; omega
  have hM_mem : M ∈ p.parts := largestPart_mem hne
  show ((M - 1) ::ₘ ((p.parts.erase M).bind expand3)).sum = n - 1
  rw [Multiset.sum_cons, Multiset.sum_bind]
  rw [show Multiset.map (fun t => (expand3 t).sum) (p.parts.erase M) = p.parts.erase M from by
    conv_rhs => rw [← Multiset.map_id (p.parts.erase M)]
    exact Multiset.map_congr rfl (fun t _ => expand3_sum t)]
  have herase : (p.parts.erase M).sum + M = n := by
    have := Multiset.sum_cons M (p.parts.erase M)
    rw [Multiset.cons_erase hM_mem] at this
    linarith [p.parts_sum]
  omega

/-- Every element of `Γraw p.parts` is positive, for `p ∈ C₃ n` with `n > 0`. -/
lemma Γraw_pos {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) (hp : p ∈ C₃ n) :
    ∀ x ∈ Γraw p.parts, 0 < x := by
  obtain ⟨_, J, hJ, hM, _⟩ := hp
  intro x hx
  rw [Γraw, Multiset.mem_cons] at hx
  rcases hx with rfl | hx
  · rw [hM]; omega
  · obtain ⟨t, ht_in, ht⟩ := Multiset.mem_bind.mp hx
    exact expand3_pos (p.parts_pos (Multiset.mem_of_mem_erase ht_in)) ht

/-- No element of `Γraw p.parts` is divisible by 3. -/
lemma Γraw_not_dvd {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) (hp : p ∈ C₃ n) :
    ∀ x ∈ Γraw p.parts, ¬ 3 ∣ x := by
  intro x hx
  obtain ⟨_, J, hJ, hM, _⟩ := hp
  rw [Γraw, Multiset.mem_cons] at hx
  rcases hx with rfl | hxbind
  · rw [hM]; intro hdvd; omega
  · obtain ⟨t, htmem, hxt⟩ := Multiset.mem_bind.mp hxbind
    exact expand3_not_dvd (p.parts_pos (Multiset.mem_of_mem_erase htmem)) hxt

/-- All parts of a partition of `n` are positive (≥ 1). -/
lemma parts_pos {n : ℕ} (p : Nat.Partition n) (v : ℕ) (hv : v ∈ p.parts) : 1 ≤ v :=
  p.parts_pos hv

/-- The largest part of `Γraw p.parts` is `largestPart p.parts - 1`. -/
lemma Γraw_largestPart {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) (hp : p ∈ C₃ n) :
    largestPart (Γraw p.parts) = largestPart p.parts - 1 := by
  obtain ⟨_, J, hJ1, hLM, _⟩ := hp
  set M := largestPart p.parts
  refine largestPart_eq (Multiset.mem_cons_self _ _) fun x hx => ?_
  rw [show Γraw p.parts = (M - 1) ::ₘ ((p.parts.erase M).bind expand3) from rfl,
      Multiset.mem_cons] at hx
  rcases hx with hxM1 | hxbind
  · exact le_of_eq hxM1
  · obtain ⟨t, ht_mem, hx_exp⟩ := Multiset.mem_bind.mp hxbind
    have ht_in : t ∈ p.parts := Multiset.mem_of_mem_erase ht_mem
    have ht_pos : 0 < t := parts_pos p t ht_in
    have ht_le_M : t ≤ M := le_largestPart ht_in
    by_cases htM : t = M
    · have h3t : 3 ∣ t := by rw [htM, hLM]; exact ⟨J, rfl⟩
      have hxt : x ≤ t / 3 := expand3_le_third ht_pos h3t hx_exp
      have ht3 : t / 3 = J := by rw [htM, hLM]; omega
      omega
    · have hxt : x ≤ t := expand3_le_self ht_pos hx_exp
      omega

lemma Γraw_ne_zero (s : Multiset ℕ) : Γraw s ≠ 0 := fun h => by
  have hmem : (largestPart s - 1) ∈ Γraw s := by simp [Γraw, Multiset.mem_cons]
  rw [h] at hmem; simp at hmem

/-- Well-definedness of Γraw on `C₃ n`. -/
lemma Γraw_well_defined {n : ℕ} (hn : 0 < n)
    (p : Nat.Partition n) (hp : p ∈ C₃ n) :
    ∃ q : Nat.Partition (n - 1), q.parts = Γraw p.parts ∧ q ∈ B₃₂ (n - 1) ∧
      ∀ J : ℕ, 1 ≤ J → largestPart p.parts = 3 * J → q ∈ B₃₂J (n - 1) J := by
  obtain ⟨hpne, J₀, hJ₀, hMJ₀, hcount⟩ := hp
  have hp' : p ∈ C₃ n := ⟨hpne, J₀, hJ₀, hMJ₀, hcount⟩
  have hpos := Γraw_pos hn p hp'
  have hndvd := Γraw_not_dvd hn p hp'
  have hlp := Γraw_largestPart hn p hp'
  have hne : Γraw p.parts ≠ 0 := Γraw_ne_zero p.parts
  refine ⟨⟨Γraw p.parts, fun {i} hi => hpos i hi, Γraw_sum hn p hp'⟩, rfl,
          ⟨hne, hndvd, by rw [hlp, hMJ₀]; omega⟩, fun J hJ hMJ =>
          ⟨⟨hne, hndvd, by rw [hlp, hMJ]; omega⟩, by rw [hlp, hMJ]⟩⟩

/-- Wrapper of `Γraw_well_defined` matching the shape required by `problem.lean`. -/
lemma intermediate_lemma (thm1 : Thm1) {n : ℕ} (hn : 0 < n) :
    ∀ p : Nat.Partition n, p ∈ C₃ n →
      ∃ q : Nat.Partition (n - 1), q.parts = Γraw p.parts ∧ q ∈ B₃₂ (n - 1) ∧
        ∀ J : ℕ, 1 ≤ J → largestPart p.parts = 3 * J → q ∈ B₃₂J (n - 1) J :=
  fun p hp => Γraw_well_defined hn p hp

/-- The forward map ΓJ on `C₃,J(n)`, obtained from `intermediate_lemma`. -/
noncomputable def buildΓJ (thm1 : Thm1) {n : ℕ} (hn : 0 < n) (J : ℕ) (hJ : 1 ≤ J) :
    ↥(C₃J n J) → ↥(B₃₂J (n - 1) J) := fun p =>
  ⟨Classical.choose (intermediate_lemma thm1 hn p.1 p.2.1),
    (Classical.choose_spec (intermediate_lemma thm1 hn p.1 p.2.1)).2.2 J hJ p.2.2⟩

lemma buildΓJ_parts (thm1 : Thm1) {n : ℕ} (hn : 0 < n) (J : ℕ) (hJ : 1 ≤ J) :
    ∀ p : ↥(C₃J n J), (buildΓJ thm1 hn J hJ p).1.parts = Γraw p.1.parts := fun p =>
  (Classical.choose_spec (intermediate_lemma thm1 hn p.1 p.2.1)).1

/-- The forward map Γ on `C₃(n)`, obtained from `intermediate_lemma`. -/
noncomputable def buildΓ (thm1 : Thm1) {n : ℕ} (hn : 0 < n) :
    ↥(C₃ n) → ↥(B₃₂ (n - 1)) := fun p =>
  ⟨Classical.choose (intermediate_lemma thm1 hn p.1 p.2),
    (Classical.choose_spec (intermediate_lemma thm1 hn p.1 p.2)).2.1⟩

lemma buildΓ_parts (thm1 : Thm1) {n : ℕ} (hn : 0 < n) :
    ∀ p : ↥(C₃ n), (buildΓ thm1 hn p).1.parts = Γraw p.1.parts := fun p =>
  (Classical.choose_spec (intermediate_lemma thm1 hn p.1 p.2)).1

/-- For `p ∈ C₃J n J`, every part `v ∈ p.parts` satisfies `v ≤ 3*J`. -/
lemma parts_le_3J {n J : ℕ} (p : Nat.Partition n) (hp : p ∈ C₃J n J)
    (v : ℕ) (hv : v ∈ p.parts) : v ≤ 3 * J := by
  simpa [hp.2] using le_largestPart hv

/-- For `p ∈ C₃J n J`, the element `3*J` is in `p.parts`. -/
lemma largestPart_in_parts {n J : ℕ} (hJ : 1 ≤ J) (p : Nat.Partition n)
    (hp : p ∈ C₃J n J) : 3 * J ∈ p.parts := by
  simpa [hp.2] using largestPart_mem hp.1.1

/-- For any positive `v`, the count of `w` in `expand3 v` is
`3 ^ padicValNat 3 v` if `w = v / 3 ^ padicValNat 3 v`, else `0`. -/
lemma count_expand3 (v w : ℕ) :
    (expand3 v).count w =
      if w = v / 3 ^ padicValNat 3 v then 3 ^ padicValNat 3 v else 0 := by
  unfold expand3
  rw [Multiset.count_replicate]
  split_ifs with h₁ h₂ h₂ <;> first | rfl | exact absurd h₁.symm h₂ | exact absurd h₂.symm h₁

/-- For 3-free `b` and any `k`, `padicValNat 3 (b * 3 ^ k) = k`
and `(b * 3^k) / 3 ^ k = b`. -/
lemma padicValNat_three_free_mul_pow {b : ℕ} (hb : ThreeFree b) (k : ℕ) :
    padicValNat 3 (b * 3 ^ k) = k ∧ (b * 3 ^ k) / 3 ^ k = b := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbpos : 0 < b := hb.1
  have hpow : (0 : ℕ) < 3 ^ k := Nat.pos_of_neZero (3 ^ k)
  have h1 : padicValNat 3 b = 0 := padicValNat.eq_zero_of_not_dvd hb.2
  have h2 : padicValNat 3 (3 ^ k) = k := padicValNat.prime_pow k
  have h3 : padicValNat 3 (b * 3 ^ k) = padicValNat 3 b + padicValNat 3 (3 ^ k) :=
    padicValNat.mul hbpos.ne' hpow.ne'
  exact ⟨by rw [h3, h1, h2, Nat.zero_add], Nat.mul_div_cancel b hpow⟩

/-- For a 3-free `b`, given any positive `v`, `(expand3 v).count b` is
`3 ^ padicValNat 3 v` when `v / 3 ^ padicValNat 3 v = b`, else `0`. -/
lemma count_expand3_threefree (b v : ℕ) :
    (expand3 v).count b =
      if v / 3 ^ padicValNat 3 v = b then 3 ^ padicValNat 3 v else 0 := by
  unfold expand3
  rw [Multiset.count_replicate]

/-- The maximum exponent `K` such that `b * 3^K ≤ 3*J` exists for 3-free
`b` with `1 ≤ b ≤ 3*J`. -/
lemma exists_maxExp {b J : ℕ} (hb : 1 ≤ b) (hbJ : b ≤ 3 * J) :
    ∃ K : ℕ, b * 3 ^ K ≤ 3 * J ∧ ∀ K', b * 3 ^ K' ≤ 3 * J → K' ≤ K := by
  classical
  have hbnd : ∀ K', b * 3 ^ K' ≤ 3 * J → K' ≤ 3 * J := fun K' hK' => by
    have h1 : K' ≤ 3 ^ K' :=
      (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by norm_num) K')).le
    have h2 : 3 ^ K' ≤ b * 3 ^ K' := Nat.le_mul_of_pos_left _ hb
    omega
  refine ⟨Nat.findGreatest (fun K => b * 3 ^ K ≤ 3 * J) (3 * J), ?_, fun K' hK' =>
    Nat.le_findGreatest (hbnd K' hK') hK'⟩
  exact Nat.findGreatest_spec (P := fun K => b * 3 ^ K ≤ 3 * J) (Nat.zero_le _) (by simpa using hbJ)

/-- For 3-free positive `b`, positive `v ≤ 3*J`, and `K` with
`b * 3^(K+1) > 3*J`, if `v = b * 3^k` for some `k`, then `k ≤ K`. -/
lemma k_le_K_of_v_eq {b J K v k : ℕ} (hb : ThreeFree b)
    (hbKsucc : b * 3 ^ (K + 1) > 3 * J) (hvJ : v ≤ 3 * J)
    (h : v = b * 3 ^ k) : k ≤ K := by
  have h2 : b * 3 ^ k < b * 3 ^ (K + 1) := lt_of_le_of_lt (h ▸ hvJ) hbKsucc
  have h3 : 3 ^ k < 3 ^ (K + 1) := Nat.lt_of_mul_lt_mul_left h2
  exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide)).mp h3)

/-- For a 3-free `b`, any positive `v ≤ 3*J`, and `K` with `b * 3^(K+1) > 3*J`,
the count of `b` in `expand3 v` is a sum of indicators. -/
lemma expand3_count_eq_indicator_sum {b J K v : ℕ} (hb : ThreeFree b)
    (hbKsucc : b * 3 ^ (K + 1) > 3 * J) (hv : 1 ≤ v) (hvJ : v ≤ 3 * J) :
    (expand3 v).count b =
      ∑ k ∈ Finset.range (K + 1), (if v = b * 3 ^ k then 3 ^ k else 0) := by
  rw [count_expand3_threefree b v]
  set k₀ := padicValNat 3 v with hk₀
  by_cases hdiv : v / 3 ^ k₀ = b
  · rw [if_pos hdiv]
    have hveq : v = b * 3 ^ k₀ := by rw [← hdiv, Nat.div_mul_cancel pow_padicValNat_dvd]
    have hk₀le : k₀ ≤ K := k_le_K_of_v_eq hb hbKsucc hvJ hveq
    have hk₀mem : k₀ ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk₀le)
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hveq]
    · intro k _ hne
      rw [if_neg]
      intro heq
      have : b * 3 ^ k = b * 3 ^ k₀ := heq ▸ hveq
      exact hne (Nat.pow_right_injective (by norm_num)
        (Nat.eq_of_mul_eq_mul_left hb.1 this))
    · exact fun h => absurd hk₀mem h
  · rw [if_neg hdiv]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro heq
    have hpval := padicValNat_three_free_mul_pow hb k
    have hk₀_eq : k₀ = k := by rw [hk₀, heq, hpval.1]
    exact hdiv (by rw [hk₀_eq, heq]; exact hpval.2)

/-- For a multiset `t` and natural numbers `a, c`:
`(t.map (fun v => if v = a then c else 0)).sum = t.count a * c`. -/
lemma multiset_sum_map_ite_eq (t : Multiset ℕ) (a c : ℕ) :
    (t.map (fun v => if v = a then c else 0)).sum = t.count a * c := by
  induction t using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons, add_mul]
    by_cases h : b = a
    · simp [h, add_comm]
    · have h' : a ≠ b := fun e => h e.symm
      simp [h, h']

lemma multiset_sum_map_finset_sum (t : Multiset ℕ) (N : ℕ) (g : ℕ → ℕ → ℕ) :
    (t.map (fun v => ∑ k ∈ Finset.range N, g v k)).sum =
      ∑ k ∈ Finset.range N, (t.map (fun v => g v k)).sum := by
  classical
  induction' t using Multiset.induction with a t ih
  · simp
  · simp [ih, Finset.sum_add_distrib]

/-- Main theorem: count of a 3-free `b` in `(s.erase M).bind expand3` equals the
sum over `k` of `(s.erase M).count (b * 3^k) * 3^k`. -/
lemma count_bind_expand3_sum {s : Multiset ℕ} {b J K M : ℕ} (hb : ThreeFree b)
    (hbK : b * 3 ^ K ≤ 3 * J) (hbKsucc : b * 3 ^ (K + 1) > 3 * J)
    (hs : ∀ v ∈ s, v ≤ 3 * J) (hpos : ∀ v ∈ s, 1 ≤ v) :
    ((s.erase M).bind expand3).count b =
      ∑ k ∈ Finset.range (K + 1), (s.erase M).count (b * 3 ^ k) * 3 ^ k := by
  set t := s.erase M with ht_def
  have ht_bound : ∀ v ∈ t, v ≤ 3 * J :=
    fun v hv => hs v (Multiset.mem_of_mem_erase hv)
  have ht_pos : ∀ v ∈ t, 1 ≤ v :=
    fun v hv => hpos v (Multiset.mem_of_mem_erase hv)
  rw [Multiset.count_bind]
  have h_map_eq : (t.map (fun v => (expand3 v).count b)) =
      t.map (fun v => ∑ k ∈ Finset.range (K + 1), (if v = b * 3 ^ k then 3 ^ k else 0)) :=
    Multiset.map_congr rfl fun v hv =>
      expand3_count_eq_indicator_sum hb hbKsucc (ht_pos v hv) (ht_bound v hv)
  rw [h_map_eq, multiset_sum_map_finset_sum]
  exact Finset.sum_congr rfl fun k _ => multiset_sum_map_ite_eq t (b * 3 ^ k) (3 ^ k)

/-- The count of any `v` in `s.erase M` adjusts by one at `v = M`. -/
lemma count_erase_eq {s : Multiset ℕ} {M v : ℕ} (hM : M ∈ s) :
    (s.erase M).count v = s.count v - if v = M then 1 else 0 := by
  by_cases h : v = M
  · subst h; simp [Multiset.count_erase_self]
  · simp [Multiset.count_erase_of_ne h, h]

/-- After cancellation of matching low-order terms, the suffix sums starting at `k`
are equal. -/
lemma suffix_eq_of_prefix_eq {K : ℕ} {c d : ℕ → ℕ}
    (heq : ∑ k ∈ Finset.range (K + 1), c k * 3 ^ k =
           ∑ k ∈ Finset.range (K + 1), d k * 3 ^ k)
    (k : ℕ) (hk : k ≤ K + 1) (hpre : ∀ j < k, c j = d j) :
    ∑ i ∈ Finset.Ico k (K + 1), c i * 3 ^ i =
    ∑ i ∈ Finset.Ico k (K + 1), d i * 3 ^ i := by
  have hsplit : Finset.range (K + 1) = Finset.range k ∪ Finset.Ico k (K + 1) := by
    ext i; simp [Finset.mem_range, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range k) (Finset.Ico k (K + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb; simp [Finset.mem_range, Finset.mem_Ico] at ha hb; omega
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj] at heq
  have hpref : ∑ i ∈ Finset.range k, c i * 3 ^ i =
               ∑ i ∈ Finset.range k, d i * 3 ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hpre i (Finset.mem_range.mp hi)]
  omega

/-- If two suffix sums starting at position `k` of the form `∑ c i * 3^i` are equal,
then `(c k * 3^k) % 3^(k+1) = (d k * 3^k) % 3^(k+1)`. -/
lemma suffix_mod_three_pow {K : ℕ} {c d : ℕ → ℕ} {k : ℕ} (hk : k < K + 1)
    (hsuf : ∑ i ∈ Finset.Ico k (K + 1), c i * 3 ^ i =
            ∑ i ∈ Finset.Ico k (K + 1), d i * 3 ^ i) :
    (c k * 3 ^ k) % 3 ^ (k + 1) = (d k * 3 ^ k) % 3 ^ (k + 1) := by
  have htail_dvd : ∀ (f : ℕ → ℕ),
      3 ^ (k + 1) ∣ ∑ i ∈ Finset.Ico (k + 1) (K + 1), f i * 3 ^ i := fun f =>
    Finset.dvd_sum fun i hi => by
      rw [Finset.mem_Ico] at hi
      exact Dvd.intro_left (f i * 3 ^ (i - (k + 1)))
        (by rw [mul_assoc, ← pow_add]; congr 2; omega)
  have hsplit : ∀ (f : ℕ → ℕ), ∑ i ∈ Finset.Ico k (K + 1), f i * 3 ^ i =
      f k * 3 ^ k + ∑ i ∈ Finset.Ico (k + 1) (K + 1), f i * 3 ^ i := fun f => by
    rw [← Finset.sum_Ico_consecutive _ (Nat.le_succ k) hk]
    simp [Finset.sum_Ico_eq_sum_range]
  rw [hsplit c, hsplit d] at hsuf
  obtain ⟨a, ha⟩ := htail_dvd c
  obtain ⟨b, hb⟩ := htail_dvd d
  rw [ha, hb] at hsuf
  have := congrArg (· % 3 ^ (k + 1)) hsuf
  simp [Nat.add_mul_mod_self_left] at this
  exact this

/-- From `(a * 3^k) % 3^(k+1) = (b * 3^k) % 3^(k+1)`, we can deduce `a % 3 = b % 3`. -/
lemma digit_eq_of_mul_mod_eq {k : ℕ} {a b : ℕ}
    (heq : (a * 3 ^ k) % 3 ^ (k + 1) = (b * 3 ^ k) % 3 ^ (k + 1)) :
    a % 3 = b % 3 := by
  have h3k : (0 : ℕ) < 3 ^ k := pow_pos (by norm_num) k
  rw [show (3 : ℕ) ^ (k + 1) = 3 ^ k * 3 by rw [pow_succ]] at heq
  rw [Nat.mul_comm a, Nat.mul_comm b, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at heq
  exact Nat.eq_of_mul_eq_mul_left h3k heq

/-- Uniqueness of the mixed base-3 representation up to position `K`. -/
lemma mixed_base3_unique {K : ℕ} {c d : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ 2) (hd : ∀ k < K, d k ≤ 2)
    (heq : ∑ k ∈ Finset.range (K + 1), c k * 3 ^ k =
           ∑ k ∈ Finset.range (K + 1), d k * 3 ^ k) :
    ∀ k ≤ K, c k = d k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hpre : ∀ j < k, c j = d j := fun j hjk =>
      ih j hjk (le_trans hjk.le hk)
    have hsuf := suffix_eq_of_prefix_eq heq k (le_trans hk (Nat.le_succ K)) hpre
    rcases lt_or_eq_of_le hk with hkK | hkK
    · have hmod := digit_eq_of_mul_mod_eq (suffix_mod_three_pow (Nat.lt_succ_of_lt hkK) hsuf)
      have hc_le : c k ≤ 2 := hc k hkK
      have hd_le : d k ≤ 2 := hd k hkK
      omega
    · subst hkK; simpa using hsuf

/-- For `p ∈ C₃J n J`, 3-free `b ≤ 3*J`, and `k < K` (with `K` the max
exponent), `p.parts.count (b * 3^k) ≤ 2`. -/
lemma count_le_two_below_K {n J : ℕ} (p : Nat.Partition n) (hp : p ∈ C₃J n J)
    {b K : ℕ} (hb : ThreeFree b)
    (hbK : b * 3 ^ K ≤ 3 * J) (hbKsucc : b * 3 ^ (K + 1) > 3 * J)
    {k : ℕ} (hk : k < K) : p.parts.count (b * 3 ^ k) ≤ 2 := by
  obtain ⟨⟨_, J', hJ'pos, hLPJ', hcount⟩, hLP⟩ := hp
  have hJJ' : J' = J := by have : 3 * J' = 3 * J := hLPJ'.symm.trans hLP; omega
  rw [hJJ'] at hcount
  have hpow : 3 ^ (k + 1) ≤ 3 ^ K := Nat.pow_le_pow_right (by norm_num) hk
  have h3J : b * 3 ^ (k + 1) ≤ 3 * J := (Nat.mul_le_mul_left b hpow).trans hbK
  rw [show b * 3 ^ (k + 1) = 3 * (b * 3 ^ k) from by ring] at h3J
  exact hcount _ (by omega)

/-- For a 3-free `b` and any `e : ℕ`, `(expand3 (b * 3^e)).count b = 3 ^ e`. -/
lemma count_expand3_mul_pow {b : ℕ} (hb : 1 ≤ b) (hb3 : ¬ 3 ∣ b) (e : ℕ) :
    (expand3 (b * 3 ^ e)).count b = 3 ^ e := by
  obtain ⟨hpadic, hdiv⟩ := padicValNat_three_free_mul_pow (⟨hb, hb3⟩ : ThreeFree b) e
  rw [count_expand3, hpadic, hdiv]; simp

/-- "No collision" lemma. Suppose `S` is a multiset with `S.bind expand3 = r`
and that `r` contains no copies of a positive 3-free integer `b`. Then `S`
contains no part of the form `b * 3 ^ e` for any `e`. -/
lemma no_collision {b : ℕ} (hb : 1 ≤ b) (hb3 : ¬ 3 ∣ b)
    {S r : Multiset ℕ} (h_bind : S.bind expand3 = r) (h_no_b : r.count b = 0)
    (e : ℕ) : S.count (b * 3 ^ e) = 0 := by
  have hsum : (S.map (fun v => (expand3 v).count b)).sum = 0 := by
    rw [← Multiset.count_bind, h_bind]; exact h_no_b
  by_contra hpos
  have hmem : b * 3 ^ e ∈ S := Multiset.count_pos.mp (Nat.pos_of_ne_zero hpos)
  have hterm : (expand3 (b * 3 ^ e)).count b = 3 ^ e := count_expand3_mul_pow hb hb3 e
  have h3e_mem : 3 ^ e ∈ S.map (fun v => (expand3 v).count b) := by
    simpa [hterm] using Multiset.mem_map_of_mem (fun v => (expand3 v).count b) hmem
  exact absurd (Multiset.sum_eq_zero_iff.mp hsum _ h3e_mem) (pow_ne_zero _ (by norm_num))

/-- Helper: bound on a sum of indicator functions where the map `e ↦ b * 3^e` is injective. -/
lemma indicator_sum_le_two (b K : ℕ) (d : ℕ → ℕ) (hb : 1 ≤ b)
    (h_d_le : ∀ e < K, d e ≤ 2) (t : ℕ) :
    (∑ e ∈ Finset.range K, (if t = b * 3 ^ e then d e else 0)) ≤ 2 := by
  by_cases hex : ∃ e ∈ Finset.range K, t = b * 3 ^ e
  · obtain ⟨e₀, he₀mem, he₀eq⟩ := hex
    have he₀K : e₀ < K := Finset.mem_range.mp he₀mem
    have hsum : (∑ e ∈ Finset.range K, (if t = b * 3 ^ e then d e else 0)) = d e₀ := by
      rw [Finset.sum_eq_single e₀]
      · simp [he₀eq]
      · intro e he hne
        by_cases hcond : t = b * 3 ^ e
        · refine absurd ?_ hne
          have heq : b * 3 ^ e = b * 3 ^ e₀ := by rw [← hcond, he₀eq]
          exact Nat.pow_right_injective (by norm_num) (Nat.eq_of_mul_eq_mul_left hb heq)
        · simp [hcond]
      · exact fun h => absurd he₀mem h
    rw [hsum]; exact h_d_le e₀ he₀K
  · push_neg at hex
    have hzero : (∑ e ∈ Finset.range K, (if t = b * 3 ^ e then d e else 0)) = 0 :=
      Finset.sum_eq_zero fun e he => by simp [hex e he]
    omega

lemma expand3_threefree_mul_pow {b : ℕ} (hb : ThreeFree b) (e : ℕ) :
    expand3 (b * 3 ^ e) = Multiset.replicate (3 ^ e) b := by
  obtain ⟨hval, hdiv⟩ := padicValNat_three_free_mul_pow hb e
  simp [expand3, hval, hdiv]

lemma sum_replicate_eq_replicate_sum (b : ℕ) (K : ℕ) (f : ℕ → ℕ) :
    (∑ e ∈ Finset.range K, Multiset.replicate (f e) b) =
      Multiset.replicate (∑ e ∈ Finset.range K, f e) b := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, ← Multiset.replicate_add]

/-- Binding `expand3` on a single replicate `replicate n (b * 3 ^ e)` for
3-free `b` gives `replicate (n * 3 ^ e) b`. -/
lemma bind_replicate_threefree (b : ℕ) (hb : ThreeFree b) (n e : ℕ) :
    (Multiset.replicate n (b * 3 ^ e)).bind expand3 =
      Multiset.replicate (n * 3 ^ e) b := by
  induction n with
  | zero => simp [Multiset.replicate_zero, Multiset.zero_bind]
  | succ k ih =>
    rw [Multiset.replicate_succ, Multiset.cons_bind, ih,
        expand3_threefree_mul_pow hb, Nat.succ_mul, add_comm (k * 3 ^ e) (3 ^ e),
        Multiset.replicate_add]

lemma bind_finset_sum {α β : Type*} (s : Finset α) (g : α → Multiset ℕ)
    (f : ℕ → Multiset β) :
    (∑ e ∈ s, g e).bind f = ∑ e ∈ s, (g e).bind f := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.add_bind, ih]

/-- Core case of the main theorem: for `1 ≤ v ≤ 3*J`, the counts of `v`
in `p₁.parts` and `p₂.parts` are equal. -/
lemma counts_eq_of_bind_eq_core
    {n J : ℕ} (hn : 0 < n) (hJ : 1 ≤ J)
    (p₁ p₂ : Nat.Partition n) (h₁ : p₁ ∈ C₃J n J) (h₂ : p₂ ∈ C₃J n J)
    (heq : (p₁.parts.erase (3 * J)).bind expand3 =
           (p₂.parts.erase (3 * J)).bind expand3)
    {v : ℕ} (hpos : 1 ≤ v) (hle : v ≤ 3 * J) :
    p₁.parts.count v = p₂.parts.count v := by
  set k : ℕ := padicValNat 3 v
  set b : ℕ := v / 3 ^ k with hb_def
  obtain ⟨hb_tf, hv_eq⟩ := three_free_decomposition v hpos
  have hb_pos : 1 ≤ b := hb_tf.1
  have hb_le_3J : b ≤ 3 * J := by
    have hb_le_v : b ≤ v := by
      rw [hv_eq]; nlinarith [pow_pos (by norm_num : (0:ℕ) < 3) k]
    exact hb_le_v.trans hle
  obtain ⟨K, hbK, hbK_max⟩ := exists_maxExp hb_pos hb_le_3J
  have hbKsucc : b * 3 ^ (K + 1) > 3 * J := by
    by_contra hcontra
    push_neg at hcontra
    exact absurd (hbK_max (K + 1) hcontra) (by omega)
  have hk_le_K : k ≤ K := k_le_K_of_v_eq hb_tf hbKsucc hle hv_eq
  have hsum1 := count_bind_expand3_sum (s := p₁.parts) (b := b) (J := J) (K := K)
    (M := 3 * J) hb_tf hbK hbKsucc (fun x hx => parts_le_3J p₁ h₁ x hx)
    (fun x hx => parts_pos p₁ x hx)
  have hsum2 := count_bind_expand3_sum (s := p₂.parts) (b := b) (J := J) (K := K)
    (M := 3 * J) hb_tf hbK hbKsucc (fun x hx => parts_le_3J p₂ h₂ x hx)
    (fun x hx => parts_pos p₂ x hx)
  have hc_bound : ∀ (p : Nat.Partition n) (hp : p ∈ C₃J n J),
      ∀ i < K, (p.parts.erase (3 * J)).count (b * 3 ^ i) ≤ 2 := fun p hp i hi =>
    (Multiset.count_le_of_le _ (Multiset.erase_le _ _)).trans
      (count_le_two_below_K p hp hb_tf hbK hbKsucc hi)
  have hdigits_eq := mixed_base3_unique (hc_bound p₁ h₁) (hc_bound p₂ h₂)
    (by rw [← hsum1, ← hsum2, heq])
  have h_erased_eq : (p₁.parts.erase (3 * J)).count v = (p₂.parts.erase (3 * J)).count v := by
    have := hdigits_eq k hk_le_K
    rw [hv_eq]; exact this
  have h1 := count_erase_eq (s := p₁.parts) (M := 3 * J) (v := v) (largestPart_in_parts hJ p₁ h₁)
  have h2 := count_erase_eq (s := p₂.parts) (M := 3 * J) (v := v) (largestPart_in_parts hJ p₂ h₂)
  have hsub_eq : p₁.parts.count v - (if v = 3 * J then 1 else 0) =
                 p₂.parts.count v - (if v = 3 * J then 1 else 0) := by
    rw [← h1, ← h2]; exact h_erased_eq
  by_cases hvJ : v = 3 * J
  · have hc1_ge : 1 ≤ p₁.parts.count (3 * J) :=
      Multiset.one_le_count_iff_mem.mpr (largestPart_in_parts hJ p₁ h₁)
    have hc2_ge : 1 ≤ p₂.parts.count (3 * J) :=
      Multiset.one_le_count_iff_mem.mpr (largestPart_in_parts hJ p₂ h₂)
    subst hvJ; simp at hsub_eq; omega
  · simp [hvJ] at hsub_eq; exact hsub_eq

/-- Main reconstruction: from equality of `(p₁.parts.erase (3*J)).bind expand3`
with the analogous expression for `p₂`, we recover equality of all counts. -/
lemma counts_eq_of_bind_eq {n J : ℕ} (hn : 0 < n) (hJ : 1 ≤ J)
    (p₁ p₂ : Nat.Partition n) (h₁ : p₁ ∈ C₃J n J) (h₂ : p₂ ∈ C₃J n J)
    (heq : (p₁.parts.erase (3 * J)).bind expand3 =
           (p₂.parts.erase (3 * J)).bind expand3) (v : ℕ) :
    p₁.parts.count v = p₂.parts.count v := by
  rcases Nat.eq_zero_or_pos v with hv0 | hvpos
  · subst hv0
    have h1 : (0 : ℕ) ∉ p₁.parts := fun h => by have := parts_pos p₁ 0 h; omega
    have h2 : (0 : ℕ) ∉ p₂.parts := fun h => by have := parts_pos p₂ 0 h; omega
    rw [Multiset.count_eq_zero.mpr h1, Multiset.count_eq_zero.mpr h2]
  · by_cases hle : v ≤ 3 * J
    · exact counts_eq_of_bind_eq_core hn hJ p₁ p₂ h₁ h₂ heq hvpos hle
    · push_neg at hle
      have h1 : v ∉ p₁.parts := fun h => by have := parts_le_3J p₁ h₁ v h; omega
      have h2 : v ∉ p₂.parts := fun h => by have := parts_le_3J p₂ h₂ v h; omega
      rw [Multiset.count_eq_zero.mpr h1, Multiset.count_eq_zero.mpr h2]
/-- Injectivity of the forward Glaisher map on `C₃J n J`. -/
lemma Γraw_inj_on_C₃J {n J : ℕ} (hn : 0 < n) (hJ : 1 ≤ J)
    (p₁ p₂ : Nat.Partition n) (h₁ : p₁ ∈ C₃J n J) (h₂ : p₂ ∈ C₃J n J)
    (heq : Γraw p₁.parts = Γraw p₂.parts) : p₁ = p₂ := by
  have hM₁ : largestPart p₁.parts = 3 * J := h₁.2
  have hM₂ : largestPart p₂.parts = 3 * J := h₂.2
  have heq' : (p₁.parts.erase (3 * J)).bind expand3 =
              (p₂.parts.erase (3 * J)).bind expand3 := by
    have h1 : Γraw p₁.parts = (3 * J - 1) ::ₘ ((p₁.parts.erase (3 * J)).bind expand3) := by
      simp [Γraw, hM₁]
    have h2 : Γraw p₂.parts = (3 * J - 1) ::ₘ ((p₂.parts.erase (3 * J)).bind expand3) := by
      simp [Γraw, hM₂]
    rw [h1, h2] at heq
    exact (Multiset.cons_inj_right (3 * J - 1)).mp heq
  exact Nat.Partition.ext (Multiset.ext.mpr (counts_eq_of_bind_eq hn hJ p₁ p₂ h₁ h₂ heq'))
/-- Injectivity of the forward Glaisher map on `C₃ n`. -/
lemma Γraw_inj_on_C₃ {n : ℕ} (hn : 0 < n)
    (p₁ p₂ : Nat.Partition n) (h₁ : p₁ ∈ C₃ n) (h₂ : p₂ ∈ C₃ n)
    (heq : Γraw p₁.parts = Γraw p₂.parts) : p₁ = p₂ := by
  obtain ⟨hne₁, J₁, hJ₁, hM₁, hcount₁⟩ := h₁
  obtain ⟨hne₂, J₂, hJ₂, hM₂, hcount₂⟩ := h₂
  have hL₁ := Γraw_largestPart hn p₁ ⟨hne₁, J₁, hJ₁, hM₁, hcount₁⟩
  have hL₂ := Γraw_largestPart hn p₂ ⟨hne₂, J₂, hJ₂, hM₂, hcount₂⟩
  rw [hM₁] at hL₁
  rw [hM₂] at hL₂
  obtain rfl : J₁ = J₂ := by
    have : 3 * J₁ - 1 = 3 * J₂ - 1 := by rw [← hL₁, ← hL₂, heq]
    omega
  exact Γraw_inj_on_C₃J hn hJ₁ p₁ p₂
    ⟨⟨hne₁, J₁, hJ₁, hM₁, hcount₁⟩, hM₁⟩ ⟨⟨hne₂, J₁, hJ₂, hM₂, hcount₂⟩, hM₂⟩ heq

/-- The standard base-3 truncated decomposition:
`M = (M / 3^E) * 3^E + ∑ e ∈ Finset.range E, ((M / 3^e) % 3) * 3^e`. -/
lemma base3_truncated_decomp (M E : ℕ) :
    M = (M / 3 ^ E) * 3 ^ E +
        ∑ e ∈ Finset.range E, ((M / 3 ^ e) % 3) * 3 ^ e := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hdiv : M / 3 ^ E = (M / (3 ^ E * 3)) * 3 + (M / 3 ^ E) % 3 := by
      conv_lhs => rw [← Nat.div_add_mod (M / 3 ^ E) 3]
      rw [Nat.div_div_eq_div_mul]; ring
    have key : (M / 3 ^ E) * 3 ^ E =
        (M / (3 ^ E * 3)) * (3 ^ E * 3) + (M / 3 ^ E) % 3 * 3 ^ E := by
      calc (M / 3 ^ E) * 3 ^ E
          = ((M / (3 ^ E * 3)) * 3 + (M / 3 ^ E) % 3) * 3 ^ E := by rw [← hdiv]
        _ = (M / (3 ^ E * 3)) * (3 ^ E * 3) + (M / 3 ^ E) % 3 * 3 ^ E := by ring
    linarith [ih]

/-- Existence of a base-3 expansion of `M` relative to the top bucket exponent `E`. -/
lemma base3_decomp_exists (M E : ℕ) :
    ∃ Q : ℕ, ∃ d : ℕ → ℕ,
      (∀ e < E, d e ≤ 2) ∧
      M = Q * 3 ^ E + ∑ e ∈ Finset.range E, d e * 3 ^ e := by
  refine ⟨M / 3 ^ E, fun e => (M / 3 ^ e) % 3, ?_, base3_truncated_decomp M E⟩
  intro e _
  show (M / 3 ^ e) % 3 ≤ 2
  have : (M / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
  omega

/-- The sum of the "bucket" multiset
`Multiset.replicate Q (b * 3^K) + Σ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3^e)`
equals `b * (Q * 3^K + Σ e ∈ Finset.range K, d e * 3^e)`. -/
lemma bucketMS_sum (b K Q : ℕ) (d : ℕ → ℕ) :
    ((Multiset.replicate Q (b * 3 ^ K) +
      ∑ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3 ^ e))).sum
      = b * (Q * 3 ^ K + ∑ e ∈ Finset.range K, d e * 3 ^ e) := by
  rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_sum]
  simp_rw [Multiset.sum_replicate, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  ring_nf

/-- Every element of the bucket multiset has the form `b * 3^e` for some `e ≤ K`. -/
lemma bucketMS_mem (b K Q : ℕ) (d : ℕ → ℕ) {x : ℕ}
    (hx : x ∈ Multiset.replicate Q (b * 3 ^ K) +
      ∑ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3 ^ e)) :
    ∃ e, e ≤ K ∧ x = b * 3 ^ e := by
  rw [Multiset.mem_add] at hx
  rcases hx with h | h
  · exact ⟨K, le_refl K, (Multiset.mem_replicate.mp h).2⟩
  · obtain ⟨e, he, hxe⟩ := Multiset.mem_sum.mp h
    exact ⟨e, (Finset.mem_range.mp he).le, (Multiset.mem_replicate.mp hxe).2⟩

/-- For `t ≤ J < b * 3^K`, the count of `t` in the bucket multiset is at most 2. -/
lemma bucketMS_count_le_two (b J K Q : ℕ) (d : ℕ → ℕ) (hb : 1 ≤ b)
    (h_d_le : ∀ e < K, d e ≤ 2) (hKJ : J < b * 3 ^ K)
    {t : ℕ} (ht : t ≤ J) :
    (Multiset.replicate Q (b * 3 ^ K) +
      ∑ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3 ^ e)).count t ≤ 2 := by
  rw [Multiset.count_add]
  have h1 : (Multiset.replicate Q (b * 3 ^ K)).count t = 0 := by
    rw [Multiset.count_replicate]
    simp [Ne.symm (ne_of_lt (lt_of_le_of_lt ht hKJ))]
  rw [h1, zero_add]
  have h2 : (∑ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3 ^ e)).count t =
      ∑ e ∈ Finset.range K, (if t = b * 3 ^ e then d e else 0) := by
    induction (Finset.range K) using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, Multiset.count_add, ih,
          Multiset.count_replicate]
      congr 1
      by_cases h : t = b * 3 ^ a
      · simp [h]
      · simp [h, Ne.symm h]
  rw [h2]; exact indicator_sum_le_two b K d hb h_d_le t

/-- For 3-free `b`, binding `expand3` over the bucket multiset yields
`Multiset.replicate (Q * 3^K + Σ_{e<K} d e * 3^e) b`. -/
lemma bucketMS_bind_expand3 {b : ℕ} (hb : ThreeFree b) (K Q : ℕ) (d : ℕ → ℕ) :
    (Multiset.replicate Q (b * 3 ^ K) +
      ∑ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3 ^ e)).bind expand3 =
      Multiset.replicate (Q * 3 ^ K + ∑ e ∈ Finset.range K, d e * 3 ^ e) b := by
  rw [Multiset.add_bind, bind_replicate_threefree b hb Q K, bind_finset_sum]
  rw [show (∑ e ∈ Finset.range K, (Multiset.replicate (d e) (b * 3 ^ e)).bind expand3) =
        ∑ e ∈ Finset.range K, Multiset.replicate (d e * 3 ^ e) b from
      Finset.sum_congr rfl fun e _ => bind_replicate_threefree b hb (d e) e]
  rw [sum_replicate_eq_replicate_sum, ← Multiset.replicate_add]

/-- The main bucket-contribution lemma (target). -/
lemma bucket_contribution {J : ℕ} (hJ : 1 ≤ J) {b : ℕ} (hb : 1 ≤ b)
    (hb3 : ¬ 3 ∣ b) (hbJ : b ≤ 3 * J) (M : ℕ) :
    ∃ c : Multiset ℕ,
      c.sum = b * M ∧
      (∀ x ∈ c, ∃ e : ℕ, x = b * 3 ^ e ∧ x ≤ 3 * J) ∧
      (∀ t ≤ J, c.count t ≤ 2) ∧
      c.bind expand3 = Multiset.replicate M b := by
  obtain ⟨K, hK, hKmax⟩ := exists_maxExp hb hbJ
  have hb3free : ThreeFree b := ⟨hb, hb3⟩
  have hKsucc : 3 * J < b * 3 ^ (K + 1) := by
    by_contra h
    push_neg at h
    exact absurd (hKmax (K + 1) h) (by omega)
  have hKJ : J < b * 3 ^ K := by
    have hrw : b * 3 ^ (K + 1) = 3 * (b * 3 ^ K) := by ring
    rw [hrw] at hKsucc; omega
  obtain ⟨Q, d, hd_le, hMeq⟩ := base3_decomp_exists M K
  refine ⟨Multiset.replicate Q (b * 3 ^ K) +
            ∑ e ∈ Finset.range K, Multiset.replicate (d e) (b * 3 ^ e),
          by rw [bucketMS_sum, ← hMeq], ?_,
          fun t ht => bucketMS_count_le_two b J K Q d hb hd_le hKJ ht,
          by rw [bucketMS_bind_expand3 hb3free, ← hMeq]⟩
  intro x hx
  obtain ⟨e, heK, hxe⟩ := bucketMS_mem b K Q d hx
  refine ⟨e, hxe, ?_⟩
  rw [hxe]
  exact (Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by norm_num) heK)).trans hK

/-- `Multiset.replicate M b ≤ r` whenever `M ≤ r.count b`. -/
lemma replicate_le_of_count_le {α : Type*} [DecidableEq α] (M : ℕ) (b : α)
    (r : Multiset α) (h : M ≤ r.count b) :
    Multiset.replicate M b ≤ r := by
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_replicate]
  split_ifs with hab
  · subst hab; exact h
  · exact Nat.zero_le _

lemma combined_buckets_step {J : ℕ} (hJ : 1 ≤ J) (r : Multiset ℕ)
    (hr_pos : ∀ x ∈ r, 1 ≤ x)
    (hr_nd : ∀ x ∈ r, ¬ 3 ∣ x)
    (hr_le : ∀ x ∈ r, x ≤ 3 * J - 1)
    (hr_ne : r ≠ 0)
    (ih : ∀ r' : Multiset ℕ, r' < r →
       (∀ x ∈ r', 1 ≤ x) → (∀ x ∈ r', ¬ 3 ∣ x) → (∀ x ∈ r', x ≤ 3 * J - 1) →
       ∃ S' : Multiset ℕ,
         S'.sum = r'.sum ∧
         (∀ x ∈ S', 1 ≤ x ∧ x ≤ 3 * J) ∧
         (∀ t ≤ J, S'.count t ≤ 2) ∧
         S'.bind expand3 = r') :
    ∃ S : Multiset ℕ,
      S.sum = r.sum ∧
      (∀ x ∈ S, 1 ≤ x ∧ x ≤ 3 * J) ∧
      (∀ t ≤ J, S.count t ≤ 2) ∧
      S.bind expand3 = r := by
  -- Step 1: choose b ∈ r
  obtain ⟨b, hb_mem⟩ := Multiset.exists_mem_of_ne_zero hr_ne
  have hb_pos : 1 ≤ b := hr_pos b hb_mem
  have hb_nd : ¬ 3 ∣ b := hr_nd b hb_mem
  have hb_le_3J : b ≤ 3 * J := le_trans (hr_le b hb_mem) (Nat.sub_le _ _)
  set M : ℕ := r.count b with hM_def
  have hM_pos : 1 ≤ M := by rw [hM_def]; exact Multiset.one_le_count_iff_mem.mpr hb_mem
  have hrep_le : Multiset.replicate M b ≤ r :=
    replicate_le_of_count_le M b r (le_of_eq hM_def.symm)
  set r' : Multiset ℕ := r - Multiset.replicate M b with hr'_def
  have hsplit : r = Multiset.replicate M b + r' := by
    rw [hr'_def, add_comm]; exact (tsub_add_cancel_of_le hrep_le).symm
  have hr'_no_b : r'.count b = 0 := by
    rw [hr'_def, Multiset.count_sub, Multiset.count_replicate_self, ← hM_def]
    omega
  have hr'_lt : r' < r := by
    rw [hsplit]
    have hM_repl_ne : Multiset.replicate M b ≠ 0 := fun h => by
      have : (Multiset.replicate M b).card = 0 := by rw [h]; rfl
      rw [Multiset.card_replicate] at this; omega
    simpa [add_comm] using
      add_lt_add_of_le_of_lt (le_refl r') (pos_iff_ne_zero.mpr hM_repl_ne)
  have hr'_sub : r' ≤ r := Multiset.sub_le_self _ _
  have hr'_pos : ∀ x ∈ r', 1 ≤ x := fun x hx => hr_pos x (Multiset.mem_of_le hr'_sub hx)
  have hr'_nd : ∀ x ∈ r', ¬ 3 ∣ x := fun x hx => hr_nd x (Multiset.mem_of_le hr'_sub hx)
  have hr'_le : ∀ x ∈ r', x ≤ 3 * J - 1 := fun x hx => hr_le x (Multiset.mem_of_le hr'_sub hx)
  obtain ⟨S', hS'_sum, hS'_range, hS'_count, hS'_bind⟩ :=
    ih r' hr'_lt hr'_pos hr'_nd hr'_le
  obtain ⟨S_b, hSb_sum, hSb_form, hSb_count, hSb_bind⟩ :=
    bucket_contribution hJ hb_pos hb_nd hb_le_3J M
  refine ⟨S_b + S', ?_, ?_, ?_, ?_⟩
  · rw [Multiset.sum_add, hSb_sum, hS'_sum, hsplit, Multiset.sum_add,
        Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · obtain ⟨e, hxe, hxJ⟩ := hSb_form x hx
      refine ⟨?_, hxJ⟩
      rw [hxe]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hb_pos) (pow_ne_zero _ (by norm_num)))
    · exact hS'_range x hx
  · intro t htJ
    rw [Multiset.count_add]
    by_cases hex : ∃ e : ℕ, t = b * 3 ^ e
    · obtain ⟨e, hte⟩ := hex
      have hS'_t_zero : S'.count t = 0 := by
        rw [hte]; exact no_collision hb_pos hb_nd hS'_bind hr'_no_b e
      rw [hS'_t_zero]; simpa using hSb_count t htJ
    · have hSb_t_zero : S_b.count t = 0 := by
        by_contra h
        have : t ∈ S_b := Multiset.count_pos.mp (Nat.pos_of_ne_zero h)
        obtain ⟨e, hxe, _⟩ := hSb_form t this
        exact hex ⟨e, hxe⟩
      rw [hSb_t_zero, zero_add]; exact hS'_count t htJ
  · rw [Multiset.add_bind, hSb_bind, hS'_bind, hsplit]

/-- Combine bucket contributions for every distinct 3-free `b` appearing in `r`.
By strong induction on `r`, builds a multiset `S` such that `S.bind expand3 = r`. -/
lemma combined_buckets {J : ℕ} (hJ : 1 ≤ J)
    (r : Multiset ℕ)
    (hr_pos : ∀ x ∈ r, 1 ≤ x)
    (hr_nd : ∀ x ∈ r, ¬ 3 ∣ x)
    (hr_le : ∀ x ∈ r, x ≤ 3 * J - 1) :
    ∃ S : Multiset ℕ,
      S.sum = r.sum ∧
      (∀ x ∈ S, 1 ≤ x ∧ x ≤ 3 * J) ∧
      (∀ t ≤ J, S.count t ≤ 2) ∧
      S.bind expand3 = r := by
  induction r using Multiset.strongInductionOn with
  | _ r ih =>
    by_cases h_empty : r = 0
    · subst h_empty
      exact ⟨0, by simp, by intro x hx; simp at hx, by intro t _; simp, by simp⟩
    · exact combined_buckets_step hJ r hr_pos hr_nd hr_le h_empty ih

lemma exists_inverse_multiset {n J : ℕ} (hn : 0 < n) (hJ : 1 ≤ J)
    (q : Nat.Partition (n - 1)) (hq : q ∈ B₃₂J (n - 1) J) :
    ∃ s : Multiset ℕ,
      s.sum = n ∧
      (∀ {x}, x ∈ s → 0 < x) ∧
      largestPart s = 3 * J ∧
      (∀ t ≤ J, s.count t ≤ 2) ∧
      Γraw s = q.parts := by
  obtain ⟨⟨hq_ne, hq_nd, _⟩, hq_lp⟩ := hq
  have h_max_mem : largestPart q.parts ∈ q.parts := largestPart_mem hq_ne
  have h_max_le : ∀ x ∈ q.parts, x ≤ largestPart q.parts := fun x hx => le_largestPart hx
  rw [hq_lp] at h_max_mem h_max_le
  set r : Multiset ℕ := q.parts.erase (3 * J - 1) with hr_def
  have hr_pos : ∀ x ∈ r, 1 ≤ x := fun x hx => parts_pos q x (Multiset.mem_of_mem_erase hx)
  have hr_nd : ∀ x ∈ r, ¬ 3 ∣ x := fun x hx => hq_nd x (Multiset.mem_of_mem_erase hx)
  have hr_le : ∀ x ∈ r, x ≤ 3 * J - 1 := fun x hx => h_max_le x (Multiset.mem_of_mem_erase hx)
  have hr_sum : r.sum + (3 * J - 1) = n - 1 := by
    have := Multiset.sum_cons (3 * J - 1) r
    rw [hr_def, Multiset.cons_erase h_max_mem] at this
    linarith [q.parts_sum]
  obtain ⟨S, hS_sum, hS_bnd, hS_count, hS_bind⟩ :=
    combined_buckets hJ r hr_pos hr_nd hr_le
  have hlp : largestPart ((3 * J : ℕ) ::ₘ S) = 3 * J := by
    refine largestPart_eq (Multiset.mem_cons_self _ _) fun x hx => ?_
    rcases Multiset.mem_cons.mp hx with heq | hmem
    · exact le_of_eq heq
    · exact (hS_bnd x hmem).2
  refine ⟨(3 * J) ::ₘ S, ?_, ?_, hlp, ?_, ?_⟩
  · rw [Multiset.sum_cons, hS_sum]; omega
  · intro x hx
    rcases Multiset.mem_cons.mp hx with heq | hmem
    · subst heq; omega
    · exact lt_of_lt_of_le Nat.zero_lt_one (hS_bnd x hmem).1
  · intro t ht
    rw [Multiset.count_cons]
    split_ifs with h
    · omega
    · exact hS_count t ht
  · show Γraw ((3 * J : ℕ) ::ₘ S) = q.parts
    rw [Γraw, show largestPart ((3 * J : ℕ) ::ₘ S) = 3 * J from hlp,
        Multiset.erase_cons_head, hS_bind, hr_def, Multiset.cons_erase h_max_mem]

lemma exists_Γinv_J {n J : ℕ} (hn : 0 < n) (hJ : 1 ≤ J) :
    ∀ q : Nat.Partition (n - 1), q ∈ B₃₂J (n - 1) J →
      ∃ p : Nat.Partition n, p ∈ C₃J n J ∧ Γraw p.parts = q.parts := by
  intro q hq
  obtain ⟨s, hs_sum, hs_pos, hs_max, hs_mult, hs_Γraw⟩ :=
    exists_inverse_multiset hn hJ q hq
  have hs_ne : s ≠ 0 := fun hs => by rw [hs] at hs_max; simp [largestPart] at hs_max; omega
  exact ⟨⟨s, hs_pos, hs_sum⟩, ⟨⟨hs_ne, J, hJ, hs_max, hs_mult⟩, hs_max⟩, hs_Γraw⟩

/-- Surjectivity of the forward Glaisher map onto `B₃₂ (n-1)`. -/
lemma exists_Γinv {n : ℕ} (hn : 0 < n) :
    ∀ q : Nat.Partition (n - 1), q ∈ B₃₂ (n - 1) →
      ∃ p : Nat.Partition n, p ∈ C₃ n ∧ Γraw p.parts = q.parts := by
  intro q hq
  set L := largestPart q.parts
  set J := (L + 1) / 3
  have hL_mod : L % 3 = 2 := hq.2.2
  have hJ_ge : 1 ≤ J := by simp only [J]; omega
  have hL_eq : L = 3 * J - 1 := by simp only [J]; omega
  obtain ⟨p, hp_J, hp_eq⟩ := exists_Γinv_J hn hJ_ge q ⟨hq, hL_eq⟩
  exact ⟨p, hp_J.1, hp_eq⟩

theorem prop_gamma (thm1 : Thm1) {n : ℕ} (hn : 0 < n) :
    (∀ J : ℕ, 1 ≤ J → ∃ ΓJ : ↥(C₃J n J) → ↥(B₃₂J (n - 1) J),
        (∀ p : ↥(C₃J n J), (ΓJ p).1.parts = Γraw p.1.parts) ∧
        Function.Bijective ΓJ) ∧
    (∃ Γ : ↥(C₃ n) → ↥(B₃₂ (n - 1)),
        (∀ p : ↥(C₃ n), (Γ p).1.parts = Γraw p.1.parts) ∧
        Function.Bijective Γ) := by
  refine ⟨fun J hJ => ⟨buildΓJ thm1 hn J hJ, buildΓJ_parts thm1 hn J hJ, ?_, ?_⟩,
          buildΓ thm1 hn, buildΓ_parts thm1 hn, ?_, ?_⟩
  · intro p₁ p₂ heq
    refine Subtype.ext (Γraw_inj_on_C₃J (J := J) hn hJ p₁.1 p₂.1 p₁.2 p₂.2 ?_)
    rw [← buildΓJ_parts thm1 hn J hJ p₁, ← buildΓJ_parts thm1 hn J hJ p₂, heq]
  · intro q
    obtain ⟨p, hp, hpq⟩ := exists_Γinv_J (J := J) hn hJ q.1 q.2
    refine ⟨⟨p, hp⟩, Subtype.ext (Nat.Partition.ext ?_)⟩
    rw [buildΓJ_parts thm1 hn J hJ ⟨p, hp⟩]; exact hpq
  · intro p₁ p₂ heq
    refine Subtype.ext (Γraw_inj_on_C₃ hn p₁.1 p₂.1 p₁.2 p₂.2 ?_)
    rw [← buildΓ_parts thm1 hn p₁, ← buildΓ_parts thm1 hn p₂, heq]
  · intro q
    obtain ⟨p, hp, hpq⟩ := exists_Γinv hn q.1 q.2
    refine ⟨⟨p, hp⟩, Subtype.ext (Nat.Partition.ext ?_)⟩
    rw [buildΓ_parts thm1 hn ⟨p, hp⟩]; exact hpq

end PropGamma
