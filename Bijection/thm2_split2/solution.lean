import Mathlib

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

/-- The set `D_3(n)`. -/
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

/-! ### Helper lemmas. -/

lemma isPositive_erase_one (μ : Multiset ℕ) (h0 : (0 : ℕ) ∉ μ) :
    IsPositive (μ.erase 1) := by
  intro x hx
  rcases Nat.eq_zero_or_pos x with rfl | h
  · exact absurd (Multiset.mem_of_mem_erase hx) h0
  · exact h

lemma count_eq_zero_of_lt_smallestPart (η : Multiset ℕ) (v : ℕ) (h : v < smallestPart η) :
    η.count v = 0 := by
  by_contra hne
  have hmem : v ∈ η.toFinset :=
    Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))
  have h_nonempty : η.toFinset.Nonempty := ⟨v, hmem⟩
  rw [show smallestPart η = η.toFinset.min' h_nonempty by simp [smallestPart, h_nonempty]] at h
  exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr h)

lemma smallestPart_le (η : Multiset ℕ) (x : ℕ) (hx : x ∈ η) : smallestPart η ≤ x := by
  have hmem : x ∈ η.toFinset := by simpa using hx
  have h_nonempty : η.toFinset.Nonempty := ⟨x, hmem⟩
  rw [show smallestPart η = η.toFinset.min' h_nonempty by simp [smallestPart, h_nonempty]]
  exact Finset.min'_le _ _ hmem

/-- The multiset of elements of `η` that are `≤ smallestPart η` equals the multiset of
elements equal to `smallestPart η`. -/
lemma filter_le_smallestPart_eq_filter_eq (η : Multiset ℕ) :
    η.filter (fun v => v ≤ smallestPart η) = η.filter (fun v => v = smallestPart η) :=
  Multiset.filter_congr fun x hx =>
    ⟨fun hle => le_antisymm hle (smallestPart_le η x hx), le_of_eq⟩

/-- If `η.count (smallestPart η) = 3`, then `card (η.filter (· ≤ smallestPart η)) = 3`. -/
lemma card_filter_le_smallestPart_eq_three (η : Multiset ℕ)
    (h : η.count (smallestPart η) = 3) :
    Multiset.card (η.filter (fun v => v ≤ smallestPart η)) = 3 := by
  rw [filter_le_smallestPart_eq_filter_eq, Multiset.filter_eq', Multiset.card_replicate]
  exact h

/-- If the smallest part of `η` has count exactly 3, then `tau η + 3 = len η`. -/
lemma tau_add_three_eq_len_of_count_smallestPart_eq_three (η : Multiset ℕ)
    (h : η.count (smallestPart η) = 3) :
    tau η + 3 = len η := by
  have hpart : η.filter (fun v => smallestPart η < v)
                  + η.filter (fun v => ¬ smallestPart η < v) = η :=
    Multiset.filter_add_not (fun v => smallestPart η < v) η
  rw [show η.filter (fun v => ¬ smallestPart η < v)
        = η.filter (fun v => v ≤ smallestPart η) from
      Multiset.filter_congr (fun _ _ => ⟨not_lt.mp, not_lt.mpr⟩)] at hpart
  have hcard := congrArg Multiset.card hpart
  rw [Multiset.card_add, card_filter_le_smallestPart_eq_three η h] at hcard
  unfold tau len
  exact hcard

lemma L_eval_caseA_s1 (μ : Multiset ℕ) (h0 : (0 : ℕ) ∈ μ)
    (hs : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) = 1) :
    L μ = (μ - ({0, 0, 0} : Multiset ℕ)).erase 1 := by
  unfold L
  rw [if_pos h0, if_pos hs]

lemma erase_one_count_le_two (η : Multiset ℕ) (h : ∀ v, η.count v ≤ 2) :
    ∀ v, (η.erase 1).count v ≤ 2 := fun v =>
  le_trans (Multiset.count_le_of_le v (Multiset.erase_le 1 η)) (h v)/-- If `0 ∈ μ`, then `smallestPart μ = 0`. -/
lemma smallestPart_eq_zero_of_zero_mem (μ : Multiset ℕ) (h0 : (0 : ℕ) ∈ μ) :
    smallestPart μ = 0 := by
  have h1 : μ.toFinset.Nonempty := ⟨0, by simpa using h0⟩
  rw [show smallestPart μ = μ.toFinset.min' h1 by simp [smallestPart, h1]]
  exact Nat.le_zero.mp (Finset.min'_le _ _ (by simpa using h0))

lemma count_zero_sub_three_zeros (μ : Multiset ℕ) :
    (μ - ({0, 0, 0} : Multiset ℕ)).count 0 = μ.count 0 - 3 := by
  rw [Multiset.count_sub]; rfl

lemma count_pos_sub_three_zeros (μ : Multiset ℕ) (v : ℕ) (hv : 0 < v) :
    (μ - ({0, 0, 0} : Multiset ℕ)).count v = μ.count v := by
  rw [Multiset.count_sub,
      show ({0, 0, 0} : Multiset ℕ).count v = 0 by simp [Nat.pos_iff_ne_zero.mp hv]]
  omega
/-- The triple `{0,0,0}` is a submultiset of `μ` when `μ.count 0 ≥ 3`. -/
private lemma three_zeros_le (μ : Multiset ℕ) (h : 3 ≤ μ.count 0) :
    ({0, 0, 0} : Multiset ℕ) ≤ μ := by
  rw [Multiset.le_iff_count]
  intro a
  by_cases ha : a = 0
  · subst ha; simpa using h
  · simp [ha]

/-- The sum of `μ - {0,0,0}` equals `μ.sum` when `μ.count 0 ≥ 3`. -/
lemma sum_sub_three_zeros (μ : Multiset ℕ) (h : 3 ≤ μ.count 0) :
    (μ - ({0, 0, 0} : Multiset ℕ)).sum = μ.sum := by
  have h1 := Multiset.sum_add (μ - ({0, 0, 0} : Multiset ℕ)) ({0, 0, 0} : Multiset ℕ)
  rw [Multiset.sub_add_cancel (three_zeros_le μ h)] at h1
  have h2 : ({0, 0, 0} : Multiset ℕ).sum = 0 := by decide
  omega

/-- Card of `μ - {0,0,0}` equals `μ.card - 3` when `μ.count 0 ≥ 3`. -/
lemma card_sub_three_zeros (μ : Multiset ℕ) (h : 3 ≤ μ.count 0) :
    Multiset.card (μ - ({0, 0, 0} : Multiset ℕ)) = Multiset.card μ - 3 := by
  rw [Multiset.card_sub (three_zeros_le μ h)]
  rfl

lemma sub_three_zeros_isPositive (μ : Multiset ℕ) (h : μ.count 0 = 3) :
    IsPositive (μ - ({0, 0, 0} : Multiset ℕ)) := by
  intro x hx
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · have h1 : (μ - ({0, 0, 0} : Multiset ℕ)).count 0 = 0 := by
      rw [count_zero_sub_three_zeros]; omega
    have h2 : 0 < (μ - ({0, 0, 0} : Multiset ℕ)).count 0 := Multiset.count_pos.mpr hx
    omega
  · exact hpos

/-- The smallest part of a nonempty multiset is a member. -/
lemma smallestPart_mem (η : Multiset ℕ) (hne : η ≠ 0) :
    smallestPart η ∈ η := by
  have h : η.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hne
  rw [show smallestPart η = η.toFinset.min' h by simp [smallestPart, h],
      ← Multiset.mem_toFinset]
  exact Finset.min'_mem _ _

/-- `smallestPart η = b` when `b ∈ η` and `b` is a lower bound. -/
lemma smallestPart_eq_of_min (η : Multiset ℕ) (b : ℕ)
    (hmem : b ∈ η) (hmin : ∀ x ∈ η, b ≤ x) : smallestPart η = b := by
  have h_nonempty : η.toFinset.Nonempty := ⟨b, Multiset.mem_toFinset.mpr hmem⟩
  rw [show smallestPart η = η.toFinset.min' h_nonempty by simp [smallestPart, h_nonempty]]
  exact le_antisymm (Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hmem))
    (Finset.le_min' _ _ _ fun x hx => hmin x (Multiset.mem_toFinset.mp hx))

/-- The sum of `η.erase 1` equals `η.sum - 1` when `1 ∈ η`. -/
lemma sum_erase_one (μ : Multiset ℕ) (h : (1 : ℕ) ∈ μ) :
    (μ.erase 1).sum = μ.sum - 1 := by
  have h1 : μ.sum = 1 + (μ.erase 1).sum := by
    conv_lhs => rw [← Multiset.cons_erase h]
    simp
  omega

/-- **Case A, subcase s = 1.** When `0 ∈ μ` and the smallest part of `η := μ - {0,0,0}`
equals `1`, the partition `L μ = η.erase 1` lies in `R(n-1)`. -/
lemma L_mem_R_caseA_s1 (n : ℕ) (_hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∈ μ)
    (hs : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) = 1) :
    L μ ∈ R (n - 1) := by
  obtain ⟨⟨hsum, _, hcnt, hbnd⟩, htau⟩ := hμ
  have hsm : smallestPart μ = 0 := smallestPart_eq_zero_of_zero_mem μ h0
  rw [hsm] at hcnt hbnd
  set η : Multiset ℕ := μ - ({0, 0, 0} : Multiset ℕ) with hη_def
  have h3 : 3 ≤ μ.count 0 := by omega
  have hL : L μ = η.erase 1 := L_eval_caseA_s1 μ h0 hs
  have heta_sum : η.sum = n := by rw [hη_def, sum_sub_three_zeros μ h3]; exact hsum
  have htau_eq : tau μ + 3 = Multiset.card μ := by
    simpa [len] using tau_add_three_eq_len_of_count_smallestPart_eq_three μ (hsm ▸ hcnt)
  have heta_pos : IsPositive η := by rw [hη_def]; exact sub_three_zeros_isPositive μ hcnt
  have heta_count_zero : η.count 0 = 0 := by
    rw [hη_def, count_zero_sub_three_zeros μ, hcnt]
  have heta_count_le_two : ∀ v, η.count v ≤ 2 := by
    intro v
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [heta_count_zero]; omega
    · rw [hη_def, count_pos_sub_three_zeros μ v hv]; exact hbnd v hv
  have h_eta_ne : η ≠ 0 := by
    intro he; rw [he] at hs; simp [smallestPart] at hs
  have h1_mem : (1 : ℕ) ∈ η := hs ▸ smallestPart_mem η h_eta_ne
  have h0_notmem : (0 : ℕ) ∉ η := fun h0e => absurd (heta_pos 0 h0e) (lt_irrefl 0)
  have heta_card : Multiset.card η = Multiset.card μ - 3 := by
    rw [hη_def]; exact card_sub_three_zeros μ h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL, sum_erase_one η h1_mem, heta_sum]
  · rw [hL]; exact isPositive_erase_one η h0_notmem
  · rw [hL]; exact erase_one_count_le_two η heta_count_le_two
  · left
    rw [hL, len, Multiset.card_erase_of_mem h1_mem]
    have h_card_pos : 1 ≤ Multiset.card η := Multiset.card_pos.mpr h_eta_ne
    have h_card_eq : Multiset.card η = tau μ := by omega
    rw [h_card_eq, Nat.pred_eq_sub_one]
    omega

/-- For `μ ∈ D3(μ.sum)` with `0 ∈ μ`, `card (μ - {0,0,0}) = tau μ`. -/
lemma card_sub_three_zeros_eq_tau (μ : Multiset ℕ) (hμ : μ ∈ D3 (μ.sum)) (h0 : (0 : ℕ) ∈ μ) :
    Multiset.card (μ - ({0, 0, 0} : Multiset ℕ)) = tau μ := by
  have hsp : smallestPart μ = 0 := smallestPart_eq_zero_of_zero_mem μ h0
  have hc0 : μ.count 0 = 3 := by have h := hμ.2.2.1; rw [hsp] at h; exact h
  rw [card_sub_three_zeros μ hc0.ge]
  have hsplit : Multiset.card μ = μ.count 0 + Multiset.card (μ.filter (fun v => 0 < v)) := by
    rw [Multiset.count_eq_card_filter_eq, add_comm]
    conv_lhs => rw [← Multiset.filter_add_not (fun v => 0 < v) μ]
    rw [Multiset.card_add]
    congr 1
    apply congrArg
    exact Multiset.filter_congr (fun v _ => by omega)
  have htau : tau μ = Multiset.card (μ.filter (fun v => 0 < v)) :=
    congrArg _ (Multiset.filter_congr (fun v _ => by rw [hsp]))
  rw [hsplit, hc0, htau]; omega

/-- The smallest part of `μ - {0,0,0}` is at least 1 when `μ.count 0 = 3`. -/
lemma smallestPart_sub_three_zeros_ge_one (μ : Multiset ℕ)
    (h : μ.count 0 = 3) (hne : (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 0) :
    1 ≤ smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) := by
  have h0_notmem : (0 : ℕ) ∉ (μ - ({0, 0, 0} : Multiset ℕ)) := by
    rw [← Multiset.count_pos, count_zero_sub_three_zeros]; omega
  have hnE : (μ - ({0, 0, 0} : Multiset ℕ)).toFinset.Nonempty :=
    Multiset.toFinset_nonempty.mpr hne
  unfold smallestPart
  rw [dif_pos hnE]
  apply Finset.le_min'
  intro x hx
  rw [Multiset.mem_toFinset] at hx
  by_contra hlt
  push_neg at hlt
  interval_cases x
  exact h0_notmem hx
/-- Sum of `η.erase s + {s - 1}` equals `η.sum - 1` when `s ∈ η` and `1 ≤ s`. -/
lemma sum_erase_add_singleton_sub_one (η : Multiset ℕ) (s : ℕ)
    (hmem : s ∈ η) (hs : 1 ≤ s) :
    ((η.erase s) + ({s - 1} : Multiset ℕ)).sum = η.sum - 1 := by
  rw [Multiset.sum_add, show ({s - 1} : Multiset ℕ).sum = s - 1 from rfl]
  have := Multiset.sum_erase hmem
  omega

/-- Cardinality of `η.erase s + {s - 1}` equals `η.card` when `s ∈ η`. -/
lemma card_erase_add_singleton (η : Multiset ℕ) (s : ℕ) (hmem : s ∈ η) :
    Multiset.card ((η.erase s) + ({s - 1} : Multiset ℕ)) = Multiset.card η := by
  rw [Multiset.card_add, Multiset.card_singleton, Multiset.card_erase_of_mem hmem,
      Nat.pred_eq_sub_one]
  have hpos : 0 < Multiset.card η :=
    Multiset.card_pos.mpr fun h => by rw [h] at hmem; exact Multiset.notMem_zero s hmem
  omega

/-- `IsPositive` of `η.erase s + {s - 1}` when η is positive and `s ≥ 2`. -/
lemma isPositive_erase_add_singleton (η : Multiset ℕ) (s : ℕ)
    (hη : IsPositive η) (hs : 2 ≤ s) :
    IsPositive ((η.erase s) + ({s - 1} : Multiset ℕ)) := by
  intro x hx
  rcases Multiset.mem_add.mp hx with h | h
  · exact hη x (Multiset.mem_of_mem_erase h)
  · rw [Multiset.mem_singleton.mp h]; omega

/-- Count of `s` in `η.erase s + {s - 1}` is `η.count s - 1` when `s ≥ 1`. -/
lemma count_self_erase_add_singleton (η : Multiset ℕ) (s : ℕ) (hs : 1 ≤ s) :
    ((η.erase s) + ({s - 1} : Multiset ℕ)).count s = η.count s - 1 := by
  rw [Multiset.count_add, Multiset.count_erase_self, Multiset.count_singleton,
      if_neg (by omega : ¬ s = s - 1), Nat.add_zero]

/-- Count of `s - 1` in `η.erase s + {s - 1}` is `1` when `s = smallestPart η` and `s ≥ 1`. -/
lemma count_pred_erase_add_singleton (η : Multiset ℕ) (s : ℕ) (hs : 1 ≤ s)
    (hsp : s = smallestPart η) :
    ((η.erase s) + ({s - 1} : Multiset ℕ)).count (s - 1) = 1 := by
  have hlt : s - 1 < s := Nat.sub_lt (by omega) (by norm_num)
  rw [Multiset.count_add, Multiset.count_singleton_self,
      Multiset.count_erase_of_ne (Nat.ne_of_lt hlt),
      count_eq_zero_of_lt_smallestPart η _ (hsp ▸ hlt)]

/-- Count of `v ∉ {s, s - 1}` in `η.erase s + {s - 1}` equals `η.count v`. -/
lemma count_other_erase_add_singleton (η : Multiset ℕ) (s v : ℕ)
    (hv1 : v ≠ s) (hv2 : v ≠ s - 1) :
    ((η.erase s) + ({s - 1} : Multiset ℕ)).count v = η.count v := by
  rw [Multiset.count_add, Multiset.count_erase_of_ne hv1, Multiset.count_singleton, if_neg hv2,
      Nat.add_zero]

/-- The multiset `η.erase s + {s - 1}` is nonzero. -/
lemma erase_add_singleton_ne_zero (η : Multiset ℕ) (s : ℕ) :
    (η.erase s) + ({s - 1} : Multiset ℕ) ≠ 0 := by
  intro h
  have hcard : Multiset.card ((η.erase s) + ({s - 1} : Multiset ℕ)) = 0 := by rw [h]; rfl
  rw [Multiset.card_add, Multiset.card_singleton] at hcard
  omega

/-- The smallest part of `η.erase s + {s - 1}` is `s - 1` when `s = smallestPart η ≥ 2`. -/
lemma smallestPart_erase_add_singleton (η : Multiset ℕ) (s : ℕ)
    (hs : 2 ≤ s) (hsp : s = smallestPart η) :
    smallestPart ((η.erase s) + ({s - 1} : Multiset ℕ)) = s - 1 := by
  set μ : Multiset ℕ := η.erase s + ({s - 1} : Multiset ℕ) with hμ
  have hne : μ ≠ 0 := erase_add_singleton_ne_zero η s
  have hnE : μ.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hne
  have hsm1_mem : s - 1 ∈ μ.toFinset := by
    rw [Multiset.mem_toFinset, hμ, Multiset.mem_add]; right; simp
  have hlb : ∀ x ∈ μ.toFinset, s - 1 ≤ x := by
    intro x hx
    rw [Multiset.mem_toFinset, hμ, Multiset.mem_add] at hx
    rcases hx with hxe | hxs
    · have : s ≤ x := hsp ▸ smallestPart_le η x (Multiset.mem_of_mem_erase hxe)
      omega
    · rw [Multiset.mem_singleton] at hxs; omega
  unfold smallestPart
  rw [dif_pos hnE]
  exact le_antisymm (Finset.min'_le _ _ hsm1_mem) (Finset.le_min' _ _ _ hlb)

/-- Unfolds `L μ` in case A, `s ≠ 1`. -/
lemma L_eq_caseA_sgt1 (μ : Multiset ℕ) (h0 : (0 : ℕ) ∈ μ)
    (hs : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 1) :
    L μ = ((μ - ({0, 0, 0} : Multiset ℕ)).erase
            (smallestPart (μ - ({0, 0, 0} : Multiset ℕ))))
          + ({smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) - 1} : Multiset ℕ) := by
  unfold L
  simp only [if_pos h0, if_neg hs]

/-- `μ - {0,0,0}` is nonempty when `μ ∈ D3_0 n` with `n ≥ 1` and `0 ∈ μ`. -/
lemma sub_three_zeros_ne_zero_of_caseA (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∈ μ) :
    (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 0 := by
  intro hsub
  have hμD3 : μ ∈ D3 n := hμ.1
  have hsp : smallestPart μ = 0 := smallestPart_eq_zero_of_zero_mem μ h0
  have hc0 : μ.count 0 = 3 := by have h := hμD3.2.2.1; rw [hsp] at h; exact h
  have hdecomp : (μ - ({0, 0, 0} : Multiset ℕ)) + ({0, 0, 0} : Multiset ℕ) = μ :=
    Multiset.sub_add_cancel (three_zeros_le μ hc0.ge)
  rw [hsub] at hdecomp
  have hμeq : μ = ({0, 0, 0} : Multiset ℕ) := by rw [← hdecomp]; simp
  have hsum : μ.sum = n := hμD3.1
  have : μ.sum = 0 := by rw [hμeq]; decide
  omega
/-- **Case A, subcase s > 1.** When `0 ∈ μ` and the smallest part of `η := μ - {0,0,0}`
is `> 1`, the partition `L μ = η.erase s + {s-1}` lies in `R(n-1)`. -/
lemma L_mem_R_caseA_sgt1 (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∈ μ)
    (hs : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 1) :
    L μ ∈ R (n - 1) := by
  obtain ⟨⟨hsum, hne, hcnt, hbnd⟩, htau⟩ := hμ
  have hsp0 : smallestPart μ = 0 := smallestPart_eq_zero_of_zero_mem μ h0
  rw [hsp0] at hcnt
  set η : Multiset ℕ := μ - ({0, 0, 0} : Multiset ℕ) with hη
  have hD3 : μ ∈ D3 n := ⟨hsum, hne, by rw [hsp0]; exact hcnt, fun v hv => hbnd v hv⟩
  have hηne : η ≠ 0 := sub_three_zeros_ne_zero_of_caseA n hn μ ⟨hD3, htau⟩ h0
  have hηpos : IsPositive η := sub_three_zeros_isPositive μ hcnt
  set s : ℕ := smallestPart η with hs_def
  have hs1 : 1 ≤ s := smallestPart_sub_three_zeros_ge_one μ hcnt hηne
  have hs2 : 2 ≤ s := by omega
  have hsmem : s ∈ η := smallestPart_mem η hηne
  have hηsum : η.sum = n := by rw [hη, sum_sub_three_zeros μ (by omega)]; exact hsum
  have hL : L μ = (η.erase s) + ({s - 1} : Multiset ℕ) := L_eq_caseA_sgt1 μ h0 hs
  rw [hL]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_erase_add_singleton_sub_one η s hsmem hs1, hηsum]
  · exact isPositive_erase_add_singleton η s hηpos hs2
  · intro v
    have hscnt : η.count s ≤ 2 := by
      rw [hη, count_pos_sub_three_zeros μ s (by omega)]
      exact hbnd s (by rw [hsp0]; omega)
    by_cases hv1 : v = s
    · rw [hv1, count_self_erase_add_singleton η s hs1]; omega
    by_cases hv2 : v = s - 1
    · rw [hv2, count_pred_erase_add_singleton η s hs1 hs_def]; omega
    · rw [count_other_erase_add_singleton η s v hv1 hv2]
      by_cases hv0 : v = 0
      · rw [hv0, hη, count_zero_sub_three_zeros]; omega
      · rw [hη, count_pos_sub_three_zeros μ v (by omega)]
        exact hbnd v (by rw [hsp0]; omega)
  · right
    refine ⟨?_, erase_add_singleton_ne_zero η s, ?_⟩
    · have hcardη : Multiset.card η = tau μ := by
        rw [hη]
        exact card_sub_three_zeros_eq_tau μ (by rw [hsum]; exact hD3) h0
      show len ((η.erase s) + ({s - 1} : Multiset ℕ)) % 3 = 0
      unfold len
      rw [card_erase_add_singleton η s hsmem, hcardη]
      exact htau
    · rw [smallestPart_erase_add_singleton η s hs2 hs_def]
      exact count_pred_erase_add_singleton η s hs1 hs_def

/-- For `μ ∈ D3 n`, `μ.card = 3 + tau μ`. -/
lemma card_eq_three_add_tau_caseB (μ : Multiset ℕ) (n : ℕ) (hμ : μ ∈ D3 n) :
    Multiset.card μ = 3 + tau μ := by
  have h := tau_add_three_eq_len_of_count_smallestPart_eq_three μ hμ.2.2.1
  unfold len at h
  omega

lemma L_caseB_s1_eq (μ : Multiset ℕ) (h0 : (0 : ℕ) ∉ μ) (hs : smallestPart μ = 1) :
    L μ = μ.erase 1 := by
  unfold L
  rw [if_neg h0, if_pos hs]

lemma count_one_of_caseB_s1 (n : ℕ) (μ : Multiset ℕ) (hμ : μ ∈ D3_0 n)
    (hs : smallestPart μ = 1) : μ.count 1 = 3 :=
  hs ▸ hμ.1.2.2.1

lemma mem_one_of_caseB_s1 (n : ℕ) (μ : Multiset ℕ) (hμ : μ ∈ D3_0 n)
    (hs : smallestPart μ = 1) : (1 : ℕ) ∈ μ :=
  Multiset.count_pos.mp (by rw [count_one_of_caseB_s1 n μ hμ hs]; omega)

lemma count_erase_one_le_two (μ : Multiset ℕ) (h0 : (0 : ℕ) ∉ μ)
    (hs : smallestPart μ = 1) (hc1 : μ.count 1 = 3)
    (hlarger : ∀ v, smallestPart μ < v → μ.count v ≤ 2) :
    ∀ v, (μ.erase 1).count v ≤ 2 := by
  intro v
  by_cases hv : v = 1
  · rw [hv, Multiset.count_erase_self, hc1]
  · rw [Multiset.count_erase_of_ne hv]
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · simp [Multiset.count_eq_zero.mpr h0]
    · have : smallestPart μ < v := by rw [hs]; omega
      exact hlarger v this

/-- `len (μ.erase 1) % 3 = 2` under Case B subcase s = 1 hypotheses. -/
lemma len_erase_one_mod_three (n : ℕ) (μ : Multiset ℕ) (hμD3 : μ ∈ D3 n)
    (_hs : smallestPart μ = 1) (hc1 : μ.count 1 = 3)
    (htau : tau μ % 3 = 0) :
    len (μ.erase 1) % 3 = 2 := by
  have h1mem : (1 : ℕ) ∈ μ := Multiset.count_pos.mp (by omega)
  have hcard : Multiset.card μ = 3 + tau μ := card_eq_three_add_tau_caseB μ n hμD3
  unfold len
  rw [Multiset.card_erase_of_mem h1mem, hcard, Nat.pred_eq_sub_one]
  omega

/-- **Case B, subcase s = 1.** When `0 ∉ μ` and `smallestPart μ = 1`,
`L μ = μ.erase 1` lies in `R(n-1)`. -/
lemma L_mem_R_caseB_s1 (n : ℕ) (_hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∉ μ)
    (hs : smallestPart μ = 1) :
    L μ ∈ R (n - 1) := by
  obtain ⟨⟨hsum, hne, hcnt, hlarger⟩, htau⟩ := hμ
  have hμD3 : μ ∈ D3 n := ⟨hsum, hne, hcnt, hlarger⟩
  have hc1 : μ.count 1 = 3 := count_one_of_caseB_s1 n μ ⟨hμD3, htau⟩ hs
  have h1mem : (1 : ℕ) ∈ μ := mem_one_of_caseB_s1 n μ ⟨hμD3, htau⟩ hs
  rw [L_caseB_s1_eq μ h0 hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_erase_one μ h1mem, hsum]
  · exact isPositive_erase_one μ h0
  · exact count_erase_one_le_two μ h0 hs hc1 hlarger
  · exact Or.inl (len_erase_one_mod_three n μ hμD3 hs hc1 htau)

/-- **Case B, subcase `s > 1`.** When `0 ∉ μ` and `smallestPart μ ≠ 1`,
the partition `L μ = μ.erase s + {s - 1}` lies in `R(n - 1)`. -/
lemma L_mem_R_caseB_sgt1 (n : ℕ) (_hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∉ μ)
    (hs : smallestPart μ ≠ 1) :
    L μ ∈ R (n - 1) := by
  obtain ⟨⟨hsum, hne, hcount, hbnd⟩, htau⟩ := hμ
  have hsmem : smallestPart μ ∈ μ := smallestPart_mem μ hne
  have hpos : IsPositive μ := fun x hx => by
    rcases Nat.eq_zero_or_pos x with rfl | hxp
    · exact absurd hx h0
    · exact hxp
  have hs1 : 1 ≤ smallestPart μ := hpos _ hsmem
  have hs2 : 2 ≤ smallestPart μ := by omega
  have hLeq : L μ = μ.erase (smallestPart μ) + ({smallestPart μ - 1} : Multiset ℕ) := by
    unfold L; simp [h0, hs]
  rw [hLeq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_erase_add_singleton_sub_one μ (smallestPart μ) hsmem hs1, hsum]
  · exact isPositive_erase_add_singleton μ (smallestPart μ) hpos hs2
  · intro v
    by_cases hv1 : v = smallestPart μ
    · rw [hv1, count_self_erase_add_singleton μ (smallestPart μ) hs1, hcount]
    by_cases hv2 : v = smallestPart μ - 1
    · rw [hv2, count_pred_erase_add_singleton μ (smallestPart μ) hs1 rfl]; omega
    · rw [count_other_erase_add_singleton μ (smallestPart μ) v hv1 hv2]
      by_cases hvs : smallestPart μ < v
      · exact hbnd v hvs
      · push_neg at hvs
        rw [count_eq_zero_of_lt_smallestPart μ v (lt_of_le_of_ne hvs hv1)]; omega
  · right
    refine ⟨?_, erase_add_singleton_ne_zero μ (smallestPart μ), ?_⟩
    · unfold len
      rw [card_erase_add_singleton μ (smallestPart μ) hsmem,
          card_eq_three_add_tau_caseB μ n ⟨hsum, hne, hcount, hbnd⟩]
      omega
    · rw [smallestPart_erase_add_singleton μ (smallestPart μ) hs2 rfl]
      exact count_pred_erase_add_singleton μ (smallestPart μ) hs1 rfl

/-- If `σ ∈ R N` and `len σ % 3 ≠ 2`, then `smallestPart σ ∈ σ`. -/
lemma smallestPart_mem_of_caseB (σ : Multiset ℕ) (N : ℕ)
    (hσ : σ ∈ R N)
    (h2 : len σ % 3 ≠ 2) :
    smallestPart σ ∈ σ := by
  obtain ⟨_, _, _, hdisj⟩ := hσ
  rcases hdisj with h | ⟨_, _, hcount⟩
  · exact absurd h h2
  · exact Multiset.count_pos.mp (by omega)

/-- **Sum of `T σ` equals `n`.** -/
lemma T_sum_eq (n : ℕ) (hn : 1 ≤ n) (σ : Multiset ℕ) (hσ : σ ∈ R (n - 1)) :
    (T σ).sum = n := by
  have hσsum : σ.sum = n - 1 := hσ.1
  have hη_sum : (if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
                else (σ.erase (smallestPart σ)) +
                  ({smallestPart σ + 1} : Multiset ℕ)).sum = n := by
    by_cases hlen : len σ % 3 = 2
    · simp [hlen, Multiset.sum_add, hσsum]; omega
    · simp only [hlen, if_false]
      have hsum_erase := Multiset.sum_erase (smallestPart_mem_of_caseB σ (n - 1) hσ hlen)
      rw [Multiset.sum_add]; simp; omega
  unfold T
  set η : Multiset ℕ :=
    if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
    else (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)
  show (if η.count (smallestPart η) = 3 then η else η + ({0, 0, 0} : Multiset ℕ)).sum = n
  split_ifs
  · exact hη_sum
  · rw [Multiset.sum_add]; simp [hη_sum]

/-- **`T σ` is nonzero.** -/
lemma T_ne_zero (n : ℕ) (_hn : 1 ≤ n) (σ : Multiset ℕ) (_hσ : σ ∈ R (n - 1)) :
    T σ ≠ 0 := by
  unfold T
  set η : Multiset ℕ :=
    if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
    else σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ) with hη
  show (if η.count (smallestPart η) = 3 then η else η + ({0, 0, 0} : Multiset ℕ)) ≠ 0
  have hη_ne : η ≠ 0 := by
    intro h
    have hcard : Multiset.card η = 0 := by rw [h]; rfl
    rw [hη] at hcard
    split_ifs at hcard <;> simp [Multiset.card_add] at hcard
  split_ifs with hc
  · exact hη_ne
  · intro h
    have : Multiset.card (η + ({0, 0, 0} : Multiset ℕ)) = 0 := by rw [h]; rfl
    simp [Multiset.card_add] at this

/-- The intermediate `η` from `T` is positive. -/
lemma T_eta_isPositive (N : ℕ) (σ : Multiset ℕ) (hσ : σ ∈ R N) :
    IsPositive
      (if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
       else (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)) := by
  have hpos : IsPositive σ := hσ.2.1
  split_ifs with h
  · intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact hpos x h
    · rw [Multiset.mem_singleton.mp h]; norm_num
  · intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact hpos x (Multiset.mem_of_mem_erase h)
    · rw [Multiset.mem_singleton.mp h]; omega

/-- **The smallest part of `T σ` occurs exactly three times.** -/
lemma T_count_smallest_eq_three (n : ℕ) (_hn : 1 ≤ n) (σ : Multiset ℕ)
    (hσ : σ ∈ R (n - 1)) :
    (T σ).count (smallestPart (T σ)) = 3 := by
  set η : Multiset ℕ :=
    (if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
     else (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)) with hη_def
  have hT : T σ = if η.count (smallestPart η) = 3 then η else η + ({0, 0, 0} : Multiset ℕ) := by
    simp [T, hη_def]
  by_cases hc : η.count (smallestPart η) = 3
  · rw [hT, if_pos hc]; exact hc
  · rw [hT, if_neg hc]
    have hpos : IsPositive η := T_eta_isPositive (n - 1) σ hσ
    have hzero_mem : (0 : ℕ) ∈ η + ({0, 0, 0} : Multiset ℕ) :=
      Multiset.mem_add.mpr (Or.inr (by decide))
    rw [smallestPart_eq_zero_of_zero_mem _ hzero_mem]
    have hcount_eta : η.count 0 = 0 :=
      Multiset.count_eq_zero.mpr fun h => (lt_irrefl 0) (hpos 0 h)
    rw [Multiset.count_add, hcount_eta]; decide

/-- `0 ∉ σ + {1}` when `σ` is positive. -/
lemma zero_not_mem_addOne_of_pos (σ : Multiset ℕ) (hpos : IsPositive σ) :
    (0 : ℕ) ∉ σ + ({1} : Multiset ℕ) := by
  intro h
  rcases Multiset.mem_add.mp h with h | h
  · exact (lt_irrefl 0) (hpos 0 h)
  · simp at h/-- If `σ` is positive, then `smallestPart (σ + {1}) = 1`. -/
lemma smallestPart_addOne_of_pos (σ : Multiset ℕ) (hpos : IsPositive σ) :
    smallestPart (σ + ({1} : Multiset ℕ)) = 1 := by
  set η := σ + ({1} : Multiset ℕ) with hη
  have h1mem : (1 : ℕ) ∈ η := by rw [hη]; simp
  have hne : η ≠ 0 := fun h => by rw [h] at h1mem; simp at h1mem
  have h0notmem : (0 : ℕ) ∉ η := zero_not_mem_addOne_of_pos σ hpos
  have hle : smallestPart η ≤ 1 := smallestPart_le η 1 h1mem
  rcases Nat.eq_zero_or_pos (smallestPart η) with hzero | _
  · exact absurd (hzero ▸ smallestPart_mem η hne) h0notmem
  · omega

/-- When `len σ % 3 = 2` and `σ.count 1 = 2`, `T σ = σ + {1}`. -/
lemma T_eq_addOne_of_count_eq_two (σ : Multiset ℕ) (hpos : IsPositive σ)
    (h2 : len σ % 3 = 2) (hc : Multiset.count 1 σ = 2) :
    T σ = σ + ({1} : Multiset ℕ) := by
  unfold T
  simp only [h2, if_true]
  rw [smallestPart_addOne_of_pos σ hpos,
      show (σ + ({1} : Multiset ℕ)).count 1 = 3 by rw [Multiset.count_add]; simp [hc]]
  simp

/-- When `len σ % 3 = 2` and `σ.count 1 < 2`, `T σ = σ + {1} + {0, 0, 0}`. -/
lemma T_eq_addOneZeros_of_count_lt_two (σ : Multiset ℕ) (hpos : IsPositive σ)
    (h2 : len σ % 3 = 2) (hc : Multiset.count 1 σ < 2) :
    T σ = σ + ({1} : Multiset ℕ) + ({0, 0, 0} : Multiset ℕ) := by
  unfold T
  simp only [h2, if_true]
  rw [smallestPart_addOne_of_pos σ hpos]
  have hcnt : (σ + ({1} : Multiset ℕ)).count 1 = σ.count 1 + 1 := by
    rw [Multiset.count_add]; simp
  rw [hcnt]
  simp [show σ.count 1 + 1 ≠ 3 by omega]

/- === Helper lemmas about `T`. === -/

/-- **Case A**: When `len σ % 3 = 2`, parts of `T σ` larger than its smallest part
occur at most twice. -/
lemma T_count_larger_le_two_caseA (σ : Multiset ℕ)
    (hpos : IsPositive σ) (hcnt : ∀ v, σ.count v ≤ 2)
    (hlen : len σ % 3 = 2) :
    ∀ v, smallestPart (T σ) < v → (T σ).count v ≤ 2 := by
  rcases Nat.lt_or_ge (σ.count 1) 2 with hlt | hge
  · have hTeq : T σ = σ + ({1} : Multiset ℕ) + ({0, 0, 0} : Multiset ℕ) :=
      T_eq_addOneZeros_of_count_lt_two σ hpos hlen hlt
    have hsp : smallestPart (T σ) = 0 :=
      smallestPart_eq_zero_of_zero_mem _ (by rw [hTeq]; simp [Multiset.mem_add])
    intro v hv
    rw [hsp] at hv
    rw [hTeq]
    simp only [Multiset.count_add, show ({0, 0, 0} : Multiset ℕ).count v = 0 by
      simp [Nat.pos_iff_ne_zero.mp hv]]
    by_cases hv1 : v = 1
    · subst hv1; simp; omega
    · simp [hv1]; simpa using hcnt v
  · have hcc : σ.count 1 = 2 := le_antisymm (hcnt 1) hge
    have hTeq : T σ = σ + ({1} : Multiset ℕ) := T_eq_addOne_of_count_eq_two σ hpos hlen hcc
    have hsp : smallestPart (T σ) = 1 := by rw [hTeq]; exact smallestPart_addOne_of_pos σ hpos
    intro v hv
    rw [hsp] at hv
    rw [hTeq, Multiset.count_add,
        show ({1} : Multiset ℕ).count v = 0 by simp [Nat.ne_of_gt hv]]
    simpa using hcnt v

/-- **Case B**: When `len σ % 3 = 0` and the smallest part of `σ` is unique,
parts of `T σ` larger than its smallest part occur at most twice. -/
lemma T_count_larger_le_two_caseB (σ : Multiset ℕ)
    (_hpos : IsPositive σ) (hcnt : ∀ v, σ.count v ≤ 2)
    (hlen : len σ % 3 = 0) (_hne : σ ≠ 0)
    (hunique : σ.count (smallestPart σ) = 1) :
    ∀ v, smallestPart (T σ) < v → (T σ).count v ≤ 2 := by
  set s := smallestPart σ
  set η : Multiset ℕ := σ.erase s + ({s + 1} : Multiset ℕ) with hη_def
  have hsη : smallestPart η = s + 1 := by
    have hs_plus_one_mem : s + 1 ∈ η := by rw [hη_def]; simp
    apply smallestPart_eq_of_min η (s + 1) hs_plus_one_mem
    intro x hx
    rw [hη_def] at hx
    rcases Multiset.mem_add.mp hx with hxe | hxs
    · have : s ≤ x := smallestPart_le σ x (Multiset.mem_of_mem_erase hxe)
      have hx_ne_s : x ≠ s := fun h => by
        rw [h] at hxe
        have hcs : (σ.erase s).count s = 0 := by
          have := Multiset.count_erase_self s σ; omega
        have : 0 < (σ.erase s).count s := Multiset.count_pos.mpr hxe
        omega
      omega
    · rw [Multiset.mem_singleton] at hxs; omega
  intro v hv
  have hT_eta : T σ = if η.count (smallestPart η) = 3 then η else η + ({0, 0, 0} : Multiset ℕ) := by
    show (let η' : Multiset ℕ :=
      if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
      else (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)
      if η'.count (smallestPart η') = 3 then η' else η' + ({0, 0, 0} : Multiset ℕ)) = _
    simp only [show ¬ (len σ % 3 = 2) from by omega, if_false]
    rfl
  by_cases hcnt3 : η.count (smallestPart η) = 3
  · have hTeq : T σ = η := by rw [hT_eta, if_pos hcnt3]
    have hsT : smallestPart (T σ) = s + 1 := by rw [hTeq, hsη]
    rw [hsT] at hv
    rw [hTeq, hη_def, Multiset.count_add, Multiset.count_singleton,
        if_neg (by omega : v ≠ s + 1),
        Multiset.count_erase_of_ne (by omega : v ≠ s), Nat.add_zero]
    exact hcnt v
  · have hT_form : T σ = η + ({0, 0, 0} : Multiset ℕ) := by rw [hT_eta, if_neg hcnt3]
    have h0_in_T : (0 : ℕ) ∈ T σ := by rw [hT_form]; simp
    have hsT : smallestPart (T σ) = 0 := smallestPart_eq_zero_of_zero_mem _ h0_in_T
    rw [hsT] at hv
    have hcount_T : (T σ).count v = η.count v := by
      rw [hT_form, Multiset.count_add,
          show ({0, 0, 0} : Multiset ℕ).count v = 0 by simp [show v ≠ 0 by omega], Nat.add_zero]
    rw [hcount_T, hη_def]
    rcases lt_trichotomy v (s + 1) with hlt | rfl | hgt
    · have hv_le_s : v ≤ s := by omega
      rcases eq_or_lt_of_le hv_le_s with rfl | hlt_s
      · rw [Multiset.count_add, show (σ.erase s).count s = 0 from by
            have := Multiset.count_erase_self s σ; omega,
            Multiset.count_singleton, if_neg (Nat.ne_of_lt (Nat.lt_succ_self _))]
        omega
      · rw [Multiset.count_add, Multiset.count_singleton, if_neg (by omega : v ≠ s + 1),
            Multiset.count_erase_of_ne (by omega : v ≠ s), Nat.add_zero,
            count_eq_zero_of_lt_smallestPart σ v hlt_s]
        omega
    · rw [Multiset.count_add, Multiset.count_singleton_self,
          Multiset.count_erase_of_ne (by omega : s + 1 ≠ s)]
      have h_ne_3 : σ.count (s + 1) + 1 ≠ 3 := fun h => hcnt3 (by
        rw [hsη, hη_def, Multiset.count_add, Multiset.count_singleton_self,
            Multiset.count_erase_of_ne (by omega : s + 1 ≠ s)]
        exact h)
      have := hcnt (s + 1)
      omega
    · rw [Multiset.count_add, Multiset.count_singleton, if_neg (by omega : v ≠ s + 1),
          Multiset.count_erase_of_ne (by omega : v ≠ s), Nat.add_zero]
      exact hcnt v

/-- **Larger parts of `T σ` occur at most twice.** -/
lemma T_count_larger_le_two (n : ℕ) (_hn : 1 ≤ n) (σ : Multiset ℕ)
    (hσ : σ ∈ R (n - 1)) :
    ∀ v, smallestPart (T σ) < v → (T σ).count v ≤ 2 := by
  obtain ⟨_, hpos, hcnt, hcase⟩ := hσ
  rcases hcase with hA | ⟨hB, hne, hunique⟩
  · exact T_count_larger_le_two_caseA σ hpos hcnt hA
  · exact T_count_larger_le_two_caseB σ hpos hcnt hB hne hunique

/-- If `len σ % 3 = 2`, then `len (σ + {1}) % 3 = 0`. -/
lemma len_eta_mod3_case_two (σ : Multiset ℕ) (h : len σ % 3 = 2) :
    len (σ + ({1} : Multiset ℕ)) % 3 = 0 := by
  unfold len at *
  simp [Multiset.card_add]
  omega

/-- If `len σ % 3 = 0`, `σ ≠ 0`, and the smallest part of `σ` occurs exactly
once, then `len (σ.erase (smallestPart σ) + {smallestPart σ + 1}) % 3 = 0`. -/
lemma len_eta_mod3_case_zero (σ : Multiset ℕ)
    (hσ : σ ≠ 0) (hcount : σ.count (smallestPart σ) = 1)
    (hlen : len σ % 3 = 0) :
    len (σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ)) % 3 = 0 := by
  have hmem : smallestPart σ ∈ σ := Multiset.count_pos.mp (by omega)
  have hcard : 1 ≤ Multiset.card σ := Multiset.card_pos.mpr hσ
  unfold len at *
  simp [Multiset.card_add, Multiset.card_erase_of_mem hmem]
  omega

/-- If `σ` is positive, then `σ + {1}` is also positive. -/
lemma eta_isPositive_case_two (σ : Multiset ℕ) (hpos : IsPositive σ) :
    IsPositive (σ + ({1} : Multiset ℕ)) := by
  intro x hx
  rcases Multiset.mem_add.mp hx with h | h
  · exact hpos x h
  · rw [Multiset.mem_singleton.mp h]; exact Nat.one_pos

/-- If `σ` is positive, then `σ.erase (smallestPart σ) + {smallestPart σ + 1}` is positive. -/
lemma eta_isPositive_case_zero (σ : Multiset ℕ) (hpos : IsPositive σ) :
    IsPositive (σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ)) := by
  intro x hx
  rcases Multiset.mem_add.mp hx with h | h
  · exact hpos x (Multiset.mem_of_mem_erase h)
  · rw [Multiset.mem_singleton.mp h]; exact Nat.succ_pos _

/-- If `μ.count 0 = 3`, then `μ - {0,0,0}` keeps only the non-zero parts of `μ`. -/
lemma sub_three_zeros_eq_filter_pos (μ : Multiset ℕ) (hcount : μ.count 0 = 3) :
    μ - ({0, 0, 0} : Multiset ℕ) = μ.filter (fun v => 0 < v) := by
  ext a
  rw [Multiset.count_sub, Multiset.count_filter]
  by_cases ha : a = 0
  · subst ha; simp [hcount]
  · rw [show ({0, 0, 0} : Multiset ℕ).count a = 0 by simp [ha]]
    simp [Nat.pos_of_ne_zero ha]

lemma len_sub_three_zeros_eq_tau (μ : Multiset ℕ) (_h0 : (0 : ℕ) ∈ μ)
    (hcount : μ.count 0 = 3) :
    len (μ - ({0, 0, 0} : Multiset ℕ)) = tau μ := by
  have hs : smallestPart μ = 0 :=
    smallestPart_eq_zero_of_zero_mem μ (Multiset.count_pos.mp (by omega))
  unfold len tau
  rw [sub_three_zeros_eq_filter_pos μ hcount, hs]

/-- If `η` is a positive partition, then `tau (η + {0, 0, 0}) = len η`. -/
lemma tau_add_zeros_eq_len_of_isPositive (η : Multiset ℕ) (hpos : IsPositive η) :
    tau (η + ({0, 0, 0} : Multiset ℕ)) = len η := by
  set μ : Multiset ℕ := η + ({0, 0, 0} : Multiset ℕ) with hμ
  have h0mem : (0 : ℕ) ∈ μ := by simp [hμ]
  have hcount_eta : η.count 0 = 0 :=
    Multiset.count_eq_zero.mpr fun hmem => (lt_irrefl 0) (hpos 0 hmem)
  have hcount : μ.count 0 = 3 := by simp [hμ, Multiset.count_add, hcount_eta]
  have hsub : μ - ({0, 0, 0} : Multiset ℕ) = η := by simp [hμ]
  have h := len_sub_three_zeros_eq_tau μ h0mem hcount
  rw [hsub] at h
  exact h.symm

/-- **The number of parts of `T σ` larger than its smallest part is divisible by 3.** -/
lemma T_tau_mod_three (n : ℕ) (_hn : 1 ≤ n) (σ : Multiset ℕ)
    (hσ : σ ∈ R (n - 1)) :
    tau (T σ) % 3 = 0 := by
  obtain ⟨_, hpos, _, hcase⟩ := hσ
  set η : Multiset ℕ :=
    (if len σ % 3 = 2 then σ + ({1} : Multiset ℕ)
     else (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)) with hη_def
  have hTeq : T σ =
      (if η.count (smallestPart η) = 3 then η
       else η + ({0, 0, 0} : Multiset ℕ)) := rfl
  rw [hTeq]
  have hlen_eta : len η % 3 = 0 := by
    by_cases hcase2 : len σ % 3 = 2
    · rw [hη_def, if_pos hcase2]
      exact len_eta_mod3_case_two σ hcase2
    · rw [hη_def, if_neg hcase2]
      rcases hcase with hc | ⟨h0, hne, hc1⟩
      · exact absurd hc hcase2
      · exact len_eta_mod3_case_zero σ hne hc1 h0
  have heta_pos : IsPositive η := by
    by_cases hcase2 : len σ % 3 = 2
    · rw [hη_def, if_pos hcase2]
      exact eta_isPositive_case_two σ hpos
    · rw [hη_def, if_neg hcase2]
      exact eta_isPositive_case_zero σ hpos
  by_cases hcount : η.count (smallestPart η) = 3
  · rw [if_pos hcount]
    have h := tau_add_three_eq_len_of_count_smallestPart_eq_three η hcount
    omega
  · rw [if_neg hcount]
    rw [tau_add_zeros_eq_len_of_isPositive η heta_pos]
    exact hlen_eta

lemma erase_one_add_one (σ : Multiset ℕ) :
    (σ + ({1} : Multiset ℕ)).erase 1 = σ := by
  rw [add_comm, Multiset.singleton_add, Multiset.erase_cons_head]

/-- When `σ` is positive, `L (σ + {1} + {0, 0, 0}) = (σ + {1}).erase 1`. -/
lemma L_addOneZeros_of_pos (σ : Multiset ℕ) (hpos : IsPositive σ) :
    L (σ + ({1} : Multiset ℕ) + ({0, 0, 0} : Multiset ℕ))
      = (σ + ({1} : Multiset ℕ)).erase 1 := by
  have h0mem : (0 : ℕ) ∈ σ + ({1} : Multiset ℕ) + ({0, 0, 0} : Multiset ℕ) := by simp
  have hsub : σ + ({1} : Multiset ℕ) + ({0, 0, 0} : Multiset ℕ) - ({0, 0, 0} : Multiset ℕ)
      = σ + ({1} : Multiset ℕ) := Multiset.add_sub_cancel_right
  have hsp : smallestPart (σ + ({1} : Multiset ℕ)) = 1 := smallestPart_addOne_of_pos σ hpos
  simp only [L, h0mem, if_true, hsub, hsp]

/-- **Case A helper.** When `σ` is positive with `count ≤ 2` and `len σ % 3 = 2`,
`L (T σ) = σ`. -/
lemma L_T_eq_self_caseA (σ : Multiset ℕ) (hpos : IsPositive σ)
    (hcount : ∀ v, σ.count v ≤ 2) (h2 : len σ % 3 = 2) :
    L (T σ) = σ := by
  rcases Nat.lt_or_ge (σ.count 1) 2 with hlt | hge
  · rw [T_eq_addOneZeros_of_count_lt_two σ hpos h2 hlt,
        L_addOneZeros_of_pos σ hpos, erase_one_add_one σ]
  · have hc : σ.count 1 = 2 := le_antisymm (hcount 1) hge
    rw [T_eq_addOne_of_count_eq_two σ hpos h2 hc,
        L_caseB_s1_eq _ (zero_not_mem_addOne_of_pos σ hpos) (smallestPart_addOne_of_pos σ hpos),
        erase_one_add_one σ]

/-- `T σ` is either `η` or `η + {0,0,0}` where `η = σ.erase s + {s+1}`,
when `len σ % 3 = 0`. -/
lemma T_caseB_form (σ : Multiset ℕ) (h0 : len σ % 3 = 0) :
    T σ = σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ) ∨
    T σ = σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ)
            + ({0, 0, 0} : Multiset ℕ) := by
  unfold T
  simp only [show len σ % 3 ≠ 2 by omega, if_false]
  split <;> tauto

/-- `0 ∉ σ` when `σ` is positive. -/
lemma zero_not_mem_of_isPositive (σ : Multiset ℕ) (hpos : IsPositive σ) : (0 : ℕ) ∉ σ :=
  fun h0 => by have := hpos 0 h0; omega
/-- For positive `σ`, `0 ∉ σ.erase (smallestPart σ) + {smallestPart σ + 1}`. -/
lemma zero_not_mem_eta (σ : Multiset ℕ) (hpos : IsPositive σ) :
    (0 : ℕ) ∉ (σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ) := by
  intro h
  rcases Multiset.mem_add.mp h with h | h
  · exact zero_not_mem_of_isPositive σ hpos (Multiset.mem_of_mem_erase h)
  · rw [Multiset.mem_singleton] at h; omega

/-- `(σ.erase s + {s+1}).erase (s+1) = σ.erase s`. -/
lemma erase_succ_of_erase_add_succ (σ : Multiset ℕ) (s : ℕ) :
    ((σ.erase s) + ({s + 1} : Multiset ℕ)).erase (s + 1) = σ.erase s := by
  simp [Multiset.erase_add_right_pos, Multiset.erase_singleton]

/-- `η.erase s + {s} = η` when `s ∈ η`. -/
lemma erase_add_singleton_self (η : Multiset ℕ) (s : ℕ) (hs : s ∈ η) :
    η.erase s + ({s} : Multiset ℕ) = η := by
  rw [Multiset.add_comm, Multiset.singleton_add, Multiset.cons_erase hs]

/-- **Key lemma**: For positive `σ` with unique smallest part `s`,
the smallest part of `σ.erase s + {s+1}` is `s + 1`. -/
lemma smallestPart_erase_add_succ_singleton (σ : Multiset ℕ)
    (hunique : σ.count (smallestPart σ) = 1) :
    smallestPart ((σ.erase (smallestPart σ)) + ({smallestPart σ + 1} : Multiset ℕ)) =
      smallestPart σ + 1 := by
  set s := smallestPart σ
  set η := σ.erase s + ({s + 1} : Multiset ℕ) with hη_def
  have hs_plus_one_mem : s + 1 ∈ η := by rw [hη_def]; simp
  apply smallestPart_eq_of_min η (s + 1) hs_plus_one_mem
  intro x hx
  rw [hη_def] at hx
  rcases Multiset.mem_add.mp hx with hxe | hxs
  · have hx_in_σ : x ∈ σ := Multiset.mem_of_mem_erase hxe
    have hs_le_x : s ≤ x := smallestPart_le σ x hx_in_σ
    have hx_ne_s : x ≠ s := by
      intro h_eq
      rw [h_eq] at hxe
      have h_count : (σ.erase s).count s = 0 := by
        have := Multiset.count_erase_self s σ; omega
      have : 0 < (σ.erase s).count s := Multiset.count_pos.mpr hxe
      omega
    omega
  · rw [Multiset.mem_singleton] at hxs; omega

lemma L_eq_caseB_sgt1 (μ : Multiset ℕ) (hzero : (0 : ℕ) ∉ μ)
    (hs : 2 ≤ smallestPart μ) :
    L μ = (μ.erase (smallestPart μ)) + ({smallestPart μ - 1} : Multiset ℕ) := by
  dsimp only [L]
  rw [if_neg hzero]
  split_ifs <;> simp_all

/-- The smallest part of a positive nonempty multiset is at least `1`. -/
lemma smallestPart_pos (σ : Multiset ℕ) (hpos : IsPositive σ) (hne : σ ≠ 0) :
    1 ≤ smallestPart σ :=
  hpos _ (smallestPart_mem σ hne)

/-- Computes `L η` where `η = σ.erase s + {s+1}`, given Case B hypotheses. -/
lemma L_eta_caseB (σ : Multiset ℕ) (hpos : IsPositive σ) (hne : σ ≠ 0)
    (hunique : σ.count (smallestPart σ) = 1) :
    L (σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ)) = σ := by
  set s := smallestPart σ
  set η : Multiset ℕ := σ.erase s + ({s + 1} : Multiset ℕ)
  have h0 : (0 : ℕ) ∉ η := zero_not_mem_eta σ hpos
  have hsmall : smallestPart η = s + 1 :=
    smallestPart_erase_add_succ_singleton σ hunique
  have hs_pos : 1 ≤ s := smallestPart_pos σ hpos hne
  have hsmall_ge2 : 2 ≤ smallestPart η := by rw [hsmall]; omega
  rw [L_eq_caseB_sgt1 η h0 hsmall_ge2]
  rw [hsmall]
  simp only [Nat.add_sub_cancel]
  rw [erase_succ_of_erase_add_succ σ s]
  exact erase_add_singleton_self σ s (smallestPart_mem σ hne)

lemma L_add_three_zeros_eq_L (η : Multiset ℕ) (h0 : (0 : ℕ) ∉ η) :
    L (η + ({0, 0, 0} : Multiset ℕ)) = L η := by
  have h1 : (η + ({0, 0, 0} : Multiset ℕ)) - ({0, 0, 0} : Multiset ℕ) = η := by
    rw [add_comm]; simp
  have h2 : (0 : ℕ) ∈ η + ({0, 0, 0} : Multiset ℕ) := by simp
  dsimp only [L]
  rw [if_pos h2, if_neg h0, h1]

/-- Computes `L (η + {0,0,0})` where `η = σ.erase s + {s+1}`, given Case B hypotheses. -/
lemma L_eta_with_zeros_caseB (σ : Multiset ℕ) (hpos : IsPositive σ) (hne : σ ≠ 0)
    (hunique : σ.count (smallestPart σ) = 1) :
    L (σ.erase (smallestPart σ) + ({smallestPart σ + 1} : Multiset ℕ)
        + ({0, 0, 0} : Multiset ℕ)) = σ := by
  rw [L_add_three_zeros_eq_L _ (zero_not_mem_eta σ hpos)]
  exact L_eta_caseB σ hpos hne hunique

/-- **Case B helper.** -/
lemma L_T_eq_self_caseB (σ : Multiset ℕ) (hpos : IsPositive σ)
    (_hcount : ∀ v, σ.count v ≤ 2) (h0 : len σ % 3 = 0)
    (hne : σ ≠ 0) (hunique : σ.count (smallestPart σ) = 1) :
    L (T σ) = σ := by
  rcases T_caseB_form σ h0 with hT | hT
  · rw [hT]; exact L_eta_caseB σ hpos hne hunique
  · rw [hT]; exact L_eta_with_zeros_caseB σ hpos hne hunique

lemma sub_three_zeros_add_three_zeros (μ : Multiset ℕ) (h : μ.count 0 = 3) :
    (μ - ({0, 0, 0} : Multiset ℕ)) + ({0, 0, 0} : Multiset ℕ) = μ :=
  Multiset.sub_add_cancel (three_zeros_le μ h.ge)

/-- `(η.erase 1) + {1} = η` when `1 ∈ η`. -/
lemma erase_one_add_one_eq (η : Multiset ℕ) (h1 : (1 : ℕ) ∈ η) :
    (η.erase 1) + ({1} : Multiset ℕ) = η := by
  rw [Multiset.add_comm, Multiset.singleton_add, Multiset.cons_erase h1]

lemma len_erase_one_mod_three_of_len_zero (η : Multiset ℕ) (h1 : (1 : ℕ) ∈ η)
    (hlen : len η % 3 = 0) :
    len (η.erase 1) % 3 = 2 := by
  unfold len at *
  rw [Multiset.card_erase_of_mem h1, Nat.pred_eq_sub_one]
  have hpos : 0 < Multiset.card η := Multiset.card_pos.mpr (by rintro rfl; simp at h1)
  omega

lemma T_L_eq_self_case_zero_in_s1 (n : ℕ) (_hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (hzero : (0 : ℕ) ∈ μ)
    (hs1 : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) = 1) :
    T (L μ) = μ := by
  obtain ⟨⟨_, _, hcount_s, hcount_big⟩, htau⟩ := hμ
  have hsm0 : smallestPart μ = 0 := smallestPart_eq_zero_of_zero_mem μ hzero
  have hcount0 : μ.count 0 = 3 := by rw [← hsm0]; exact hcount_s
  set η : Multiset ℕ := μ - ({0, 0, 0} : Multiset ℕ)
  have hη_pos : IsPositive η := sub_three_zeros_isPositive μ hcount0
  have hη_ne : η ≠ 0 := by
    intro h
    have : smallestPart η = 0 := by rw [h]; simp [smallestPart]
    rw [hs1] at this; exact absurd this (by norm_num)
  have h1_mem : (1 : ℕ) ∈ η := hs1 ▸ smallestPart_mem η hη_ne
  have hLμ : L μ = η.erase 1 := L_eval_caseA_s1 μ hzero hs1
  set σ : Multiset ℕ := η.erase 1 with hσ_def
  have hσ_pos : IsPositive σ := fun x hx => hη_pos x (Multiset.mem_of_mem_erase hx)
  have hη_count_one : η.count 1 ≤ 2 := by
    rw [count_pos_sub_three_zeros μ 1 (by norm_num)]
    exact hcount_big 1 (by rw [hsm0]; norm_num)
  have hσc1 : σ.count 1 < 2 := by
    rw [hσ_def, Multiset.count_erase_self]; omega
  have hlen_η_mod : len η % 3 = 0 := by
    rw [len_sub_three_zeros_eq_tau μ hzero hcount0]; exact htau
  have hlen_σ_mod : len σ % 3 = 2 :=
    len_erase_one_mod_three_of_len_zero η h1_mem hlen_η_mod
  rw [hLμ, T_eq_addOneZeros_of_count_lt_two σ hσ_pos hlen_σ_mod hσc1,
      erase_one_add_one_eq η h1_mem, sub_three_zeros_add_three_zeros μ hcount0]

lemma one_le_smallestPart_of_zero_notMem (η : Multiset ℕ) (hne : η ≠ 0)
    (hzero : (0 : ℕ) ∉ η) : 1 ≤ smallestPart η := by
  have hmem : smallestPart η ∈ η := smallestPart_mem η hne
  have : smallestPart η ≠ 0 := fun h => hzero (h ▸ hmem)
  omega

lemma zero_notMem_sub_three_zeros (μ : Multiset ℕ) (h : μ.count 0 = 3) :
    (0 : ℕ) ∉ (μ - ({0, 0, 0} : Multiset ℕ)) := by
  rw [← Multiset.count_pos, count_zero_sub_three_zeros, h]
  omega

lemma count_smallestPart_eta_le_two (n : ℕ) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∈ μ)
    (hne : (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 0) :
    (μ - ({0, 0, 0} : Multiset ℕ)).count
      (smallestPart (μ - ({0, 0, 0} : Multiset ℕ))) ≤ 2 := by
  obtain ⟨⟨_, _, hcount_s, hbound⟩, _⟩ := hμ
  have hs0 : smallestPart μ = 0 := smallestPart_eq_zero_of_zero_mem μ h0
  have hcount0 : μ.count 0 = 3 := by rw [← hs0]; exact hcount_s
  set η := μ - ({0, 0, 0} : Multiset ℕ)
  have hsη_pos : 1 ≤ smallestPart η :=
    one_le_smallestPart_of_zero_notMem η hne (zero_notMem_sub_three_zeros μ hcount0)
  rw [count_pos_sub_three_zeros μ (smallestPart η) hsη_pos]
  exact hbound _ (by rw [hs0]; omega)

lemma count_zero_eq_three_of_D3_zero_mem (n : ℕ) (μ : Multiset ℕ)
    (hμ : μ ∈ D3 n) (h0 : (0 : ℕ) ∈ μ) : μ.count 0 = 3 :=
  smallestPart_eq_zero_of_zero_mem μ h0 ▸ hμ.2.2.1

lemma erase_pred_of_erase_add_singleton (η : Multiset ℕ) (s : ℕ)
    (hs : 1 ≤ s) (hsp : s = smallestPart η) :
    ((η.erase s) + ({s - 1} : Multiset ℕ)).erase (s - 1) = η.erase s := by
  have hnot : s - 1 ∉ η := fun hmem => by
    have : s ≤ s - 1 := hsp ▸ smallestPart_le η (s - 1) hmem
    omega
  rw [Multiset.erase_add_right_neg _ (fun h => hnot (Multiset.mem_of_mem_erase h))]
  simp [Multiset.erase_singleton]

lemma len_L_caseA_sgt1_mod3 (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (h0 : (0 : ℕ) ∈ μ)
    (_hs1 : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 1) :
    len ((μ - ({0, 0, 0} : Multiset ℕ)).erase
            (smallestPart (μ - ({0, 0, 0} : Multiset ℕ)))
          + ({smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) - 1} : Multiset ℕ)) % 3 = 0 := by
  set η : Multiset ℕ := μ - ({0, 0, 0} : Multiset ℕ)
  set s : ℕ := smallestPart η with hs_def
  have hμD3 : μ ∈ D3 n := hμ.1
  have htau : tau μ % 3 = 0 := hμ.2
  have hcnt0 : μ.count 0 = 3 := count_zero_eq_three_of_D3_zero_mem n μ hμD3 h0
  have hηne : η ≠ 0 := sub_three_zeros_ne_zero_of_caseA n hn μ hμ h0
  have hsmem : s ∈ η := by rw [hs_def]; exact smallestPart_mem η hηne
  have hcard : Multiset.card ((η.erase s) + ({s - 1} : Multiset ℕ)) = Multiset.card η :=
    card_erase_add_singleton η s hsmem
  have hlen_tau : len η = tau μ := len_sub_three_zeros_eq_tau μ h0 hcnt0
  unfold len at hlen_tau
  show Multiset.card ((η.erase s) + ({s - 1} : Multiset ℕ)) % 3 = 0
  rw [hcard, hlen_tau]
  exact htau

lemma T_L_eq_self_case_zero_in_sgt1 (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (hzero : (0 : ℕ) ∈ μ)
    (hs_ne1 : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) ≠ 1) :
    T (L μ) = μ := by
  set η : Multiset ℕ := μ - ({0, 0, 0} : Multiset ℕ)
  set s : ℕ := smallestPart η with hs_def
  have hμD3 : μ ∈ D3 n := hμ.1
  have hηne : η ≠ 0 := sub_three_zeros_ne_zero_of_caseA n hn μ hμ hzero
  have hcnt0 : μ.count 0 = 3 := count_zero_eq_three_of_D3_zero_mem n μ hμD3 hzero
  have hs1 : 1 ≤ s := smallestPart_sub_three_zeros_ge_one μ hcnt0 hηne
  have hs2 : 2 ≤ s := by omega
  have hLeq : L μ = η.erase s + ({s - 1} : Multiset ℕ) := L_eq_caseA_sgt1 μ hzero hs_ne1
  have hspL : smallestPart (L μ) = s - 1 := by
    rw [hLeq]
    exact smallestPart_erase_add_singleton η s hs2 hs_def
  have hlen0 : len (L μ) % 3 = 0 := by
    rw [hLeq]; exact len_L_caseA_sgt1_mod3 n hn μ hμ hzero hs_ne1
  have hlen_ne2 : len (L μ) % 3 ≠ 2 := by omega
  have hsmem : s ∈ η := by
    rw [hs_def]; exact smallestPart_mem η hηne
  have hcnt_s : η.count s ≤ 2 :=
    count_smallestPart_eta_le_two n μ hμ hzero hηne
  unfold T
  simp only [hlen_ne2, if_false]
  rw [hspL, Nat.sub_add_cancel hs1, hLeq, erase_pred_of_erase_add_singleton η s hs1 hs_def,
      erase_add_singleton_self η s hsmem]
  have htest : η.count (smallestPart η) ≠ 3 := by rw [← hs_def]; omega
  simp only [htest, if_false]
  exact sub_three_zeros_add_three_zeros μ hcnt0

lemma T_L_eq_self_case_zero_in (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (hzero : (0 : ℕ) ∈ μ) : T (L μ) = μ := by
  by_cases hs1 : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) = 1
  · exact T_L_eq_self_case_zero_in_s1 n hn μ hμ hzero hs1
  · exact T_L_eq_self_case_zero_in_sgt1 n hn μ hμ hzero hs1

/-- Case B: when `smallestPart μ = 1`, `T (L μ) = μ`. -/
lemma T_L_case_s_eq_one
    (n : ℕ) (μ : Multiset ℕ) (hμ : μ ∈ D3_0 n)
    (hzero : (0 : ℕ) ∉ μ) (hs : smallestPart μ = 1) :
    T (L μ) = μ := by
  have hcount : μ.count 1 = 3 := count_one_of_caseB_s1 n μ hμ hs
  have hmem : (1 : ℕ) ∈ μ := mem_one_of_caseB_s1 n μ hμ hs
  have hpos : IsPositive (μ.erase 1) := isPositive_erase_one μ hzero
  have hce : (μ.erase 1).count 1 = 2 := by
    rw [Multiset.count_erase_self, hcount]
  have hlen : len (μ.erase 1) % 3 = 2 :=
    len_erase_one_mod_three n μ hμ.1 hs hcount hμ.2
  rw [L_caseB_s1_eq μ hzero hs, T_eq_addOne_of_count_eq_two (μ.erase 1) hpos hlen hce,
      erase_one_add_one_eq μ hmem]

/-- Case B: when `smallestPart μ ≥ 2`, `T (L μ) = μ`. -/
lemma T_L_case_s_ge_two
    (n : ℕ) (μ : Multiset ℕ) (hμ : μ ∈ D3_0 n)
    (hzero : (0 : ℕ) ∉ μ) (hs : 2 ≤ smallestPart μ) :
    T (L μ) = μ := by
  obtain ⟨⟨hsum, hne, hcount, hlarge⟩, htau⟩ := hμ
  set s := smallestPart μ
  have hs1 : 1 ≤ s := by omega
  have hs_mem : s ∈ μ := smallestPart_mem μ hne
  have hL : L μ = μ.erase s + ({s - 1} : Multiset ℕ) := by
    show L μ = μ.erase (smallestPart μ) + ({smallestPart μ - 1} : Multiset ℕ)
    unfold L; simp [hzero, show smallestPart μ ≠ 1 by omega]
  have hsmL : smallestPart (L μ) = s - 1 := by
    rw [hL]; exact smallestPart_erase_add_singleton μ s hs rfl
  have hcard_eq : Multiset.card μ = 3 + tau μ :=
    card_eq_three_add_tau_caseB μ n ⟨hsum, hne, hcount, hlarge⟩
  have hlenL_ne2 : len (L μ) % 3 ≠ 2 := by
    unfold len; rw [hL, card_erase_add_singleton μ s hs_mem, hcard_eq]; omega
  have hsm1_not_mem_μ : s - 1 ∉ μ := fun hm => by
    have : s ≤ s - 1 := smallestPart_le μ _ hm; omega
  have hLerase : (L μ).erase (s - 1) = μ.erase s := by
    rw [hL, Multiset.erase_add_right_neg _ (fun h => hsm1_not_mem_μ (Multiset.mem_of_mem_erase h))]
    simp [Multiset.erase_singleton]
  have heta_T :
      (L μ).erase (smallestPart (L μ)) + ({smallestPart (L μ) + 1} : Multiset ℕ) = μ := by
    rw [hsmL, hLerase, Nat.sub_add_cancel hs1, Multiset.add_comm, Multiset.singleton_add,
        Multiset.cons_erase hs_mem]
  unfold T
  simp only [hlenL_ne2, if_false]
  rw [heta_T, if_pos hcount]

/-- **Case B: `T ∘ L = id` when `0 ∉ μ`.** -/
lemma T_L_eq_self_case_zero_not_in (n : ℕ) (_hn : 1 ≤ n) (μ : Multiset ℕ)
    (hμ : μ ∈ D3_0 n) (hzero : (0 : ℕ) ∉ μ) : T (L μ) = μ := by
  have hne : μ ≠ 0 := hμ.1.2.1
  have hs1 : 1 ≤ smallestPart μ :=
    one_le_smallestPart_of_zero_notMem μ hne hzero
  rcases Nat.lt_or_ge (smallestPart μ) 2 with hlt | hge
  · exact T_L_case_s_eq_one n μ hμ hzero (by omega)
  · exact T_L_case_s_ge_two n μ hμ hzero hge

/-- **Well-definedness of `L`.** -/
lemma L_mem_R (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ) (hμ : μ ∈ D3_0 n) :
    L μ ∈ R (n - 1) := by
  by_cases h0 : (0 : ℕ) ∈ μ
  · by_cases hs : smallestPart (μ - ({0, 0, 0} : Multiset ℕ)) = 1
    · exact L_mem_R_caseA_s1 n hn μ hμ h0 hs
    · exact L_mem_R_caseA_sgt1 n hn μ hμ h0 hs
  · by_cases hs : smallestPart μ = 1
    · exact L_mem_R_caseB_s1 n hn μ hμ h0 hs
    · exact L_mem_R_caseB_sgt1 n hn μ hμ h0 hs

/-- **Well-definedness of `T`.** -/
lemma T_mem_D3_0 (n : ℕ) (hn : 1 ≤ n) (σ : Multiset ℕ) (hσ : σ ∈ R (n - 1)) :
    T σ ∈ D3_0 n :=
  ⟨⟨T_sum_eq n hn σ hσ, T_ne_zero n hn σ hσ, T_count_smallest_eq_three n hn σ hσ,
    T_count_larger_le_two n hn σ hσ⟩, T_tau_mod_three n hn σ hσ⟩

/-- **`L ∘ T = id` on `R(n-1)`.** -/
lemma L_T_eq_self (n : ℕ) (_hn : 1 ≤ n) (σ : Multiset ℕ) (hσ : σ ∈ R (n - 1)) :
    L (T σ) = σ := by
  obtain ⟨_, hpos, hcount, hcase⟩ := hσ
  rcases hcase with h2 | ⟨h0, hne, hunique⟩
  · exact L_T_eq_self_caseA σ hpos hcount h2
  · exact L_T_eq_self_caseB σ hpos hcount h0 hne hunique

/-- **`T ∘ L = id` on `D3_0(n)`.** -/
lemma T_L_eq_self (n : ℕ) (hn : 1 ≤ n) (μ : Multiset ℕ) (hμ : μ ∈ D3_0 n) :
    T (L μ) = μ := by
  by_cases hzero : (0 : ℕ) ∈ μ
  · exact T_L_eq_self_case_zero_in n hn μ hμ hzero
  · exact T_L_eq_self_case_zero_not_in n hn μ hμ hzero

/-! ### Main theorem. -/

/-- For every `n ≥ 1`, the maps `L : D_3^{(0)}(n) → R(n-1)` and
`T : R(n-1) → D_3^{(0)}(n)` are well-defined and mutually inverse bijections. -/
theorem lem_L (_thm1 : Thm1) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ μ ∈ D3_0 n, L μ ∈ R (n - 1)) ∧
      (∀ σ ∈ R (n - 1), T σ ∈ D3_0 n) ∧
      (∀ σ ∈ R (n - 1), L (T σ) = σ) ∧
      (∀ μ ∈ D3_0 n, T (L μ) = μ) := fun n hn =>
  ⟨L_mem_R n hn, T_mem_D3_0 n hn, L_T_eq_self n hn, T_L_eq_self n hn⟩

end AndrewsDhar
