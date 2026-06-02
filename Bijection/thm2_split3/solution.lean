import Mathlib

/-!
# Conjugation bijection between repetition-bounded partitions and
3-flat partitions with first nonzero residue 2

This file proves `lem_conj`: conjugation induces a bijection
`R(N) → F²(N)`. The proof goes via structural properties of `conjList`
(weight preservation, positivity, involution), the *intermediate lemma*
expressing multiplicity as a consecutive difference of the conjugate,
and matching forward and backward direction lemmas.
-/

namespace AndrewsDhar

open scoped Classical

-- ===========================================================================
-- Definitions copied verbatim from problem.lean
-- ===========================================================================

def IsPart (l : List ℕ) : Prop := l.Pairwise (· ≥ ·)

def IsPosPart (l : List ℕ) : Prop :=
  l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, 0 < x

def weight (l : List ℕ) : ℕ := l.sum

def length (l : List ℕ) : ℕ := l.length

def conjList (l : List ℕ) : List ℕ :=
  (List.range (l.headD 0)).map (fun i => l.countP (fun x => decide (i + 1 ≤ x)))

def Is3Flat (l : List ℕ) : Prop :=
  ∀ i : ℕ, i < l.length → (l.getD i 0) - (l.getD (i + 1) 0) < 3

def firstNonzeroRes3 (l : List ℕ) : Option ℕ :=
  (l.find? (fun x => decide (x % 3 ≠ 0))).map (fun x => x % 3)

def setF2 (N : ℕ) : Set (List ℕ) :=
  { α | IsPosPart α ∧ weight α = N ∧ Is3Flat α ∧ firstNonzeroRes3 α = some 2 }

def setR (N : ℕ) : Set (List ℕ) :=
  { σ | IsPosPart σ ∧ weight σ = N ∧ σ ≠ [] ∧
        (∀ k, σ.count k ≤ 2) ∧
        (σ.length % 3 = 2 ∨
          (σ.length % 3 = 0 ∧ σ.count (σ.getLastD 0) = 1)) }

def partitionsOf (n : ℕ) : Set (List ℕ) :=
  { l | l.Pairwise (· ≥ ·) ∧ l.sum = n }

def positivePartitionsOf (n : ℕ) : Set (List ℕ) :=
  { l | IsPosPart l ∧ l.sum = n }

def isCmPart (m : ℕ) (σ : List ℕ) : Prop :=
  σ ≠ [] ∧
    ∃ j : ℕ, σ.headD 0 = m * j ∧ ∀ k : ℕ, 1 ≤ k → k ≤ j → σ.count k < m

noncomputable def C_m (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else Set.ncard { σ ∈ positivePartitionsOf n | isCmPart m σ }

def isDmPart (m : ℕ) (σ : List ℕ) : Prop :=
  σ ≠ [] ∧
    σ.count (σ.getLastD 0) = m ∧
    ∀ k : ℕ, σ.getLastD 0 < k → σ.count k < m

noncomputable def D_m (m n : ℕ) : ℕ :=
  Set.ncard { σ ∈ partitionsOf n | isDmPart m σ }

noncomputable def zeta_m (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / m)

noncomputable def qPochFinite (A : PowerSeries ℂ) (N : ℕ) : PowerSeries ℂ :=
  ∏ i ∈ Finset.range N, (1 - A * (PowerSeries.X : PowerSeries ℂ) ^ i)

noncomputable def qPochInf (A : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk
    (fun n => PowerSeries.coeff (R := ℂ) n (qPochFinite A (n + 1)))

noncomputable def epsilon_m (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (fun N =>
    ∑ n ∈ Finset.range (N + 1),
      PowerSeries.coeff (R := ℂ) N
        ((PowerSeries.X : PowerSeries ℂ) ^ (m * n)
          * qPochInf ((PowerSeries.X : PowerSeries ℂ) ^ (m * (n + 1)))
          * ∑ j ∈ Finset.Ico 1 m,
              (qPochInf
                ((zeta_m m) ^ j • ((PowerSeries.X : PowerSeries ℂ) ^ (n + 1))))⁻¹))

noncomputable def E_m_complex (m n : ℕ) : ℂ :=
  PowerSeries.coeff (R := ℂ) n (epsilon_m m)

def Thm1 : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ),
    ∃ Em : ℤ, ((Em : ℂ) = E_m_complex m n) ∧
      ((m : ℤ) * (C_m m n : ℤ) = (D_m m n : ℤ) + Em)

-- ===========================================================================
-- Basic facts about positive partitions
-- ===========================================================================

/-- For a weakly-decreasing list, every element is at most the head. -/
lemma all_le_headD (σ : List ℕ) (hsort : σ.Pairwise (· ≥ ·)) :
    ∀ x ∈ σ, x ≤ σ.headD 0 := by
  induction σ with
  | nil => simp
  | cons a l _ =>
    intro x hx
    cases l with
    | nil => grind [List.headD]
    | cons b l => grind [List.headD]

/-- For a weakly-decreasing list, every element is at least the last element. -/
lemma all_ge_getLastD (σ : List ℕ) (hsort : σ.Pairwise (· ≥ ·)) :
    ∀ x ∈ σ, σ.getLastD 0 ≤ x := by
  induction σ with
  | nil => simp
  | cons a rest ih =>
    rw [List.pairwise_cons] at hsort
    obtain ⟨hhead, htail⟩ := hsort
    intro x hx
    rcases rest with _ | ⟨b, rest'⟩
    · simp at hx
      subst hx
      simp [List.getLastD]
    · rw [show (a :: b :: rest').getLastD 0 = (b :: rest').getLastD 0 from by simp]
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [List.getLastD_cons]
        exact hhead _ (List.getLastD_mem_cons (l := rest') (a := b))
      · exact ih htail x hx

-- ===========================================================================
-- Weight preservation under conjugation
-- ===========================================================================

/-- Sum of indicators `if i+1 ≤ a then 1 else 0` over `i ∈ range m` is `min a m`. -/
lemma sum_indicator_range_eq_min (a m : ℕ) :
    ((List.range m).map (fun i => if i + 1 ≤ a then (1:ℕ) else 0)).sum = min a m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h : m + 1 ≤ a <;> simp [h] <;> omega

/-- `countP` distributes over `cons` after summing over a range. -/
lemma sum_countP_range_cons (a : ℕ) (L : List ℕ) (m : ℕ) :
    ((List.range m).map (fun i => (a :: L).countP (fun x => decide (i + 1 ≤ x)))).sum
      = min a m
        + ((List.range m).map (fun i => L.countP (fun x => decide (i + 1 ≤ x)))).sum := by
  have hpt : ∀ i,
      (a :: L).countP (fun x => decide (i + 1 ≤ x))
        = L.countP (fun x => decide (i + 1 ≤ x)) + (if i + 1 ≤ a then 1 else 0) := by
    intro i
    rw [List.countP_cons]
    by_cases h : i + 1 ≤ a <;> simp [h]
  simp only [hpt]
  rw [show ∀ (l : List ℕ),
      (l.map (fun i => L.countP (fun x => decide (i+1 ≤ x))
                        + (if i + 1 ≤ a then (1:ℕ) else 0))).sum
      = (l.map (fun i => L.countP (fun x => decide (i+1 ≤ x)))).sum
        + (l.map (fun i => (if i + 1 ≤ a then (1:ℕ) else 0))).sum from by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring,
    sum_indicator_range_eq_min]
  ring

/-- Double-counting identity:
`∑_{i<m} #{x ∈ σ : i+1 ≤ x} = ∑_{x ∈ σ} min x m`. -/
lemma sum_countP_range_eq_sum_map_min (σ : List ℕ) (m : ℕ) :
    ((List.range m).map (fun i => σ.countP (fun x => decide (i + 1 ≤ x)))).sum
      = (σ.map (fun x => min x m)).sum := by
  induction σ with
  | nil => simp
  | cons a L ih =>
    rw [sum_countP_range_cons a L m, ih]
    simp [List.map_cons, List.sum_cons]

/-- For a positive partition `σ`, summing `min x (σ.headD 0)` over `σ` gives `σ.sum`. -/
lemma sum_map_min_headD (σ : List ℕ) (h : IsPosPart σ) :
    (σ.map (fun x => min x (σ.headD 0))).sum = σ.sum := by
  rw [show σ.map (fun x => min x (σ.headD 0)) = σ.map id from
      List.map_congr_left (fun x hx => Nat.min_eq_left (all_le_headD σ h.1 x hx)),
      List.map_id]

/-- **Weight preservation.** Conjugation preserves the total weight. -/
lemma conjList_weight (σ : List ℕ) (h : IsPosPart σ) :
    weight (conjList σ) = weight σ := by
  unfold weight conjList
  rw [sum_countP_range_eq_sum_map_min σ (σ.headD 0)]
  exact sum_map_min_headD σ h

-- ===========================================================================
-- Structural properties of conjList
-- ===========================================================================

/-- The conjugate list is weakly decreasing. -/
lemma conjList_pairwise (l : List ℕ) :
    (conjList l).Pairwise (· ≥ ·) := by
  refine (List.pairwise_map).2 (List.pairwise_lt_range.imp ?_)
  intro i j hij
  exact List.countP_mono_left (fun x _ hx => by
    simp only [decide_eq_true_eq] at hx ⊢; omega)

/-- Every entry of the conjugate of a positive partition is positive. -/
lemma conjList_all_pos (σ : List ℕ) (_h : IsPosPart σ) :
    ∀ x ∈ conjList σ, 0 < x := by
  intro x hx
  simp only [conjList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  cases hσ : σ with
  | nil => simp [hσ] at hi
  | cons hd tl =>
    have hi' : i < hd := by simpa [hσ, List.headD] using hi
    rw [List.countP_eq_length_filter]
    exact List.length_pos_of_mem
      (List.mem_filter.mpr ⟨List.mem_cons_self, by simp [hi']⟩)
/-- The conjugate of a positive partition is a positive partition. -/
lemma conjList_isPosPart (σ : List ℕ) (h : IsPosPart σ) :
    IsPosPart (conjList σ) :=
  ⟨conjList_pairwise σ, conjList_all_pos σ h⟩

/-- First entry of the conjugate of a nonempty positive partition equals its length. -/
lemma conjList_head_eq_length (σ : List ℕ) (h_pos : IsPosPart σ) (h_ne : σ ≠ []) :
    (conjList σ).getD 0 0 = σ.length := by
  have h1 : 0 < σ.headD 0 := by
    cases σ with
    | nil => exact absurd rfl h_ne
    | cons a _ => exact h_pos.2 a (by simp)
  unfold conjList
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1]
  simp
  exact h_pos.2

/-- Length of the conjugate equals the largest part of the original. -/
lemma length_conjList (σ : List ℕ) :
    (conjList σ).length = σ.headD 0 := by
  simp [conjList, List.length_map, List.length_range]

/-- The `i`-th element of `conjList σ` is `σ.countP (i+1 ≤ ·)`. -/
lemma conjList_getElem (σ : List ℕ) (i : ℕ) (hi : i < (conjList σ).length) :
    (conjList σ)[i] = σ.countP (fun x => decide (i + 1 ≤ x)) := by
  simp [conjList, List.getElem_map, List.getElem_range]

/-- The double conjugate has the same length as the original. -/
lemma conjList_conjList_length (σ : List ℕ) (h : IsPosPart σ) :
    (conjList (conjList σ)).length = σ.length := by
  by_cases h_ne : σ = []
  · subst h_ne
    simp [conjList]
  · rw [length_conjList, show (conjList σ).headD 0 = (conjList σ).getD 0 0 from by
      cases conjList σ <;> rfl, conjList_head_eq_length σ h h_ne]

-- ===========================================================================
-- The counting bridge: σ[j] ≥ k+1 ↔ countP (k+1 ≤ ·) ≥ j+1
-- ===========================================================================

/-- On a weakly decreasing list, if `σ[j] ≥ m` then the first `j+1` entries
also satisfy `· ≥ m`, so the count is at least `j+1`. -/
lemma countP_ge_of_sorted (σ : List ℕ) (hp : σ.Pairwise (· ≥ ·))
    (j : ℕ) (hj : j < σ.length) (m : ℕ) (hm : m ≤ σ[j]) :
    j + 1 ≤ σ.countP (fun x => decide (m ≤ x)) := by
  have hall : ∀ x ∈ σ.take (j+1), m ≤ x := by
    intro x hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hij : i ≤ j := by
      have := lt_min_iff.mp hi
      omega
    have hilen : i < σ.length := (lt_min_iff.mp hi).2
    rcases lt_or_eq_of_le hij with hij' | rfl
    · have hge : σ[i] ≥ σ[j] :=
        List.pairwise_iff_getElem.mp hp i j hilen hj hij'
      omega
    · exact hm
  have h1 : (σ.take (j+1)).countP (fun x => decide (m ≤ x))
              = (σ.take (j+1)).length := by
    rw [List.countP_eq_length]
    intro x hx
    simp [hall x hx]
  have hlen : (σ.take (j+1)).length = j + 1 := by
    rw [List.length_take]
    omega
  have hmono : (σ.take (j+1)).countP (fun x => decide (m ≤ x))
                 ≤ σ.countP (fun x => decide (m ≤ x)) :=
    (List.take_sublist _ _).countP_le
  omega

/-- On a weakly decreasing list, the suffix from index `j` contributes zero
count when `σ[j] < m`. -/
lemma countP_drop_eq_zero_of_sorted (σ : List ℕ) (hp : σ.Pairwise (· ≥ ·))
    (j : ℕ) (hj : j < σ.length) (m : ℕ) (hm : σ[j] < m) :
    (σ.drop j).countP (fun x => decide (m ≤ x)) = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  rw [Bool.not_eq_true, decide_eq_false_iff_not, not_le]
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  rw [List.length_drop] at hi
  have hk : j + i < σ.length := by omega
  have hle : σ[j + i] ≤ σ[j] := by
    rcases Nat.eq_or_lt_of_le (Nat.le_add_right j i) with heq | hlt
    · have : i = 0 := by omega
      subst this; simp
    · exact (List.pairwise_iff_getElem.mp hp) j (j + i) hj hk hlt
  rw [← hxi, List.getElem_drop]
  exact lt_of_le_of_lt hle hm

/-- On a weakly decreasing list, if `σ[j] < m` then the count of `· ≥ m` is at most `j`. -/
lemma countP_lt_of_sorted (σ : List ℕ) (hp : σ.Pairwise (· ≥ ·))
    (j : ℕ) (hj : j < σ.length) (m : ℕ) (hm : σ[j] < m) :
    σ.countP (fun x => decide (m ≤ x)) ≤ j := by
  have hcount :
      σ.countP (fun x => decide (m ≤ x)) =
        (σ.take j).countP (fun x => decide (m ≤ x)) +
        (σ.drop j).countP (fun x => decide (m ≤ x)) := by
    conv_lhs => rw [show σ = σ.take j ++ σ.drop j from (List.take_append_drop j σ).symm]
    exact List.countP_append
  rw [hcount, countP_drop_eq_zero_of_sorted σ hp j hj m hm, Nat.add_zero]
  exact List.countP_le_length.trans (by rw [List.length_take]; omega)

/-- **Counting bridge.** For a positive partition `σ` and any `j < σ.length`,
`countP (k+1 ≤ ·) σ ≥ j+1 ↔ σ[j] ≥ k+1`. -/
lemma countP_ge_iff_get_ge (σ : List ℕ) (h : IsPosPart σ)
    (j : ℕ) (hj : j < σ.length) (k : ℕ) :
    j + 1 ≤ σ.countP (fun x => decide (k + 1 ≤ x)) ↔ k + 1 ≤ σ[j] := by
  refine ⟨fun hc => ?_, fun hge => countP_ge_of_sorted σ h.1 j hj (k + 1) hge⟩
  by_contra hne
  have := countP_lt_of_sorted σ h.1 j hj (k + 1) (Nat.lt_of_not_le hne)
  omega

/-- The number of parts of `conjList σ` that are `≥ j+1` equals `σ[j]`. -/
lemma countP_conjList_eq_get (σ : List ℕ) (h : IsPosPart σ)
    (j : ℕ) (hj : j < σ.length) :
    (conjList σ).countP (fun x => decide (j + 1 ≤ x)) = σ[j] := by
  have hsort_L : (conjList σ).Pairwise (· ≥ ·) := conjList_pairwise σ
  have hlen_L : (conjList σ).length = σ.headD 0 := length_conjList σ
  have hj_mem : σ[j] ∈ σ := σ.getElem_mem hj
  have hj_pos : 0 < σ[j] := h.2 σ[j] hj_mem
  have hj_L : σ[j] ≤ (conjList σ).length := hlen_L ▸ all_le_headD σ h.1 σ[j] hj_mem
  refine Nat.le_antisymm ?_ ?_
  · by_cases hjL : σ[j] = (conjList σ).length
    · rw [hjL]; exact List.countP_le_length
    · have hjL' : σ[j] < (conjList σ).length := lt_of_le_of_ne hj_L hjL
      apply countP_lt_of_sorted (conjList σ) hsort_L σ[j] hjL' (j + 1)
      rw [conjList_getElem σ σ[j] hjL']
      by_contra hge
      push_neg at hge
      have := (countP_ge_iff_get_ge σ h j hj σ[j]).mp hge
      omega
  · have hj_pred_lt : σ[j] - 1 < (conjList σ).length :=
      lt_of_lt_of_le (Nat.sub_lt hj_pos Nat.one_pos) hj_L
    have key : j + 1 ≤ (conjList σ)[σ[j] - 1] := by
      rw [conjList_getElem σ (σ[j] - 1) hj_pred_lt]
      exact (countP_ge_iff_get_ge σ h j hj (σ[j] - 1)).mpr (by omega)
    have hle := countP_ge_of_sorted (conjList σ) hsort_L (σ[j] - 1) hj_pred_lt (j + 1) key
    rwa [Nat.sub_add_cancel hj_pos] at hle

-- ===========================================================================
-- Conjugation is an involution
-- ===========================================================================

/-- **Involution.** `conjList (conjList σ) = σ` for positive partitions. -/
lemma conjList_involution (σ : List ℕ) (h : IsPosPart σ) :
    conjList (conjList σ) = σ := by
  apply List.ext_getElem (conjList_conjList_length σ h)
  intro j _ hj
  rw [conjList_getElem (conjList σ) j (by rw [conjList_conjList_length σ h]; exact hj)]
  exact countP_conjList_eq_get σ h j hj

-- ===========================================================================
-- Pointwise formula and the intermediate lemma
-- ===========================================================================

/-- Pointwise formula for `conjList`, in-range case. -/
lemma conjList_getD_of_lt (σ : List ℕ) (i : ℕ) (hi : i < σ.headD 0) :
    (conjList σ).getD i 0 = σ.countP (fun x => decide (i + 1 ≤ x)) := by
  unfold conjList
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp

/-- Pointwise formula for entries of `conjList`. -/
lemma conjList_getD_eq (σ : List ℕ) (hsort : σ.Pairwise (· ≥ ·)) (i : ℕ) :
    (conjList σ).getD i 0 = σ.countP (fun x => decide (i + 1 ≤ x)) := by
  by_cases h : i < σ.headD 0
  · exact conjList_getD_of_lt σ i h
  · push_neg at h
    have hlen : (conjList σ).length = σ.headD 0 := length_conjList σ
    rw [List.getD_eq_default _ _ (by omega),
        (List.countP_eq_zero (l := σ)).mpr (fun x hx => by
          have := all_le_headD σ hsort x hx
          simp; omega)]

/-- Discrete-derivative identity: difference of count gives `count`. -/
lemma countP_ge_diff_eq_count (σ : List ℕ) (k : ℕ) :
    σ.countP (fun x => decide (k ≤ x)) -
      σ.countP (fun x => decide (k + 1 ≤ x)) = σ.count k := by
  suffices key : σ.countP (fun x => decide (k ≤ x)) =
                 σ.count k + σ.countP (fun x => decide (k + 1 ≤ x)) by omega
  induction σ with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    grind

/-- **Intermediate lemma (the conjugation dictionary).** For any positive
partition `σ` and any positive integer `k`, the multiplicity of `k` in `σ`
equals `α[k-1] - α[k]` where `α = conjList σ`. -/
lemma intermediate_lemma_aux (σ : List ℕ) (h : IsPosPart σ)
    (k : ℕ) (hk : 1 ≤ k) :
    σ.count k =
      (conjList σ).getD (k - 1) 0 - (conjList σ).getD k 0 := by
  rw [conjList_getD_eq σ h.1 (k - 1), conjList_getD_eq σ h.1 k,
      Nat.sub_add_cancel hk]
  exact (countP_ge_diff_eq_count σ k).symm

lemma intermediate_lemma (_thm1 : Thm1) :
    ∀ σ : List ℕ, IsPosPart σ → ∀ k : ℕ, 1 ≤ k →
      σ.count k =
        (conjList σ).getD (k - 1) 0 - (conjList σ).getD k 0 :=
  intermediate_lemma_aux

-- ===========================================================================
-- Forward direction: σ ∈ setR N ⇒ conjList σ ∈ setF2 N
-- ===========================================================================

/-- 3-flatness of the conjugate from multiplicity bound. -/
lemma conjList_is3Flat (σ : List ℕ) (h_pos : IsPosPart σ)
    (h_mult : ∀ k, σ.count k ≤ 2) :
    Is3Flat (conjList σ) := by
  intro i _
  have h1 : σ.count (i + 1) = (conjList σ).getD i 0 - (conjList σ).getD (i + 1) 0 := by
    simpa using intermediate_lemma_aux σ h_pos (i + 1) (Nat.succ_le_succ (Nat.zero_le _))
  have h2 := h_mult (i + 1)
  omega
/-- If the head's residue mod 3 is nonzero, it's the first nonzero residue. -/
lemma firstNonzeroRes3_of_head_mod_ne_zero (α : List ℕ)
    (hα : α ≠ []) (h : α.headD 0 % 3 ≠ 0) :
    firstNonzeroRes3 α = some (α.headD 0 % 3) := by
  cases α with
  | nil => exact absurd rfl hα
  | cons a as => simp_all [firstNonzeroRes3, List.headD, List.find?]

/-- `firstNonzeroRes3` of conjugate when `σ.length % 3 = 2`. -/
lemma conjList_firstNonzeroRes3_case1 (σ : List ℕ)
    (h_pos : IsPosPart σ) (h_ne : σ ≠ [])
    (h_len : σ.length % 3 = 2) :
    firstNonzeroRes3 (conjList σ) = some 2 := by
  have h_headD_pos : 0 < σ.headD 0 := by
    cases σ with
    | nil => exact absurd rfl h_ne
    | cons a _ => exact h_pos.2 a (by simp)
  have h_len_conj : (conjList σ).length = σ.headD 0 := length_conjList σ
  have h_conj_ne : conjList σ ≠ [] := fun heq => by
    rw [heq, List.length_nil] at h_len_conj
    omega
  have h_count : σ.countP (fun x => decide (0 + 1 ≤ x)) = σ.length := by
    rw [List.countP_eq_length]
    intro x hx
    have := h_pos.2 x hx
    simp only [decide_eq_true_eq]
    omega
  have h_head_eq : (conjList σ).headD 0 = σ.length := by
    rcases h : conjList σ with _ | ⟨a, t⟩
    · exact absurd h h_conj_ne
    · have h0 := conjList_getD_of_lt σ 0 h_headD_pos
      rw [h] at h0
      simp only [List.headD_cons]
      rw [show a = σ.countP (fun x => decide (0 + 1 ≤ x)) from h0, h_count]
  rw [firstNonzeroRes3_of_head_mod_ne_zero (conjList σ) h_conj_ne
        (by rw [h_head_eq, h_len]; decide),
      h_head_eq, h_len]

/-- A positive partition with length divisible by 3 and nonempty has length ≥ 3. -/
lemma length_ge_three (σ : List ℕ) (h_ne : σ ≠ [])
    (h_len0 : σ.length % 3 = 0) : 3 ≤ σ.length := by
  have : 0 < σ.length := List.length_pos_of_ne_nil h_ne
  omega

/-- Smallest part is strictly less than largest part (case 2). -/
lemma getLastD_lt_headD_case2 (σ : List ℕ)
    (h_pos : IsPosPart σ) (h_ne : σ ≠ [])
    (h_len0 : σ.length % 3 = 0)
    (h_unique : σ.count (σ.getLastD 0) = 1) :
    σ.getLastD 0 < σ.headD 0 := by
  have h3 : 3 ≤ σ.length := length_ge_three σ h_ne h_len0
  by_contra hle
  push_neg at hle
  have hcount : σ.count (σ.getLastD 0) = σ.length :=
    List.count_eq_length.mpr fun x hx =>
      (le_antisymm ((all_le_headD σ h_pos.1 x hx).trans hle)
        (all_ge_getLastD σ h_pos.1 x hx)).symm
  rw [h_unique] at hcount
  omega

/-- Count of parts `≥ i+1` equals `σ.length` when `i < σ.getLastD 0`. -/
lemma countP_ge_eq_length_for_small (σ : List ℕ)
    (h_pos : IsPosPart σ) (i : ℕ) (hi : i < σ.getLastD 0) :
    σ.countP (fun x => decide (i + 1 ≤ x)) = σ.length := by
  apply List.countP_eq_length.mpr
  intro x hx
  have := all_ge_getLastD σ h_pos.1 x hx
  simp
  omega

/-- When the smallest part is unique, the count of parts `> smallest` is `length - 1`. -/
lemma countP_ge_smallest_succ (σ : List ℕ)
    (h_pos : IsPosPart σ) (h_ne : σ ≠ [])
    (h_unique : σ.count (σ.getLastD 0) = 1) :
    σ.countP (fun x => decide (σ.getLastD 0 + 1 ≤ x)) = σ.length - 1 := by
  set s := σ.getLastD 0 with hs_def
  have hs_pos : 0 < s := by
    have hmem : s ∈ σ := by
      rw [hs_def]
      simp [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h_ne,
            List.getLast_mem]
    exact h_pos.2 s hmem
  have h_all : σ.countP (fun x => decide (s ≤ x)) = σ.length := by
    have h := countP_ge_eq_length_for_small σ h_pos (s - 1) (by omega)
    rwa [Nat.sub_add_cancel hs_pos] at h
  have h_diff := countP_ge_diff_eq_count σ s
  rw [h_all, h_unique] at h_diff
  have : σ.countP (fun x => decide (s + 1 ≤ x)) ≤ σ.length := List.countP_le_length
  omega

/-- `(conjList σ).take s = replicate s σ.length` for `s = σ.getLastD 0`. -/
lemma take_conjList_eq_replicate (σ : List ℕ)
    (h_pos : IsPosPart σ) (h_ne : σ ≠ [])
    (h_len0 : σ.length % 3 = 0)
    (h_unique : σ.count (σ.getLastD 0) = 1) :
    (conjList σ).take (σ.getLastD 0) =
      List.replicate (σ.getLastD 0) σ.length := by
  set s := σ.getLastD 0
  have hs_lt : s < σ.headD 0 :=
    getLastD_lt_headD_case2 σ h_pos h_ne h_len0 h_unique
  have hlen : (conjList σ).length = σ.headD 0 := length_conjList σ
  have hs_le : s ≤ (conjList σ).length := hlen ▸ Nat.le_of_lt hs_lt
  apply List.ext_getElem
  · rw [List.length_take, List.length_replicate]; exact min_eq_left hs_le
  · intro i hi1 _
    have hi_s : i < s := by rw [List.length_take] at hi1; omega
    have hi_head : i < σ.headD 0 := lt_of_lt_of_le hi_s (Nat.le_of_lt hs_lt)
    have hi_len : i < (conjList σ).length := hlen ▸ hi_head
    rw [List.getElem_replicate, List.getElem_take,
        ← List.getD_eq_getElem _ _ hi_len, conjList_getD_of_lt σ i hi_head,
        countP_ge_eq_length_for_small σ h_pos i hi_s]

/-- `conjList σ` decomposes as `replicate s σ.length ++ (σ.length - 1) :: rest`
under case-2 hypotheses, where `s = σ.getLastD 0`. -/
lemma conjList_decomp_case2 (σ : List ℕ)
    (h_pos : IsPosPart σ) (h_ne : σ ≠ [])
    (h_len0 : σ.length % 3 = 0)
    (h_unique : σ.count (σ.getLastD 0) = 1) :
    ∃ rest : List ℕ,
      conjList σ = List.replicate (σ.getLastD 0) σ.length
                 ++ (σ.length - 1) :: rest := by
  set s := σ.getLastD 0
  have hs_lt_head : s < σ.headD 0 :=
    getLastD_lt_headD_case2 σ h_pos h_ne h_len0 h_unique
  have hlen : (conjList σ).length = σ.headD 0 := length_conjList σ
  have hs_lt_clen : s < (conjList σ).length := hlen ▸ hs_lt_head
  have h_getElem_s : (conjList σ)[s]'hs_lt_clen = σ.length - 1 := by
    rw [← List.getD_eq_getElem _ _ hs_lt_clen, conjList_getD_of_lt σ s hs_lt_head]
    exact countP_ge_smallest_succ σ h_pos h_ne h_unique
  refine ⟨(conjList σ).drop (s + 1), ?_⟩
  calc conjList σ
      = (conjList σ).take s ++ (conjList σ).drop s :=
        (List.take_append_drop s (conjList σ)).symm
    _ = (conjList σ).take s ++
          ((conjList σ)[s]'hs_lt_clen :: (conjList σ).drop (s + 1)) := by
        rw [(@List.getElem_cons_drop ℕ (conjList σ) s hs_lt_clen).symm]
    _ = List.replicate s σ.length ++ ((σ.length - 1) :: (conjList σ).drop (s + 1)) := by
        rw [take_conjList_eq_replicate σ h_pos h_ne h_len0 h_unique, h_getElem_s]

/-- `firstNonzeroRes3` of conjugate when `σ.length % 3 = 0` with unique smallest part. -/
lemma conjList_firstNonzeroRes3_case2 (σ : List ℕ)
    (h_pos : IsPosPart σ) (h_ne : σ ≠ [])
    (h_len0 : σ.length % 3 = 0)
    (h_unique : σ.count (σ.getLastD 0) = 1) :
    firstNonzeroRes3 (conjList σ) = some 2 := by
  have hlen3 : 3 ≤ σ.length := length_ge_three σ h_ne h_len0
  have hmod : (σ.length - 1) % 3 = 2 := by omega
  obtain ⟨rest, hdec⟩ :=
    conjList_decomp_case2 σ h_pos h_ne h_len0 h_unique
  unfold firstNonzeroRes3
  rw [hdec,
    show (List.replicate (σ.getLastD 0) σ.length ++ (σ.length - 1) :: rest).find?
        (fun x => decide (x % 3 ≠ 0)) = some (σ.length - 1) from by grind]
  show some ((σ.length - 1) % 3) = some 2
  rw [hmod]

/-- **Forward direction.** If `σ ∈ setR N`, then `conjList σ ∈ setF2 N`. -/
lemma conjList_forward (N : ℕ) (σ : List ℕ) (h : σ ∈ setR N) :
    conjList σ ∈ setF2 N := by
  obtain ⟨h_pos, h_wt, h_ne, h_mult, h_len⟩ := h
  refine ⟨conjList_isPosPart σ h_pos, conjList_weight σ h_pos ▸ h_wt,
    conjList_is3Flat σ h_pos h_mult, ?_⟩
  rcases h_len with h2 | ⟨h0, hu⟩
  · exact conjList_firstNonzeroRes3_case1 σ h_pos h_ne h2
  · exact conjList_firstNonzeroRes3_case2 σ h_pos h_ne h0 hu

-- ===========================================================================
-- Backward direction: α ∈ setF2 N ⇒ conjList α ∈ setR N
-- ===========================================================================

/-- `firstNonzeroRes3 α = some r` implies `α ≠ []`. -/
lemma ne_nil_of_firstNonzeroRes3_some (α : List ℕ) (r : ℕ)
    (h : firstNonzeroRes3 α = some r) : α ≠ [] := by
  rintro rfl
  simp [firstNonzeroRes3] at h

lemma headD_pos_of_isPosPart_ne_nil (α : List ℕ)
    (hpos : IsPosPart α) (hne : α ≠ []) : 0 < α.headD 0 := by
  cases α with
  | nil => exact absurd rfl hne
  | cons a _ => exact hpos.2 a (by simp)

/-- **Multiplicity bound for `conjList α`** under 3-flatness. -/
lemma conjList_count_le_two (α : List ℕ)
    (hpos : IsPosPart α) (hflat : Is3Flat α) :
    ∀ k, (conjList α).count k ≤ 2 := by
  intro k
  have hσpos : IsPosPart (conjList α) := conjList_isPosPart α hpos
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp [List.count_eq_zero.mpr (fun h0 => absurd (hσpos.2 0 h0) (lt_irrefl 0))]
  · rw [intermediate_lemma_aux (conjList α) hσpos k hk1, conjList_involution α hpos]
    by_cases hkα : k - 1 < α.length
    · have := hflat (k - 1) hkα
      rw [Nat.sub_add_cancel hk1] at this
      omega
    · push_neg at hkα
      rw [List.getD_eq_default _ _ hkα,
          List.getD_eq_default _ _ (le_trans hkα (Nat.sub_le k 1))]
      omega

/-- Extract the first nonzero-residue index `s` of `α`. -/
lemma exists_s_index (α : List ℕ) (_hpos : IsPosPart α)
    (hres : firstNonzeroRes3 α = some 2) (h0 : α.headD 0 % 3 = 0) :
    ∃ s : ℕ, 1 ≤ s ∧ s < α.length ∧ α.getD s 0 % 3 = 2 ∧
      (∀ j < s, α.getD j 0 % 3 = 0) := by
  unfold firstNonzeroRes3 at hres
  rw [Option.map_eq_some_iff] at hres
  obtain ⟨y, hfind, hy⟩ := hres
  rw [List.find?_eq_some_iff_getElem] at hfind
  obtain ⟨_, s, hslen, hys, hmin⟩ := hfind
  refine ⟨s, ?_, hslen, ?_, ?_⟩
  · by_contra hne
    push_neg at hne
    interval_cases s
    have hh : α.headD 0 = α[0] := by
      cases α with
      | nil => simp at hslen
      | cons a t => simp
    rw [hh, hys, hy] at h0
    exact absurd h0 (by decide)
  · rw [List.getD_eq_getElem _ _ hslen, hys]
    exact hy
  · intro j hj
    rw [List.getD_eq_getElem _ _ (lt_trans hj hslen)]
    have := hmin j hj
    simp at this
    omega

/-- Two consecutive parts both divisible by 3 are equal under `Is3Flat`. -/
lemma eq_of_consecutive_div3 (α : List ℕ) (hpos : IsPosPart α) (hflat : Is3Flat α)
    (j : ℕ) (hjα : j < α.length)
    (hj : α.getD j 0 % 3 = 0) (hj1 : α.getD (j+1) 0 % 3 = 0) :
    α.getD j 0 = α.getD (j+1) 0 := by
  have hge : α.getD (j + 1) 0 ≤ α.getD j 0 := by
    rcases lt_or_ge (j + 1) α.length with hj1' | hj1'
    · rw [List.getD_eq_getElem _ _ hjα, List.getD_eq_getElem _ _ hj1']
      exact List.pairwise_iff_getElem.mp hpos.1 j (j + 1) hjα hj1' (Nat.lt_succ_self j)
    · rw [List.getD_eq_default _ _ hj1']; exact Nat.zero_le _
  have hflat_j := hflat j hjα
  omega

/-- For `j ≤ s` with all residues 0 below `s`, `α.getD j 0 = α.headD 0` (unless `j = s`). -/
lemma getD_eq_headD_lt_s (α : List ℕ) (hpos : IsPosPart α) (hflat : Is3Flat α)
    (s : ℕ) (hs : s < α.length)
    (hzero : ∀ j < s, α.getD j 0 % 3 = 0) :
    ∀ j ≤ s, j < α.length → α.getD j 0 = α.headD 0 ∨ j = s := by
  intro j
  induction j with
  | zero =>
    intro _ hjα
    cases α with
    | nil => simp at hjα
    | cons a l => exact Or.inl rfl
  | succ k ih =>
    intro hjs hjα
    by_cases hk : k + 1 = s
    · exact Or.inr hk
    have hk1_lt_s : k + 1 < s := lt_of_le_of_ne hjs hk
    have hkα : k < α.length := by omega
    rcases ih (by omega) hkα with hk_res | hk_eq_s
    · refine Or.inl ?_
      rw [← eq_of_consecutive_div3 α hpos hflat k hkα (hzero k (by omega))
            (hzero (k+1) hk1_lt_s), hk_res]
    · omega

/-- Difference equals 1 under residue + 3-flatness. -/
lemma diff_eq_one_of_residues (α : List ℕ) (hpos : IsPosPart α) (hflat : Is3Flat α)
    (s : ℕ) (hs1 : 1 ≤ s) (hs : s < α.length)
    (hsm : α.getD (s-1) 0 = α.headD 0) (h0 : α.headD 0 % 3 = 0)
    (hsr : α.getD s 0 % 3 = 2) :
    α.getD (s-1) 0 - α.getD s 0 = 1 := by
  have hps_lt : s - 1 < α.length := by omega
  have hge : α.getD s 0 ≤ α.getD (s - 1) 0 := by
    rw [List.getD_eq_getElem _ _ hps_lt, List.getD_eq_getElem _ _ hs]
    simpa using List.pairwise_iff_get.mp hpos.1 ⟨s - 1, hps_lt⟩ ⟨s, hs⟩ (by simp; omega)
  have hflat' : α.getD (s - 1) 0 - α.getD s 0 < 3 := by
    have := hflat (s - 1) hps_lt
    rwa [show (s - 1) + 1 = s by omega] at this
  have hsm0 : α.getD (s - 1) 0 % 3 = 0 := hsm ▸ h0
  omega

/-- Strict inequality `α.getD s 0 < α.headD 0` from differing residues. -/
lemma getD_s_lt_headD (α : List ℕ) (hpos : IsPosPart α)
    (s : ℕ) (hs : s < α.length)
    (h0 : α.headD 0 % 3 = 0) (hsr : α.getD s 0 % 3 = 2) :
    α.getD s 0 < α.headD 0 := by
  have hle : α.getD s 0 ≤ α.headD 0 := by
    cases α with
    | nil => simp at hs
    | cons a as =>
      cases s with
      | zero => simp [List.getD, List.headD]
      | succ s' =>
        have hs' : s' + 1 < (a :: as).length := hs
        rw [List.headD_cons,
            show ((a :: as).getD (s' + 1) 0) = (a :: as)[s' + 1]
              from List.getD_eq_getElem _ _ hs']
        simpa using List.pairwise_iff_getElem.mp hpos.1 0 (s' + 1)
          (by simp) hs' (by omega)
  omega

/-- Express the last element of `conjList α` as a `countP` over `α`. -/
lemma getLastD_conjList_as_countP (α : List ℕ)
    (hpos : IsPosPart α) (hne : α ≠ []) :
    (conjList α).getLastD 0 =
      α.countP (fun x => decide (α.headD 0 ≤ x)) := by
  have hhead : 0 < α.headD 0 := headD_pos_of_isPosPart_ne_nil α hpos hne
  have hlen : (conjList α).length = α.headD 0 := length_conjList α
  have hne' : conjList α ≠ [] := fun h => by
    rw [h, List.length_nil] at hlen; omega
  have hidx : α.headD 0 - 1 < α.headD 0 := by omega
  have hgL : (conjList α).getLastD 0 = (conjList α).getD ((conjList α).length - 1) 0 := by
    rcases hcl : conjList α with _ | ⟨h, t⟩
    · exact (hne' hcl).elim
    · rw [List.getLastD_eq_getLast?, List.getD_eq_getElem _ _ (by simp),
          List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp)]
      simp
  rw [hgL, hlen, conjList_getD_of_lt α (α.headD 0 - 1) hidx,
      Nat.sub_add_cancel hhead]

/-- The count of elements `≥ α.headD 0` in `α` equals `s`. -/
lemma countP_headD_eq_s (α : List ℕ) (hp : α.Pairwise (· ≥ ·))
    (s : ℕ) (hs1 : 1 ≤ s) (hs : s < α.length)
    (heq : ∀ j < s, α.getD j 0 = α.headD 0)
    (hlt : α.getD s 0 < α.headD 0) :
    α.countP (fun x => decide (α.headD 0 ≤ x)) = s := by
  have hs1_lt : s - 1 < α.length := by omega
  have hsm1_eq : α[s - 1]'hs1_lt = α.headD 0 := by
    have h1 := heq (s - 1) (by omega)
    rwa [List.getD_eq_getElem _ _ hs1_lt] at h1
  have hs_lt_head : α[s]'hs < α.headD 0 := by
    rwa [List.getD_eq_getElem _ _ hs] at hlt
  have hge : s ≤ α.countP (fun x => decide (α.headD 0 ≤ x)) := by
    have := countP_ge_of_sorted α hp (s - 1) hs1_lt (α.headD 0) (le_of_eq hsm1_eq.symm)
    rwa [Nat.sub_add_cancel hs1] at this
  exact le_antisymm (countP_lt_of_sorted α hp s hs (α.headD 0) hs_lt_head) hge

/-- Main combinatorial step for `headD % 3 = 0` case: uniqueness of smallest part of `conjList α`. -/
lemma conjList_count_lastD_eq_one_div3 (α : List ℕ)
    (hpos : IsPosPart α) (hflat : Is3Flat α)
    (hres : firstNonzeroRes3 α = some 2) (h0 : α.headD 0 % 3 = 0) :
    (conjList α).count ((conjList α).getLastD 0) = 1 := by
  obtain ⟨s, hs1, hs, hsr, hzero⟩ := exists_s_index α hpos hres h0
  have heq : ∀ j < s, α.getD j 0 = α.headD 0 := fun j hj => by
    have hjα : j < α.length := lt_trans hj hs
    rcases getD_eq_headD_lt_s α hpos hflat s hs hzero j (le_of_lt hj) hjα with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hj)
  have hsm : α.getD (s-1) 0 = α.headD 0 := heq (s - 1) (by omega)
  have hlt : α.getD s 0 < α.headD 0 := getD_s_lt_headD α hpos s hs h0 hsr
  have hne : α ≠ [] := ne_nil_of_firstNonzeroRes3_some α 2 hres
  have hlast : (conjList α).getLastD 0 = s := by
    rw [getLastD_conjList_as_countP α hpos hne]
    exact countP_headD_eq_s α hpos.1 s hs1 hs heq hlt
  have hint := intermediate_lemma_aux (conjList α) (conjList_isPosPart α hpos) s hs1
  rw [conjList_involution α hpos] at hint
  rw [hlast, hint]
  exact diff_eq_one_of_residues α hpos hflat s hs1 hs hsm h0 hsr

/-- Length condition for the backward direction. -/
lemma conjList_length_condition (α : List ℕ)
    (hpos : IsPosPart α) (hflat : Is3Flat α)
    (hres : firstNonzeroRes3 α = some 2) :
    (conjList α).length % 3 = 2 ∨
    ((conjList α).length % 3 = 0 ∧
     (conjList α).count ((conjList α).getLastD 0) = 1) := by
  have hα : α ≠ [] := ne_nil_of_firstNonzeroRes3_some α 2 hres
  have hlen : (conjList α).length = α.headD 0 := length_conjList α
  by_cases h2 : α.headD 0 % 3 = 2
  · exact Or.inl (hlen ▸ h2)
  by_cases h1 : α.headD 0 % 3 = 1
  · exfalso
    have hfn := firstNonzeroRes3_of_head_mod_ne_zero α hα (by omega)
    rw [h1, hres] at hfn
    injection hfn with h_eq
    omega
  · have h0 : α.headD 0 % 3 = 0 := by omega
    exact Or.inr ⟨hlen ▸ h0, conjList_count_lastD_eq_one_div3 α hpos hflat hres h0⟩

/-- **Backward direction.** If `α ∈ setF2 N`, then `conjList α ∈ setR N`. -/
lemma conjList_backward (N : ℕ) (α : List ℕ) (h : α ∈ setF2 N) :
    conjList α ∈ setR N := by
  obtain ⟨hpos, hwt, hflat, hres⟩ := h
  have hne : α ≠ [] := ne_nil_of_firstNonzeroRes3_some α 2 hres
  have hhead : 0 < α.headD 0 := headD_pos_of_isPosPart_ne_nil α hpos hne
  have hlenσ : (conjList α).length = α.headD 0 := length_conjList α
  refine ⟨conjList_isPosPart α hpos, conjList_weight α hpos ▸ hwt, ?_,
    conjList_count_le_two α hpos hflat,
    conjList_length_condition α hpos hflat hres⟩
  intro heq
  rw [heq, List.length_nil] at hlenσ
  omega

-- ===========================================================================
-- Main theorem
-- ===========================================================================

theorem lem_conj (_thm1 : Thm1) (N : ℕ) :
    Set.BijOn conjList (setR N) (setF2 N) := by
  refine ⟨conjList_forward N, fun σ₁ h₁ σ₂ h₂ heq => ?_, fun α hα =>
    ⟨conjList α, conjList_backward N α hα, conjList_involution α hα.1⟩⟩
  rw [← conjList_involution σ₁ h₁.1, heq, conjList_involution σ₂ h₂.1]

end AndrewsDhar
