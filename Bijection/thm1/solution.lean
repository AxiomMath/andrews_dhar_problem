import Mathlib

namespace AndrewsDharD3

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

/-! ## Finiteness and basic structure of `D3Set` -/

/-- Every part of `μ ∈ D3Set n` is bounded by `n`. -/
lemma D3Set_parts_le (n : ℕ) (μ : List ℕ) (hμ : μ ∈ D3Set n)
    (x : ℕ) (hx : x ∈ μ) : x ≤ n := by
  have hsum : μ.sum = n := hμ.1.2
  have hle : x ≤ μ.sum := List.single_le_sum (by intros; exact Nat.zero_le _) _ hx
  omega

lemma smallestPart_le_of_mem_aux (μ : List ℕ) (hne : μ ≠ []) (x : ℕ) (hx : x ∈ μ) :
    smallestPart μ ≤ x := by
  unfold smallestPart
  cases hm : μ.min? with
  | none =>
    rw [List.min?_eq_none_iff] at hm
    subst hm
    simp at hx
  | some m =>
    simp
    rw [List.min?_eq_some_iff] at hm
    exact hm.2 x hx

lemma length_le_sum_add_three_of_count_zero (μ : List ℕ) (hcount : μ.count 0 = 3) :
    μ.length ≤ μ.sum + 3 := by
  have h_general : ∀ (l : List ℕ), l.length ≤ l.sum + l.count 0 := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      by_cases hx : x = 0
      · simp_all [List.length, List.sum_cons]
        omega
      · have hx' : x ≥ 1 := Nat.pos_of_ne_zero hx
        simp_all [List.length, List.sum_cons]
        omega
  have h₁ : μ.length ≤ μ.sum + μ.count 0 := h_general μ
  omega

lemma length_le_sum_add_three (μ : List ℕ) (hne : μ ≠ [])
    (hcount : μ.count (smallestPart μ) = 3) :
    μ.length ≤ μ.sum + 3 := by
  by_cases hs : smallestPart μ = 0
  · rw [hs] at hcount
    exact length_le_sum_add_three_of_count_zero μ hcount
  · have hs1 : 1 ≤ smallestPart μ := Nat.one_le_iff_ne_zero.mpr hs
    have hall : ∀ x ∈ μ, 1 ≤ x := by
      intro x hx
      have hxle := smallestPart_le_of_mem_aux μ hne x hx
      omega
    have hlen : μ.length ≤ μ.sum := List.length_le_sum_of_one_le μ hall
    omega

lemma D3Set_length_le (n : ℕ) (μ : List ℕ) (hμ : μ ∈ D3Set n) :
    μ.length ≤ n + 3 := by
  obtain ⟨⟨_, hsum⟩, hne, hcount, _⟩ := hμ
  have := length_le_sum_add_three μ hne hcount
  omega

lemma list_finite_of_length_eq (k N : ℕ) :
    {l : List ℕ | l.length = k ∧ ∀ x ∈ l, x ≤ N}.Finite := by
  let φ : (Fin k → Fin (N+1)) → List ℕ := fun f => List.ofFn (fun i => (f i).val)
  have hsub : {l : List ℕ | l.length = k ∧ ∀ x ∈ l, x ≤ N} ⊆ Set.range φ := by
    intro l hl
    obtain ⟨hlen, hbd⟩ := hl
    refine ⟨fun i => ⟨l.get (i.cast hlen.symm), ?_⟩, ?_⟩
    · have hmem : l.get (i.cast hlen.symm) ∈ l := List.get_mem _ _
      exact Nat.lt_succ_of_le (hbd _ hmem)
    · subst hlen
      simp [φ]
  have hfin : (Set.range φ).Finite := Set.finite_range φ
  exact hfin.subset hsub

lemma list_finite_bounded (L N : ℕ) :
    {l : List ℕ | l.length ≤ L ∧ ∀ x ∈ l, x ≤ N}.Finite := by
  have heq : {l : List ℕ | l.length ≤ L ∧ ∀ x ∈ l, x ≤ N} =
      ⋃ k ∈ Set.Iic L, {l : List ℕ | l.length = k ∧ ∀ x ∈ l, x ≤ N} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, exists_prop]
    constructor
    · rintro ⟨hlen, hle⟩
      exact ⟨l.length, hlen, rfl, hle⟩
    · rintro ⟨k, hkL, hlen, hle⟩
      exact ⟨hlen ▸ hkL, hle⟩
  rw [heq]
  exact (Set.finite_Iic L).biUnion (fun k _ => list_finite_of_length_eq k N)

lemma D3Set_finite (n : ℕ) : (D3Set n).Finite := by
  apply (list_finite_bounded (n + 3) n).subset
  intro μ hμ
  exact ⟨D3Set_length_le n μ hμ, fun x hx => D3Set_parts_le n μ hμ x hx⟩

/-- `D3Set n` is the union of its three residue-class subsets, since for any
`μ ∈ D3Set n` the value `tau μ % 3` is one of `0, 1, 2`. -/
lemma D3Set_eq_union (n : ℕ) :
    D3Set n = D3iSet 0 n ∪ D3iSet 1 n ∪ D3iSet 2 n := by
  ext μ
  simp only [Set.mem_union]
  constructor
  · intro hμ
    have hD3 : IsD3Partition μ n := hμ
    have h3 : tau μ % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : (tau μ % 3) <;> simp_all [D3iSet]
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h

/-- Distinct residue classes are disjoint. -/
lemma D3iSet_disjoint_of_ne (n : ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    Disjoint (D3iSet i n) (D3iSet j n) := by
  rw [Set.disjoint_iff]
  intro μ ⟨⟨_, hi'⟩, ⟨_, hj'⟩⟩
  rw [Nat.mod_eq_of_lt hi] at hi'
  rw [Nat.mod_eq_of_lt hj] at hj'
  exact absurd (hi'.symm.trans hj') hij
/-- A primitive cube root of unity exists in `ℂ`: there is `ω : ℂ` with
`ω^3 = 1` and `ω ≠ 1`. One choice is `Complex.exp (2 * Real.pi * Complex.I / 3)`. -/
lemma exists_primitive_cube_root : ∃ ω : ℂ, ω^3 = 1 ∧ ω ≠ 1 := by
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / 3), ?_, ?_⟩
  · rw [← Complex.exp_nat_mul]
    rw [show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by
      push_cast; ring]
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by ring⟩
  · intro h
    have him : (Complex.exp (2 * Real.pi * Complex.I / 3)).im = 0 := by
      rw [h]; simp
    rw [Complex.exp_im] at him
    have hsin_pos : Real.sin (2 * Real.pi / 3) > 0 := by
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
        show Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 by norm_num]
      have : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    simp at him
    nlinarith [him, hsin_pos, Real.exp_pos (Complex.re (2 * Real.pi * Complex.I / 3))]


/-- The generating polynomial `G_ω(q) := ∑_{s=0}^N q^{3s} ∏_{r=s+1}^N (1 + ω q^r + ω² q^{2r})`
in `ℂ[q]`. Its `n`-th coefficient encodes the finite weighted sum
`∑_{μ ∈ D3Set n} ω^(tau μ)`. -/
noncomputable def G_omega (ω : ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ s ∈ Finset.range (N + 1),
    Polynomial.X ^ (3 * s) *
      ∏ r ∈ Finset.Ioc s N,
        (1 + Polynomial.C ω * Polynomial.X ^ r +
              Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r))

/-- The explicit `(s, f)`-sum that the algebraic expansion reduces `(G_omega ω n).coeff n` to. -/
noncomputable def coeffSum (n : ℕ) (ω : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (n + 1),
    ∑ f ∈ ((Fintype.piFinset
              (fun _ : ↥(Finset.Ioc s n) => (Finset.univ : Finset (Fin 3)))).filter
        (fun f => 3 * s + ∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val = n)),
      ω ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val)

/-- The "Euler-side" polynomial obtained after the q-series manipulations. Explicitly,
`H_poly ω n = ∑_{k=0}^{n} C ((-1)^k * ω^{2k}) * X^{triangular k}
              * (1 - X^{k+1}) * (1 - X^{k+2})`. -/
noncomputable def H_poly (ω : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
      Polynomial.X ^ (triangular k) *
      (1 - Polynomial.X ^ (k + 1)) *
      (1 - Polynomial.X ^ (k + 2))

/-! ## Generating polynomial machinery -/

/-- For each choice function `f`, the product
`∏ r ∈ (Finset.Ioc s n).attach, (C(ω^(f r).val) * X^((f r).val * r.val))`
simplifies to `C(ω^∑r (f r).val) * X^(∑r (f r).val * r.val)`. -/
lemma prod_term_simp (s n : ℕ) (ω : ℂ)
    (f : ↥(Finset.Ioc s n) → Fin 3) :
    ∏ r ∈ (Finset.Ioc s n).attach,
        (Polynomial.C (ω ^ (f r).val) * Polynomial.X ^ ((f r).val * r.val)) =
    Polynomial.C (ω ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val)) *
      Polynomial.X ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← map_prod]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
  · rw [← Finset.prod_pow_eq_pow_sum]

/-- Each local factor as a sum over `Fin 3`. -/
lemma factor_eq_sum_fin_three (ω : ℂ) (r : ℕ) :
    (1 + Polynomial.C ω * Polynomial.X ^ r +
        Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r) : Polynomial ℂ) =
    ∑ i : Fin 3, Polynomial.C (ω ^ (i.val)) * Polynomial.X ^ ((i.val) * r) := by
  rw [Fin.sum_univ_three]
  simp [pow_zero, pow_one, zero_mul, one_mul, Polynomial.C_1]

lemma prod_sum_swap_pifinset (s n : ℕ) (ω : ℂ) :
    (∏ r ∈ (Finset.Ioc s n).attach,
        ∑ i : Fin 3, Polynomial.C (ω ^ i.val) * Polynomial.X ^ (i.val * r.val)) =
    ∑ f ∈ Fintype.piFinset (fun _ : ↥(Finset.Ioc s n) => (Finset.univ : Finset (Fin 3))),
      ∏ r ∈ (Finset.Ioc s n).attach,
        Polynomial.C (ω ^ (f r).val) * Polynomial.X ^ ((f r).val * r.val) := by
  exact Finset.prod_univ_sum (fun _ : ↥(Finset.Ioc s n) => (Finset.univ : Finset (Fin 3)))
    (fun r i => Polynomial.C (ω ^ i.val) * Polynomial.X ^ (i.val * r.val))

lemma prod_factors_eq_sum_pifinset (s n : ℕ) (ω : ℂ) :
    (∏ r ∈ Finset.Ioc s n,
        (1 + Polynomial.C ω * Polynomial.X ^ r +
              Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r))) =
    ∑ f ∈ Fintype.piFinset (fun _ : ↥(Finset.Ioc s n) => (Finset.univ : Finset (Fin 3))),
      Polynomial.C (ω ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val)) *
        Polynomial.X ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val) := by
  rw [← Finset.prod_attach (Finset.Ioc s n)
      (fun r => (1 + Polynomial.C ω * Polynomial.X ^ r +
                Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r) : Polynomial ℂ))]
  rw [show (∏ r ∈ (Finset.Ioc s n).attach,
            (1 + Polynomial.C ω * Polynomial.X ^ r.val +
              Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r.val) : Polynomial ℂ))
        = ∏ r ∈ (Finset.Ioc s n).attach,
            ∑ i : Fin 3, Polynomial.C (ω ^ i.val) * Polynomial.X ^ (i.val * r.val) from
      Finset.prod_congr rfl (fun r _ => factor_eq_sum_fin_three ω r.val)]
  rw [prod_sum_swap_pifinset s n ω]
  apply Finset.sum_congr rfl
  intro f _
  exact prod_term_simp s n ω f

lemma coeff_X_pow_mul_C_mul_X_pow_eq (n s m : ℕ) (c : ℂ) :
    (Polynomial.X ^ (3 * s) * (Polynomial.C c * Polynomial.X ^ m)).coeff n =
      c * (if 3 * s + m = n then 1 else 0) := by
  rw [show Polynomial.X ^ (3 * s) * (Polynomial.C c * Polynomial.X ^ m)
        = Polynomial.C c * Polynomial.X ^ (3 * s + m) by ring]
  grind

/-- For each filtered piFinset over Fin 3 (after expansion using `factor_eq_sum_three`
and `Finset.prod_univ_sum`), the `n`-th coefficient of the polynomial
`X^(3*s) * ∏ r (...)` equals an indicator sum over all functions. -/
lemma coeff_eq_indicator_sum (n s : ℕ) (ω : ℂ) :
    (Polynomial.X ^ (3 * s) *
        ∏ r ∈ Finset.Ioc s n,
          (1 + Polynomial.C ω * Polynomial.X ^ r +
                Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r))).coeff n =
    ∑ f ∈ Fintype.piFinset
            (fun _ : ↥(Finset.Ioc s n) => (Finset.univ : Finset (Fin 3))),
      ω ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val) *
        (if 3 * s + ∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val = n then 1 else 0) := by
  rw [prod_factors_eq_sum_pifinset s n ω, Finset.mul_sum, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro f _hf
  exact coeff_X_pow_mul_C_mul_X_pow_eq n s
    (∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val)
    (ω ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val))

/-- The `n`-th coefficient of the per-term polynomial equals an explicit
filtered sum over choice functions `f : ↥(Finset.Ioc s n) → Fin 3`. -/
lemma coeff_G_omega_term_eq_filtered_sum (n s : ℕ) (ω : ℂ) :
    (Polynomial.X ^ (3 * s) *
        ∏ r ∈ Finset.Ioc s n,
          (1 + Polynomial.C ω * Polynomial.X ^ r +
                Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r))).coeff n =
    ∑ f ∈ ((Fintype.piFinset
              (fun _ : ↥(Finset.Ioc s n) => (Finset.univ : Finset (Fin 3)))).filter
        (fun f => 3 * s + ∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val = n)),
      ω ^ (∑ r ∈ (Finset.Ioc s n).attach, (f r).val) := by
  rw [coeff_eq_indicator_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : 3 * s + ∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val = n
  · simp [hf]
  · simp [hf]

/-- The **inverse map**: given a base `s` and multiplicity function
`f : ↥(Ioc s n) → Fin 3`, build the list with each `r ∈ Ioc s n` repeated
`(f r).val` times in descending order, followed by three copies of `s`. -/
noncomputable def fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) : List ℕ :=
  (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
    (fun r => List.replicate
      (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r))
  ++ List.replicate 3 s

/-- The **forward map** (multiplicities): for `μ` a list and a base `s`,
record how many times each `r ∈ Ioc s n` occurs in `μ`. The codomain is
`Fin 3` because, for `D₃`-partitions, counts of parts strictly larger than the
smallest part are at most `2`. The total function uses `0` as a fallback when
the count would not fit. -/
noncomputable def toCounts (μ : List ℕ) (s n : ℕ) :
    ↥(Finset.Ioc s n) → Fin 3 :=
  fun r => if h : μ.count r.val < 3 then ⟨μ.count r.val, h⟩ else 0

/-! ## Helper Lemmas for the inverse map -/

/-- For `r ∈ Ioc s n`, we have `s < r.val`, so `(List.replicate 3 s).count r.val = 0`. -/
lemma count_replicate_part_zero (s n : ℕ) (r : ↥(Finset.Ioc s n)) :
    (List.replicate 3 s).count r.val = 0 := by
  have hr : s < r.val := (Finset.mem_Ioc.mp r.property).1
  rw [List.count_replicate]
  simp [Nat.ne_of_lt hr]

lemma sum_map_sort_eq_sum (s n : ℕ) (g : ℕ → ℕ) :
    (((Finset.Ioc s n).sort (· ≥ ·)).map g).sum = ∑ a ∈ Finset.Ioc s n, g a := by
  rw [((Finset.sort_perm_toList _ _).map g).sum_eq, Finset.sum_map_toList]

/-- Helper: count of `r.val` in flatMap over sorted Ioc, replicating each element. -/
lemma count_flatMap_part_eq (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3)
    (r : ↥(Finset.Ioc s n)) :
    (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
      (fun a => List.replicate
        (if h : a ∈ Finset.Ioc s n then (f ⟨a, h⟩).val else 0) a)).count r.val
      = (f r).val := by
  rw [List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate]
  rw [sum_map_sort_eq_sum]
  have hrmem : r.val ∈ Finset.Ioc s n := r.property
  rw [Finset.sum_eq_single r.val]
  · simp only [hrmem, dif_pos, beq_self_eq_true, if_true]
  · intro b _ hbne
    have : (b == r.val) = false := by simp [hbne]
    simp [this]
  · intro h
    exact absurd hrmem h

/-- For each `r ∈ Ioc s n`, the count of `r.val` in `fromPair s n f` equals `(f r).val`. -/
lemma count_fromPair_eq (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3)
    (r : ↥(Finset.Ioc s n)) :
    (fromPair s n f).count r.val = (f r).val := by
  unfold fromPair
  rw [List.count_append, count_flatMap_part_eq s n f r,
      count_replicate_part_zero s n r, Nat.add_zero]

/-- `fromPair s n f` ends with `List.replicate 3 s` which is nonempty,
so the whole list is nonempty. -/
lemma fromPair_ne_nil (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    fromPair s n f ≠ [] := by
  unfold fromPair
  intro h
  have hlen_append := congrArg List.length h
  simp [List.length_append] at hlen_append

lemma fromPair_partA_pairwise_ge (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
      (fun r => List.replicate
        (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r)).Pairwise (· ≥ ·) := by
  have h₁ : (((Finset.Ioc s n).sort (· ≥ ·)).Pairwise (· ≥ ·)) :=
    Finset.pairwise_sort _ _
  have h₂ : ∀ (r : ℕ), (List.replicate
      (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r).Pairwise (· ≥ ·) := by
    intro r
    exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  grind

lemma fromPair_partA_elt_gt_1 (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3)
    (x : ℕ)
    (hx : x ∈ (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
      (fun r => List.replicate
        (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r))) :
    s < x := by
  rw [List.mem_flatMap] at hx
  obtain ⟨r, hr_mem, hx_in⟩ := hx
  rw [Finset.mem_sort] at hr_mem
  rw [List.mem_replicate] at hx_in
  have : x = r := hx_in.2
  subst this
  exact (Finset.mem_Ioc.mp hr_mem).1

/-- The list `fromPair s n f` is sorted in weakly descending order. -/
lemma fromPair_pairwise_ge (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    (fromPair s n f).Pairwise (· ≥ ·) := by
  unfold fromPair
  rw [List.pairwise_append]
  refine ⟨fromPair_partA_pairwise_ge s n f, ?_, ?_⟩
  · exact List.pairwise_replicate.mpr (Or.inr (le_refl s))
  · intro a ha b hb
    have hb' : b = s := (List.mem_replicate.mp hb).2
    have ha' : s < a := fromPair_partA_elt_gt_1 s n f a ha
    omega

/-- The sum of `fromPair s n f` equals
`3 * s + ∑ r ∈ (Ioc s n).attach, (f r).val * r.val`. -/
lemma fromPair_sum (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    (fromPair s n f).sum = 3 * s + ∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val := by
  unfold fromPair
  rw [List.sum_append, List.flatMap_def, List.sum_flatten, List.map_map, List.sum_replicate]
  simp only [Function.comp_def, List.sum_replicate, smul_eq_mul]
  rw [add_comm _ (3 * s)]
  congr 1
  have hperm : ((Finset.Ioc s n).sort (· ≥ ·)).Perm ((Finset.Ioc s n).toList) :=
    Finset.sort_perm_toList _ _
  rw [(List.Perm.map _ hperm).sum_eq, Finset.sum_map_toList,
    ← Finset.sum_attach (Finset.Ioc s n)
    (fun r => (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) * r)]
  apply Finset.sum_congr rfl
  rintro ⟨r, hr⟩ _
  simp [hr]

/-- Membership: `s ∈ fromPair s n f`. Since `fromPair s n f` ends with three copies of `s`,
`s` is in the list. -/
lemma s_mem_fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    s ∈ fromPair s n f := by
  unfold fromPair
  exact List.mem_append_right _ (List.mem_replicate.mpr ⟨by norm_num, rfl⟩)

/-- `s` is a lower bound: every element `x ∈ fromPair s n f` satisfies `s ≤ x`.
The list is concatenation of:
- replications of `r ∈ Finset.Ioc s n` (each `r > s`)
- three copies of `s`. -/
lemma s_le_of_mem_fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3)
    (x : ℕ) (hx : x ∈ fromPair s n f) : s ≤ x := by
  unfold fromPair at hx
  rw [List.mem_append] at hx
  rcases hx with hA | hB
  · exact (fromPair_partA_elt_gt_1 s n f x hA).le
  · rw [List.mem_replicate] at hB
    exact hB.2.ge

/-- **Recovering the base part**. The smallest part of `fromPair s n f` is `s`. -/
lemma smallestPart_fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    smallestPart (fromPair s n f) = s := by
  unfold smallestPart
  have hmem : s ∈ fromPair s n f := s_mem_fromPair s n f
  have hlb : ∀ x ∈ fromPair s n f, s ≤ x := s_le_of_mem_fromPair s n f
  have hmin : (fromPair s n f).min? = some s :=
    List.min?_eq_some_iff.mpr ⟨hmem, hlb⟩
  rw [hmin]
  rfl

lemma count_flatMap_s_eq_zero (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
      (fun r => List.replicate
        (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r)).count s = 0 := by
  rw [List.count_eq_zero_of_not_mem]
  intro hs
  exact lt_irrefl s (fromPair_partA_elt_gt_1 s n f s hs)

/-- The element `s` appears exactly 3 times in `fromPair s n f`. -/
lemma count_s_fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    (fromPair s n f).count s = 3 := by
  unfold fromPair
  rw [List.count_append, count_flatMap_s_eq_zero s n f, List.count_replicate_self]

/-- For any `x` appearing in `fromPair s n f` with `s < x`, the count of `x` is at most 2. -/
lemma count_le_two_of_lt (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3)
    (x : ℕ) (hx : x ∈ fromPair s n f) (hxs : s < x) :
    (fromPair s n f).count x ≤ 2 := by
  have hmem : x ∈ Finset.Ioc s n := by
    unfold fromPair at hx
    rw [List.mem_append] at hx
    rcases hx with hA | hB
    · rw [List.mem_flatMap] at hA
      obtain ⟨r, hr_mem, hxr⟩ := hA
      rw [List.mem_replicate] at hxr
      obtain ⟨_, hxr_eq⟩ := hxr
      subst hxr_eq
      exact (Finset.mem_sort _).mp hr_mem
    · rw [List.mem_replicate] at hB
      obtain ⟨_, rfl⟩ := hB
      exact absurd hxs (lt_irrefl _)
  have hcount : (fromPair s n f).count x = (f ⟨x, hmem⟩).val :=
    count_fromPair_eq s n f ⟨x, hmem⟩
  have h3 : (f ⟨x, hmem⟩).val < 3 := (f ⟨x, hmem⟩).is_lt
  omega

/-- **Well-definedness of the inverse**.
If the degree constraint `3*s + ∑_r (f r).val * r.val = n` holds and `s ≤ n`,
then `fromPair s n f` is an Andrews–Dhar `D₃`-partition of `n`. -/
lemma fromPair_mem_D3Set (s n : ℕ) (_hsn : s ≤ n)
    (f : ↥(Finset.Ioc s n) → Fin 3)
    (hdeg : 3 * s + ∑ r ∈ (Finset.Ioc s n).attach, (f r).val * r.val = n) :
    fromPair s n f ∈ D3Set n := by
  show IsD3Partition (fromPair s n f) n
  refine ⟨⟨fromPair_pairwise_ge s n f, ?_⟩, fromPair_ne_nil s n f, ?_, ?_⟩
  · rw [fromPair_sum]; exact hdeg
  · rw [smallestPart_fromPair]; exact count_s_fromPair s n f
  · intro x hx hsx
    rw [smallestPart_fromPair] at hsx
    exact count_le_two_of_lt s n f x hx hsx

/-- **Helper: countP on the main flatMap part equals the sum of multiplicities**.
For the main flatMap part of `fromPair s n f`, the count of elements strictly
greater than `s` equals `∑ r ∈ (Ioc s n).attach, (f r).val`. -/
lemma countP_mainPart_eq_sum (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
        (fun r => List.replicate
          (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r)).countP
      (fun x => s < x) =
      ∑ r ∈ (Finset.Ioc s n).attach, (f r).val := by
  rw [List.countP_flatMap]
  have hperm : ((Finset.Ioc s n).sort (· ≥ ·)).Perm (Finset.Ioc s n).toList :=
    Finset.sort_perm_toList _ _
  rw [(hperm.map _).sum_eq]
  have hmap : List.map ((List.countP fun x => decide (s < x)) ∘ fun r =>
        List.replicate (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r)
        (Finset.Ioc s n).toList =
      List.map (fun r => if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0)
        (Finset.Ioc s n).toList := by
    apply List.map_congr_left
    intro r hr
    have hmem : r ∈ Finset.Ioc s n := by
      simpa [Finset.mem_toList] using hr
    simp only [Function.comp_apply, List.countP_replicate]
    have hslt : s < r := (Finset.mem_Ioc.mp hmem).1
    simp [hslt, hmem]
  rw [hmap, Finset.sum_map_toList, ← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro r _
  simp [r.2]

/-- **Weight preservation**: `tau (fromPair s n f) = ∑_{r ∈ Ioc s n} (f r).val`. -/
lemma tau_fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    tau (fromPair s n f) = ∑ r ∈ (Finset.Ioc s n).attach, (f r).val := by
  unfold tau
  rw [smallestPart_fromPair s n f]
  unfold fromPair
  rw [List.countP_append]
  have hbase : (List.replicate 3 s).countP (fun x => s < x) = 0 := by
    rw [List.countP_replicate]
    simp
  rw [hbase, Nat.add_zero]
  exact countP_mainPart_eq_sum s n f

/-- **Left inverse (forward ∘ inverse = id)**: `toCounts (fromPair s n f) s n = f`. -/
lemma toCounts_fromPair (s n : ℕ) (f : ↥(Finset.Ioc s n) → Fin 3) :
    toCounts (fromPair s n f) s n = f := by
  funext r
  unfold toCounts
  have hcount : (fromPair s n f).count r.val = (f r).val := count_fromPair_eq s n f r
  have hlt : (fromPair s n f).count r.val < 3 := by
    rw [hcount]
    exact (f r).isLt
  rw [dif_pos hlt]
  apply Fin.ext
  exact hcount

/-- The count of the smallest part equals 3 for `μ ∈ D3Set n`. -/
lemma count_smallestPart_eq_three (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    μ.count (smallestPart μ) = 3 := hμ.2.2.1

lemma smallestPart_mem_of_ne_nil (μ : List ℕ) (h : μ ≠ []) : smallestPart μ ∈ μ := by
  unfold smallestPart
  cases hm : μ.min? with
  | none => rw [List.min?_eq_none_iff] at hm; exact (h hm).elim
  | some m => simp; exact (List.min?_eq_some_iff.mp hm).1

/-- The smallest part of a list `μ` in `D3Set n` actually belongs to `μ`. -/
lemma smallestPart_mem_of_D3Set (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    smallestPart μ ∈ μ :=
  smallestPart_mem_of_ne_nil μ hμ.2.1

/-- The smallest part of `μ ∈ D3Set n` is at most `n`. -/
lemma smallestPart_le_of_D3Set (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    smallestPart μ ≤ n :=
  D3Set_parts_le n μ hμ (smallestPart μ) (smallestPart_mem_of_D3Set μ n hμ)

/-- For any `r > smallestPart μ` with `μ ∈ D3Set n`, the multiplicity `μ.count r ≤ 2`. -/
lemma count_le_two_of_gt_smallestPart (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n)
    (r : ℕ) (hr : smallestPart μ < r) : μ.count r ≤ 2 := by
  by_cases hrμ : r ∈ μ
  · exact hμ.2.2.2 r hrμ hr
  · simp [List.count_eq_zero.mpr hrμ]

/-- For any `r > smallestPart μ` with `μ ∈ D3Set n`, the multiplicity `μ.count r < 3`. -/
lemma count_lt_three_of_gt_smallestPart (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n)
    (r : ℕ) (hr : smallestPart μ < r) : μ.count r < 3 := by
  have := count_le_two_of_gt_smallestPart μ n hμ r hr
  omega

/-- For `r ∈ Finset.Ioc s n` (where `s = smallestPart μ`, `μ ∈ D3Set n`),
the `toCounts` function recovers `μ.count r` exactly. -/
lemma toCounts_val_eq_count (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n)
    (r : ↥(Finset.Ioc (smallestPart μ) n)) :
    (toCounts μ (smallestPart μ) n r).val = μ.count r.val := by
  unfold toCounts
  have hr_lt_s : smallestPart μ < r.val := (Finset.mem_Ioc.mp r.2).1
  have h_lt_three : μ.count r.val < 3 :=
    count_lt_three_of_gt_smallestPart μ n hμ r.val hr_lt_s
  simp [h_lt_three]

/-- Convert sum over `(Finset.Ioc s n).attach` of `(toCounts ...).val * r.val` to a plain
sum over `Finset.Ioc s n` of `μ.count r * r`. -/
lemma sum_attach_toCounts_eq (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    ∑ r ∈ (Finset.Ioc (smallestPart μ) n).attach,
        (toCounts μ (smallestPart μ) n r).val * r.val =
      ∑ r ∈ Finset.Ioc (smallestPart μ) n, μ.count r * r := by
  rw [← Finset.sum_attach (Finset.Ioc (smallestPart μ) n)
        (fun r => μ.count r * r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [toCounts_val_eq_count μ n hμ r]

/-! ## Main Statement Helpers -/

/-- The sum `μ.sum` decomposes as a sum over `Finset.range (n+1)` weighted by counts.
This uses `Finset.sum_list_count_of_subset` together with the fact that all parts are ≤ n. -/
lemma sum_eq_sum_count_mul (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    μ.sum = ∑ i ∈ Finset.range (n + 1), μ.count i * i := by
  have hsubset : μ.toFinset ⊆ Finset.range (n + 1) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_range]
    have : x ≤ n := D3Set_parts_le n μ hμ x hx
    omega
  have h := Finset.sum_list_count_of_subset μ (Finset.range (n + 1)) hsubset
  simp [smul_eq_mul] at h
  exact h

/-- For `μ ∈ D3Set n`, every element of `μ` is at least `smallestPart μ`. -/
lemma smallestPart_le_of_mem (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n)
    (x : ℕ) (hx : x ∈ μ) : smallestPart μ ≤ x :=
  smallestPart_le_of_mem_aux μ hμ.2.1 x hx

/-! ## More helpers for the main theorem -/

/-- For `μ ∈ D3Set n` and `i < smallestPart μ`, the count of `i` in `μ` is zero,
because no element of `μ` is less than `smallestPart μ`. -/
lemma count_eq_zero_of_lt_smallestPart (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n)
    (i : ℕ) (hi : i < smallestPart μ) : μ.count i = 0 := by
  rw [List.count_eq_zero]
  intro hin
  have h_le : smallestPart μ ≤ i := smallestPart_le_of_mem μ n hμ i hin
  omega

/-! ## Main theorem build-up -/

/-- Splitting the sum over `Finset.range (n+1)` at `smallestPart μ`. -/
lemma split_sum_at_smallestPart (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    (∑ i ∈ Finset.range (n + 1), μ.count i * i) =
      μ.count (smallestPart μ) * smallestPart μ +
        ∑ i ∈ Finset.Ioc (smallestPart μ) n, μ.count i * i := by
  set s := smallestPart μ
  have hsn : s ≤ n := smallestPart_le_of_D3Set μ n hμ
  have hsn' : s ≤ n + 1 := Nat.le_succ_of_le hsn
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun i => μ.count i * i) (Nat.zero_le s) hsn',
    Finset.Ico_add_one_right_eq_Icc, Finset.Icc_eq_cons_Ioc hsn, Finset.sum_cons]
  have h0 : (∑ i ∈ Finset.Ico 0 s, μ.count i * i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hilt : i < s := (Finset.mem_Ico.mp hi).2
    rw [count_eq_zero_of_lt_smallestPart μ n hμ i hilt]
    ring
  rw [h0]
  ring

/-- **Forward map respects the degree constraint**.
For `μ ∈ D3Set n`, the counts of parts in `Ioc (smallestPart μ) n` satisfy
`3 * smallestPart μ + ∑_r (toCounts μ (smallestPart μ) n r).val * r.val = n`. -/
lemma toCounts_degree_constraint (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    3 * smallestPart μ +
      ∑ r ∈ (Finset.Ioc (smallestPart μ) n).attach,
        (toCounts μ (smallestPart μ) n r).val * r.val = n := by
  rw [sum_attach_toCounts_eq μ n hμ]
  have hsum : μ.sum = n := hμ.1.2
  have h1 : μ.sum = ∑ i ∈ Finset.range (n + 1), μ.count i * i :=
    sum_eq_sum_count_mul μ n hμ
  have h2 : (∑ i ∈ Finset.range (n + 1), μ.count i * i) =
      μ.count (smallestPart μ) * smallestPart μ +
        ∑ i ∈ Finset.Ioc (smallestPart μ) n, μ.count i * i :=
    split_sum_at_smallestPart μ n hμ
  have h3 : μ.count (smallestPart μ) = 3 := count_smallestPart_eq_three μ n hμ
  rw [h3] at h2
  omega

/-- For any list `μ` and `r` strictly less than every element of `μ`, the count of `r` in `μ` is 0. -/
lemma count_eq_zero_of_lt_all (μ : List ℕ) (r : ℕ) (h : ∀ x ∈ μ, r < x) :
    μ.count r = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro hr
  exact lt_irrefl _ (h r hr)

/-- **Count of `smallestPart μ` in `fromPair`**. For `s = smallestPart μ`
(with `μ ∈ D3Set n`), the count of `s` in `fromPair s n (toCounts μ s n)` equals 3. -/
lemma count_smallestPart_fromPair_toCounts
    (μ : List ℕ) (n : ℕ) (_hμ : μ ∈ D3Set n) :
    (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).count
      (smallestPart μ) = 3 := by
  set s : ℕ := smallestPart μ
  set f : ↥(Finset.Ioc s n) → Fin 3 := toCounts μ s n
  unfold fromPair
  rw [List.count_append, List.count_replicate_self]
  have hflat :
      (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
        (fun r => List.replicate
          (if h : r ∈ Finset.Ioc s n then (f ⟨r, h⟩).val else 0) r)).count s = 0 :=
    count_eq_zero_of_lt_all _ s (fromPair_partA_elt_gt_1 s n f)
  rw [hflat]

/-- **Count agreement, case `s < r ≤ n`.** For `μ ∈ D3Set n` with `s = smallestPart μ`,
and `r` with `s < r` and `r ≤ n`, `(fromPair s n (toCounts μ s n)).count r = μ.count r`. -/
lemma count_fromPair_toCounts_of_lt_le
    (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) (r : ℕ)
    (hsr : smallestPart μ < r) (hrn : r ≤ n) :
    (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).count r =
      μ.count r := by
  have hmem : r ∈ Finset.Ioc (smallestPart μ) n := Finset.mem_Ioc.mpr ⟨hsr, hrn⟩
  have hcnt : μ.count r ≤ 2 := count_le_two_of_gt_smallestPart μ n hμ r hsr
  have hlt3 : μ.count r < 3 := lt_of_le_of_lt hcnt (by norm_num)
  have hcfp := count_fromPair_eq (smallestPart μ) n
    (toCounts μ (smallestPart μ) n) ⟨r, hmem⟩
  have htc : (toCounts μ (smallestPart μ) n ⟨r, hmem⟩).val = μ.count r := by
    simp [toCounts, hlt3]
  rw [hcfp, htc]

lemma fromPair_elt_le (s n : ℕ) (hsn : s ≤ n) (f : ↥(Finset.Ioc s n) → Fin 3)
    (x : ℕ) (hx : x ∈ fromPair s n f) : x ≤ n := by
  unfold fromPair at hx
  rw [List.mem_append] at hx
  rcases hx with hA | hB
  · rw [List.mem_flatMap] at hA
    obtain ⟨r, hr_mem, hxr⟩ := hA
    rw [Finset.mem_sort] at hr_mem
    rw [List.mem_replicate] at hxr
    rw [hxr.2]
    exact (Finset.mem_Ioc.mp hr_mem).2
  · rw [List.mem_replicate] at hB
    rw [hB.2]; exact hsn

/-- **Count agreement, case `r > n`.** -/
lemma count_fromPair_toCounts_of_gt_n
    (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) (r : ℕ) (hrn : n < r) :
    (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).count r =
      μ.count r := by
  have hs : smallestPart μ ≤ n := smallestPart_le_of_D3Set μ n hμ
  have hμ_count : μ.count r = 0 := by
    apply List.count_eq_zero.mpr
    intro hmem
    have := D3Set_parts_le n μ hμ r hmem
    omega
  have hfp_count : (fromPair (smallestPart μ) n
      (toCounts μ (smallestPart μ) n)).count r = 0 := by
    apply List.count_eq_zero.mpr
    intro hmem
    have := fromPair_elt_le (smallestPart μ) n hs
      (toCounts μ (smallestPart μ) n) r hmem
    omega
  rw [hfp_count, hμ_count]

/-- **Count agreement, case `r < s`.** -/
lemma count_fromPair_toCounts_of_lt_s
    (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) (r : ℕ)
    (hrs : r < smallestPart μ) :
    (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).count r =
      μ.count r := by
  set s := smallestPart μ
  set f := toCounts μ s n
  have h_μ : μ.count r = 0 := by
    apply count_eq_zero_of_lt_all
    intro x hx
    have hsx : s ≤ x := smallestPart_le_of_mem μ n hμ x hx
    exact lt_of_lt_of_le hrs hsx
  have h_from : (fromPair s n f).count r = 0 := by
    unfold fromPair
    rw [List.count_append]
    have h1 : (((Finset.Ioc s n).sort (· ≥ ·)).flatMap
      (fun r' => List.replicate
        (if h : r' ∈ Finset.Ioc s n then (f ⟨r', h⟩).val else 0) r')).count r = 0 := by
      apply count_eq_zero_of_lt_all
      intro x hx
      have hsx : s < x := fromPair_partA_elt_gt_1 s n f x hx
      exact lt_trans hrs hsx
    have h2 : (List.replicate 3 s).count r = 0 := by
      rw [List.count_replicate]
      have hne : s ≠ r := (Nat.ne_of_lt hrs).symm
      simp [hne]
    rw [h1, h2]
  rw [h_from, h_μ]

/-- **Aggregate count equality.** -/
lemma count_fromPair_toCounts_eq
    (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) (r : ℕ) :
    (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).count r =
      μ.count r := by
  by_cases h1 : r < smallestPart μ
  · exact count_fromPair_toCounts_of_lt_s μ n hμ r h1
  push_neg at h1
  rcases lt_or_eq_of_le h1 with hsr | heq
  · by_cases h2 : r ≤ n
    · exact count_fromPair_toCounts_of_lt_le μ n hμ r hsr h2
    · push_neg at h2
      exact count_fromPair_toCounts_of_gt_n μ n hμ r h2
  · subst heq
    rw [count_smallestPart_fromPair_toCounts μ n hμ]
    exact (hμ.2.2.1).symm

/-- **Right inverse (inverse ∘ forward = id)**. -/
lemma fromPair_toCounts (μ : List ℕ) (n : ℕ) (hμ : μ ∈ D3Set n) :
    fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n) = μ := by
  have hμP : μ.Pairwise (· ≥ ·) := hμ.1.1
  have hRHS : (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).Pairwise (· ≥ ·) :=
    fromPair_pairwise_ge _ _ _
  have hperm :
      (fromPair (smallestPart μ) n (toCounts μ (smallestPart μ) n)).Perm μ := by
    rw [List.perm_iff_count]
    intro a
    exact count_fromPair_toCounts_eq μ n hμ a
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hba hab) hRHS hμP hperm

/-- **Grouping the partition sum by the smallest part**:
`∑ μ ∈ hfin.toFinset, ω^(tau μ) = ∑ s ∈ range (n+1), ∑_{μ : smallestPart μ = s} ω^(tau μ)`. -/
lemma sum_partition_group_by_smallestPart (n : ℕ) (ω : ℂ)
    (hfin : (D3Set n).Finite) :
    ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) =
      ∑ s ∈ Finset.range (n + 1),
        ∑ μ ∈ hfin.toFinset.filter (fun μ => smallestPart μ = s),
          ω ^ (tau μ) := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro μ hμ
  rw [Set.Finite.mem_toFinset] at hμ
  obtain ⟨⟨_, hsum⟩, hne, _, _⟩ := hμ
  rw [Finset.mem_range, Nat.lt_succ_iff]
  have hmem : smallestPart μ ∈ μ := smallestPart_mem_of_ne_nil μ hne
  have hle : smallestPart μ ≤ μ.sum :=
    List.single_le_sum (by intros; exact Nat.zero_le _) _ hmem
  rw [hsum] at hle
  exact hle

lemma triangular_succ (k : ℕ) : triangular (k + 1) = triangular k + (k + 1) := by
  unfold triangular
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> (ring_nf; omega)

lemma triangular_add_two (k : ℕ) : triangular (k + 2) = triangular k + (2 * k + 3) := by
  rw [show k + 2 = (k + 1) + 1 by ring, triangular_succ, triangular_succ]; ring

lemma triangular_strictMono : StrictMono triangular := by
  intro a b hab
  induction hab with
  | refl => rw [triangular_succ]; omega
  | step _ ih => rw [triangular_succ]; omega

lemma H_poly_summand_coeff (ω : ℂ) (n k : ℕ) :
    (Polynomial.C ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        Polynomial.X ^ (triangular k) *
        (1 - Polynomial.X ^ (k + 1)) *
        (1 - Polynomial.X ^ (k + 2))).coeff n =
    ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
      ((if triangular k = n then (1 : ℂ) else 0) -
       (if triangular k + (k + 1) = n then 1 else 0) -
       (if triangular k + (k + 2) = n then 1 else 0) +
       (if triangular k + (2 * k + 3) = n then 1 else 0)) := by
  set c : ℂ := (-1 : ℂ) ^ k * ω ^ (2 * k)
  have hexpand :
      (Polynomial.C c * Polynomial.X ^ (triangular k) *
        (1 - Polynomial.X ^ (k + 1)) * (1 - Polynomial.X ^ (k + 2)) : Polynomial ℂ)
        = Polynomial.C c * Polynomial.X ^ (triangular k)
          - Polynomial.C c * Polynomial.X ^ (triangular k + (k + 1))
          - Polynomial.C c * Polynomial.X ^ (triangular k + (k + 2))
          + Polynomial.C c * Polynomial.X ^ (triangular k + (2 * k + 3)) := by
    rw [show (Polynomial.X : Polynomial ℂ) ^ (triangular k + (k + 1))
          = Polynomial.X ^ (triangular k) * Polynomial.X ^ (k + 1) from pow_add _ _ _,
        show (Polynomial.X : Polynomial ℂ) ^ (triangular k + (k + 2))
          = Polynomial.X ^ (triangular k) * Polynomial.X ^ (k + 2) from pow_add _ _ _,
        show (Polynomial.X : Polynomial ℂ) ^ (triangular k + (2 * k + 3))
          = Polynomial.X ^ (triangular k) *
            (Polynomial.X ^ (k + 1) * Polynomial.X ^ (k + 2)) from by
          rw [← pow_add, ← pow_add]; congr 1; ring]
    ring
  rw [hexpand]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  simp only [eq_comm (a := n)]
  ring

/-- **Helper (A): coefficient equality follows from quotient equality.**
If `P - Q ∈ Ideal.span {X^{n+1}}` in `Polynomial ℂ`, then `P.coeff n = Q.coeff n`. -/
lemma coeff_eq_of_sub_mem_span_X_pow (n : ℕ) (P Q : Polynomial ℂ)
    (h : P - Q ∈ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}) :
    P.coeff n = Q.coeff n := by
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨S, hS⟩ := h
  have hcoeff : (P - Q).coeff n = 0 := by
    rw [← hS, Polynomial.coeff_mul_X_pow']; simp
  rw [Polynomial.coeff_sub] at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- For a cube root of unity `ω` (with `ω² + ω + 1 = 0`), the factorization
`1 + C(ω) Xʳ + C(ω²) X²ʳ = (1 - Xʳ)(1 - C(ω²) Xʳ)` holds in `Polynomial ℂ`. -/
lemma factor_quadratic_at_cube_root (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (r : ℕ) :
    (1 : Polynomial ℂ) + Polynomial.C ω * Polynomial.X ^ r +
        Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r) =
      (1 - Polynomial.X ^ r) * (1 - Polynomial.C (ω ^ 2) * Polynomial.X ^ r) := by
  have hC : Polynomial.C ω + Polynomial.C (ω ^ 2) + 1 = 0 := by
    have : Polynomial.C (ω ^ 2 + ω + 1) = (0 : Polynomial ℂ) := by
      rw [hω]; simp
    simpa [Polynomial.C_add, Polynomial.C_1, add_comm, add_left_comm] using this
  have hX : (Polynomial.X : Polynomial ℂ) ^ (2 * r) = Polynomial.X ^ r * Polynomial.X ^ r := by
    rw [two_mul, pow_add]
  rw [hX]
  linear_combination (Polynomial.X ^ r : Polynomial ℂ) * hC

/-- From `ω^3 = 1` and `ω ≠ 1` we obtain `ω² + ω + 1 = 0`. This is the
standard factorization `x^3 - 1 = (x-1)(x^2+x+1)`: since `ω-1 ≠ 0` and the
product equals `0`, the second factor must vanish. -/
lemma omega_sq_sum_eq_zero (ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by ring_nf; linear_combination hω3
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hω1
  · exact h2

/-- **Polynomial identity (Step 4 of proof.md).**
After substituting the factorization from `factor_quadratic_at_cube_root`,
`G_omega ω n` becomes a sum over `s` of a product split into a `(1 - X^r)`-
part and a `(1 - ω² X^r)`-part. -/
lemma G_omega_factored (ω : ℂ) (n : ℕ) (hω : ω ^ 2 + ω + 1 = 0) :
    G_omega ω n =
      ∑ s ∈ Finset.range (n + 1),
        Polynomial.X ^ (3 * s) *
          ((∏ r ∈ Finset.Ioc s n, (1 - Polynomial.X ^ r)) *
            (∏ r ∈ Finset.Ioc s n, (1 - Polynomial.C (ω ^ 2) * Polynomial.X ^ r))) := by
  unfold G_omega
  refine Finset.sum_congr rfl ?_
  intro s _
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro r _
  exact factor_quadratic_at_cube_root ω hω r

lemma indices_le_n (n t : ℕ) (ht : 2 ≤ t) (htn : n = triangular t) :
    t - 2 ≤ n ∧ t - 1 ≤ n ∧ t ≤ n := by
  have htlen : t ≤ n := by
    rw [htn]
    unfold triangular
    have : t * 2 ≤ t * (t + 1) := by nlinarith
    omega
  exact ⟨by omega, by omega, htlen⟩

/-- At `k = t`, the indicator expression equals 1. -/
lemma indicator_expr_at_t (n t : ℕ) (ht : 2 ≤ t) (htn : n = triangular t) :
    ((if triangular t = n then (1 : ℂ) else 0) -
      (if triangular t + (t + 1) = n then 1 else 0) +
      (if triangular t + (2 * t + 3) = n then 1 else 0)) = 1 := by
  have h1 : triangular t = n := htn.symm
  have h2 : ¬ (triangular t + (t + 1) = n) := by
    intro h
    rw [htn] at h
    omega
  have h3 : ¬ (triangular t + (2 * t + 3) = n) := by
    intro h
    rw [htn] at h
    omega
  rw [if_pos h1, if_neg h2, if_neg h3]
  ring

/-- For `t ≥ 2`, `triangular (t-1) + t = triangular t`. (Application of `triangular_succ`
    with the index `t-1`, using `(t-1) + 1 = t`.) -/
lemma triangular_pred_add (t : ℕ) (ht : 2 ≤ t) :
    triangular (t - 1) + t = triangular t := by
  have h := triangular_succ (t - 1)
  rw [show t - 1 + 1 = t from by omega] at h
  omega

/-- For `t ≥ 2`, `triangular (t - 1) + (2 * (t - 1) + 3) = triangular (t + 1)`.
    Since `2*(t-1)+3 = 2t+1` and `triangular (t+1) = triangular t + (t+1)
    = triangular (t-1) + t + (t+1) = triangular (t-1) + (2t+1)`. -/
lemma triangular_pred_add_two_term (t : ℕ) (ht : 2 ≤ t) :
    triangular (t - 1) + (2 * (t - 1) + 3) = triangular (t + 1) := by
  have h₁ := triangular_succ (t - 1)
  have h₂ := triangular_succ t
  rw [show t - 1 + 1 = t from by omega] at h₁
  omega

/-- For any `t`, `triangular (t - 1) < triangular t` whenever `1 ≤ t`. -/
lemma triangular_pred_lt (t : ℕ) (ht : 1 ≤ t) : triangular (t - 1) < triangular t := by
  have h := triangular_succ (t - 1)
  rw [show t - 1 + 1 = t from by omega] at h
  omega

/-- For any `t`, `triangular t < triangular (t + 1)`. -/
lemma triangular_lt_succ (t : ℕ) : triangular t < triangular (t + 1) := by
  rw [triangular_succ]; omega

/-- At `k = t - 1`, the indicator expression equals `-1`. -/
lemma indicator_expr_at_t_sub_one (n t : ℕ) (ht : 2 ≤ t) (htn : n = triangular t) :
    ((if triangular (t - 1) = n then (1 : ℂ) else 0) -
      (if triangular (t - 1) + ((t - 1) + 1) = n then 1 else 0) +
      (if triangular (t - 1) + (2 * (t - 1) + 3) = n then 1 else 0)) = -1 := by
  have ht1 : 1 ≤ t := by omega
  have hsucc : (t - 1) + 1 = t := by omega
  have hlt1 : triangular (t - 1) < triangular t := triangular_pred_lt t ht1
  have hne1 : triangular (t - 1) ≠ n := by
    rw [htn]; exact Nat.ne_of_lt hlt1
  have heq2 : triangular (t - 1) + ((t - 1) + 1) = n := by
    rw [hsucc, htn]
    exact triangular_pred_add t ht
  have heq3 : triangular (t - 1) + (2 * (t - 1) + 3) = triangular (t + 1) :=
    triangular_pred_add_two_term t ht
  have hlt3 : triangular t < triangular (t + 1) := triangular_lt_succ t
  have hne3 : triangular (t - 1) + (2 * (t - 1) + 3) ≠ n := by
    rw [heq3, htn]; exact Nat.ne_of_gt hlt3
  rw [if_neg hne1, if_pos heq2, if_neg hne3]
  ring

/-- At `k = t - 2`, the indicator expression equals 1. -/
lemma indicator_expr_at_t_sub_two (n t : ℕ) (ht : 2 ≤ t) (htn : n = triangular t) :
    ((if triangular (t - 2) = n then (1 : ℂ) else 0) -
      (if triangular (t - 2) + ((t - 2) + 1) = n then 1 else 0) +
      (if triangular (t - 2) + (2 * (t - 2) + 3) = n then 1 else 0)) = 1 := by
  have ht2 : t - 2 + 2 = t := Nat.sub_add_cancel ht
  have ht1 : t - 2 + 1 = t - 1 := by omega
  have h3 : triangular (t - 2) + (2 * (t - 2) + 3) = n := by
    rw [← triangular_add_two (t - 2), ht2, htn]
  have h2 : ¬ (triangular (t - 2) + ((t - 2) + 1) = n) := by
    rw [← triangular_succ (t - 2), ht1, htn]
    intro heq
    have : t - 1 < t := by omega
    exact (triangular_strictMono this).ne heq
  have h1 : ¬ (triangular (t - 2) = n) := by
    rw [htn]
    intro heq
    have : t - 2 < t := by omega
    exact (triangular_strictMono this).ne heq
  rw [if_neg h1, if_neg h2, if_pos h3]
  ring

/-- The indicator expression vanishes whenever `k ∉ {t-2, t-1, t}` (with `n = triangular t`
and `t ≥ 2`). -/
lemma indicator_expr_eq_zero_of_ne (n t k : ℕ) (ht : 2 ≤ t) (htn : n = triangular t)
    (hk1 : k ≠ t) (hk2 : k ≠ t - 1) (hk3 : k ≠ t - 2) :
    ((if triangular k = n then (1 : ℂ) else 0) -
      (if triangular k + (k + 1) = n then 1 else 0) +
      (if triangular k + (2 * k + 3) = n then 1 else 0)) = 0 := by
  have hinj : Function.Injective triangular := triangular_strictMono.injective
  have h1 : triangular k ≠ n := by
    intro heq
    rw [htn] at heq
    exact hk1 (hinj heq)
  have h2 : triangular k + (k + 1) ≠ n := by
    intro heq
    rw [← triangular_succ k, htn] at heq
    have : k + 1 = t := hinj heq
    have : k = t - 1 := by omega
    exact hk2 this
  have h3 : triangular k + (2 * k + 3) ≠ n := by
    intro heq
    rw [← triangular_add_two k, htn] at heq
    have : k + 2 = t := hinj heq
    have : k = t - 2 := by omega
    exact hk3 this
  simp [h1, h2, h3]

/-- The image of `X^(n+1)` in `Polynomial ℂ ⧸ Ideal.span {X^(n+1)}` is zero,
i.e. `π(X)^(n+1) = 0`. Direct application of `Ideal.Quotient.eq_zero_iff_mem`
and `Ideal.subset_span`. -/
lemma quot_X_pow_nilpotent (n : ℕ) :
    ((Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (n + 1) = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- Powers of `q` past `n` vanish, given `q^(n+1) = 0`.
    From `hq : q^(n+1) = 0`, any `q^m` with `m ≥ n+1` is `0` by
    `q^m = q^(n+1) * q^(m-(n+1)) = 0`. -/
lemma pow_eq_zero_of_ge {R : Type*} [CommRing R] {q : R} {n : ℕ} (hq : q ^ (n + 1) = 0)
    {m : ℕ} (hm : n + 1 ≤ m) : q ^ m = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, hq, zero_mul]

/-- For each `r : ℕ`, `q^r` is nilpotent when `q^(n+1) = 0`.
    Proof: `(q^r)^(n+1) = q^(r*(n+1)) = (q^(n+1))^r = 0^r`. If `r=0` this gives 1, but actually
    `(q^r)^(n+1) = q^(r*(n+1))`. Since `q^(n+1) = 0`, we have `q^(r*(n+1)) = (q^(n+1))^r = 0` when r≥1.
    For r=0, q^0 = 1 which IS nilpotent only if ring is trivial. Actually we should phrase it differently:
    use `IsNilpotent.pow` or note that `q^r` for `r ≥ 1` is nilpotent. -/
lemma isNilpotent_pow_of_pow_eq_zero {R : Type*} [CommRing R] {q : R} {n : ℕ}
    (hq : q ^ (n + 1) = 0) (r : ℕ) (hr : 1 ≤ r) : IsNilpotent (q ^ r) := by
  refine ⟨n + 1, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hq, zero_pow]
  omega

/-- For each `r ≥ 1`, `1 - q^r` is a unit when `q^(n+1) = 0`. -/
lemma isUnit_one_sub_pow {R : Type*} [CommRing R] {q : R} {n : ℕ}
    (hq : q ^ (n + 1) = 0) (r : ℕ) (hr : 1 ≤ r) : IsUnit (1 - q ^ r) :=
  (isNilpotent_pow_of_pow_eq_zero hq r hr).isUnit_one_sub

/-- The Pochhammer product `P_s = ∏_{r=1}^s (1 - q^r)` is a unit. -/
lemma isUnit_pochhammer_prod {R : Type*} [CommRing R] {q : R} {n : ℕ}
    (hq : q ^ (n + 1) = 0) (s : ℕ) : IsUnit (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) := by
  have hqnil : IsNilpotent q := ⟨n + 1, hq⟩
  refine IsUnit.prod_iff.mpr ?_
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrne : r ≠ 0 := Nat.one_le_iff_ne_zero.mp hr1
  have hqrnil : IsNilpotent (q ^ r) := hqnil.pow_of_pos hrne
  exact hqrnil.isUnit_one_sub

/-- The Pochhammer product splits at `s ≤ n`:
    `∏_{r=1}^n (1-q^r) = (∏_{r=1}^s (1-q^r)) * (∏_{r∈(s,n]} (1-q^r))`. -/
lemma pochhammer_split {R : Type*} [CommRing R] (q : R) (s n : ℕ) (hs : s ≤ n) :
    (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r))
      = (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r))
          * (∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by
  have hunion : Finset.Icc 1 n = Finset.Icc 1 s ∪ Finset.Ioc s n := by
    ext r
    simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 s) (Finset.Ioc s n) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp [Finset.mem_Icc] at hr1
    simp [Finset.mem_Ioc] at hr2
    omega
  rw [hunion, Finset.prod_union hdisj]

/-- Standard splitting: `∏_{r ∈ Icc 1 (j+1)} = (∏_{r ∈ Icc 1 j}) * (1 - q^(j+1))`. -/
lemma prod_Icc_succ_split {R : Type*} [CommRing R] (q : R) (j : ℕ) :
    ∏ r ∈ Finset.Icc 1 (j + 1), (1 - q ^ r) =
      (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) * (1 - q ^ (j + 1)) := by
  rw [show Finset.Icc 1 (j + 1) = Finset.Icc 1 j ∪ {j + 1} by
    { ext x; simp [Finset.mem_Icc]; omega }]
  rw [Finset.prod_union (by simp [Finset.disjoint_left]; omega)]
  simp

/-- Reused: `∏_{r ∈ Ioc s n}(1-q^r) = P_n * Us_s` when `s ≤ n` and `P_s * Us_s = 1`. -/
lemma prod_Ioc_eq_full_mul_inverse {R : Type*} [CommRing R] (s n : ℕ) (q : R)
    (Us_s : R) (hs : s ≤ n)
    (hU : (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us_s = 1) :
    (∏ r ∈ Finset.Ioc s n, (1 - q ^ r))
      = (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us_s := by
  have hsplit := pochhammer_split q s n hs
  rw [hsplit]
  rw [show (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * (∏ r ∈ Finset.Ioc s n, (1 - q ^ r))
        * Us_s
        = (∏ r ∈ Finset.Ioc s n, (1 - q ^ r))
            * ((∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us_s) by ring]
  rw [hU, mul_one]

/-- The auxiliary function `L` indexed by `j`. -/
def L_aux {R : Type*} [CommRing R] (q : R) (n : ℕ) (j : ℕ) : R :=
  ∑ s ∈ Finset.range (n + 1), q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)

/-- The auxiliary function `Q` indexed by `j`. -/
def Q_aux {R : Type*} [CommRing R] (q : R) (j : ℕ) : R :=
  ∏ r ∈ Finset.Icc 1 (j + 2), (1 - q ^ r)

lemma prod_Ioc_pred_split {R : Type*} [CommRing R] (q : R) (n t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) :
    ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r) =
      (1 - q ^ t) * ∏ r ∈ Finset.Ioc t n, (1 - q ^ r) := by
  have h2 : Finset.Ioc (t - 1) n = insert t (Finset.Ioc t n) := by
    ext r
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    constructor
    · rintro ⟨h3, h4⟩
      by_cases h5 : r = t
      · left; exact h5
      · right; refine ⟨?_, h4⟩
        have : t - 1 < r := h3
        omega
    · rintro (rfl | ⟨h3, h4⟩)
      · exact ⟨by omega, htn⟩
      · exact ⟨by omega, h4⟩
  have h3 : t ∉ Finset.Ioc t n := by simp
  rw [h2, Finset.prod_insert h3]

lemma boundary_term_zero {R : Type*} [CommRing R] {q : R} {n : ℕ}
    (hq : q ^ (n + 1) = 0) (j : ℕ) :
    q ^ ((j + 3) * (n + 1)) = 0 := by
  apply pow_eq_zero_of_ge hq
  have h1 : 1 * (n + 1) ≤ (j + 3) * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) (by omega)
  linarith [h1]

lemma rhs_distribute_diff {R : Type*} [CommRing R] (n : ℕ) (q : R) (j : ℕ) :
    (1 - q ^ (j + 3)) *
      (∑ s ∈ Finset.range (n + 1),
        q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) =
    (∑ s ∈ Finset.range (n + 1),
        q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) -
    (∑ s ∈ Finset.range (n + 1),
        q ^ ((j + 3) * (s + 1)) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by
  rw [sub_mul, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hpow : q ^ ((j + 3) * (s + 1)) = q ^ (j + 3) * q ^ ((j + 3) * s) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hpow]
  ring

lemma shift_sum_eq {R : Type*} [CommRing R] (n : ℕ) (q : R) (j : ℕ) :
    (∑ s ∈ Finset.range (n + 1),
        q ^ ((j + 3) * (s + 1)) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) =
    (∑ t ∈ Finset.Ico 1 (n + 2),
        q ^ ((j + 3) * t) * ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hn2 : n + 2 - 1 = n + 1 := by omega
  rw [hn2]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : 1 + k - 1 = k := by omega
  have h2 : (j + 3) * (1 + k) = (j + 3) * (k + 1) := by ring
  rw [h1, h2]

lemma shift_sum_drop_boundary {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) (j : ℕ) :
    (∑ t ∈ Finset.Ico 1 (n + 2),
        q ^ ((j + 3) * t) * ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r)) =
    (∑ t ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * t) * ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r)) := by
  have hle : 1 ≤ n + 1 := by omega
  have hrw : (∑ t ∈ Finset.Ico 1 (n + 2),
      q ^ ((j + 3) * t) * ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r)) =
      (∑ t ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * t) * ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r)) +
      (q ^ ((j + 3) * (n + 1)) *
        ∏ r ∈ Finset.Ioc ((n + 1) - 1) n, (1 - q ^ r)) := by
    have : n + 2 = (n + 1) + 1 := by ring
    rw [this]
    exact Finset.sum_Ico_succ_top hle _
  rw [hrw]
  have hbdy : q ^ ((j + 3) * (n + 1)) *
      ∏ r ∈ Finset.Ioc ((n + 1) - 1) n, (1 - q ^ r) = 0 := by
    have hp : ((n + 1) - 1 : ℕ) = n := by omega
    rw [hp]
    rw [Finset.Ioc_self]
    rw [Finset.prod_empty]
    rw [mul_one]
    exact boundary_term_zero hq j
  rw [hbdy, add_zero]

lemma shift_sum_factor {R : Type*} [CommRing R] (n : ℕ) (q : R) (j : ℕ) :
    (∑ t ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * t) * ∏ r ∈ Finset.Ioc (t - 1) n, (1 - q ^ r)) =
    (∑ t ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * t) * ((1 - q ^ t) * ∏ r ∈ Finset.Ioc t n, (1 - q ^ r))) := by
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [Finset.mem_Ico] at ht
  obtain ⟨h1, h2⟩ := ht
  have htn : t ≤ n := Nat.lt_succ_iff.mp h2
  rw [prod_Ioc_pred_split q n t h1 htn]

lemma L_aux_succ_split {R : Type*} [CommRing R] (n : ℕ) (q : R) (j : ℕ) :
    (∑ s ∈ Finset.range (n + 1),
        q ^ ((j + 4) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) =
    (∏ r ∈ Finset.Ioc 0 n, (1 - q ^ r)) +
    (∑ s ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 4) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1)
    (Nat.le_add_left 1 n)]
  simp

lemma L_aux_split_at_j {R : Type*} [CommRing R] (n : ℕ) (q : R) (j : ℕ) :
    (∑ s ∈ Finset.range (n + 1),
        q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) =
    (∏ r ∈ Finset.Ioc 0 n, (1 - q ^ r)) +
    (∑ s ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by
  rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
  simp [mul_zero, pow_zero, one_mul]

lemma sum_cancel_at_j {R : Type*} [CommRing R] (n : ℕ) (q : R) (j : ℕ) :
    (∑ s ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) -
    (∑ t ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 3) * t) * ((1 - q ^ t) * ∏ r ∈ Finset.Ioc t n, (1 - q ^ r))) =
    (∑ s ∈ Finset.Ico 1 (n + 1),
        q ^ ((j + 4) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by
  have h₁ : (∑ s ∈ Finset.Ico 1 (n + 1),
      q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) -
    (∑ t ∈ Finset.Ico 1 (n + 1),
      q ^ ((j + 3) * t) * ((1 - q ^ t) * ∏ r ∈ Finset.Ioc t n, (1 - q ^ r))) =
    ∑ s ∈ Finset.Ico 1 (n + 1),
      (q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) - q ^ ((j + 3) * s) * ((1 - q ^ s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r))) := by
    rw [Finset.sum_sub_distrib]
  have h₂ : ∑ s ∈ Finset.Ico 1 (n + 1),
      (q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) - q ^ ((j + 3) * s) * ((1 - q ^ s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r))) =
    ∑ s ∈ Finset.Ico 1 (n + 1),
      q ^ ((j + 4) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) := by
    apply Finset.sum_congr rfl
    intro s _
    have h₅ : q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) - q ^ ((j + 3) * s) * ((1 - q ^ s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) = (q ^ ((j + 3) * s) - q ^ ((j + 3) * s) * (1 - q ^ s)) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) := by
      ring
    rw [h₅]
    have h₆ : q ^ ((j + 3) * s) - q ^ ((j + 3) * s) * (1 - q ^ s) = q ^ ((j + 4) * s) := by
      have h₇ : q ^ ((j + 4) * s) = q ^ ((j + 3) * s + s) := by
        ring_nf
      rw [h₇]
      have h₈ : q ^ ((j + 3) * s + s) = q ^ ((j + 3) * s) * q ^ s := by
        rw [pow_add]
      rw [h₈]
      ring
    rw [h₆]
  rw [h₁, h₂]

lemma L_aux_recurrence {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) (j : ℕ) :
    L_aux q n (j + 1) = (1 - q ^ (j + 3)) * L_aux q n j := by
  unfold L_aux
  have hexp : j + 1 + 3 = j + 4 := by ring
  simp only [hexp]
  rw [rhs_distribute_diff n q j, shift_sum_eq n q j, shift_sum_drop_boundary n q hq j,
    shift_sum_factor n q j, L_aux_succ_split n q j, L_aux_split_at_j n q j]
  set P0 := ∏ r ∈ Finset.Ioc 0 n, (1 - q ^ r)
  set A := ∑ s ∈ Finset.Ico 1 (n + 1),
            q ^ ((j + 4) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)
  set B := ∑ s ∈ Finset.Ico 1 (n + 1),
            q ^ ((j + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r)
  set C := ∑ t ∈ Finset.Ico 1 (n + 1),
            q ^ ((j + 3) * t) *
              ((1 - q ^ t) * ∏ r ∈ Finset.Ioc t n, (1 - q ^ r))
  have hcancel : B - C = A := sum_cancel_at_j n q j
  rw [← hcancel]; ring

lemma Q_aux_recurrence {R : Type*} [CommRing R] (q : R) (j : ℕ) :
    Q_aux q (j + 1) = Q_aux q j * (1 - q ^ (j + 3)) := by
  unfold Q_aux
  have h4 : Finset.Icc 1 ((j + 1) + 2) = Finset.Icc 1 (j + 2) ∪ {(j + 3)} := by
    ext x; simp [Finset.mem_Icc]; omega
  rw [h4, Finset.prod_union (by simp [Finset.disjoint_left]; omega)]
  simp

lemma L_aux_summand_vanishes {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) {s : ℕ} (hs : 1 ≤ s) :
    q ^ ((n + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) = 0 := by
  have h1 : (n + 3) * s ≥ n + 1 := by
    have h3 : (n + 3) * s ≥ (n + 3) * 1 :=
      Nat.mul_le_mul_left (n + 3) hs
    omega
  have h2 : q ^ ((n + 3) * s) = 0 := pow_eq_zero_of_ge hq h1
  rw [h2]; simp

lemma prod_Ioc_zero_eq_Icc_one {R : Type*} [CommRing R] (n : ℕ) (q : R) :
    ∏ r ∈ Finset.Ioc 0 n, (1 - q ^ r) = ∏ r ∈ Finset.Icc 1 n, (1 - q ^ r) := by
  have h : Finset.Ioc (0 : ℕ) n = Finset.Icc 1 n := by
    ext x
    simp [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [h]

lemma L_aux_at_n_eq_prod {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) :
    L_aux q n n = ∏ r ∈ Finset.Icc 1 n, (1 - q ^ r) := by
  unfold L_aux
  rw [show (Finset.range (n + 1)) = insert 0 (Finset.Ico 1 (n + 1)) from by
    ext x
    simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega]
  rw [Finset.sum_insert (by simp)]
  have hsum_zero : ∑ s ∈ Finset.Ico 1 (n + 1),
      q ^ ((n + 3) * s) * ∏ r ∈ Finset.Ioc s n, (1 - q ^ r) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.mem_Ico] at hs
    exact L_aux_summand_vanishes n q hq hs.1
  rw [hsum_zero, add_zero]
  simp only [mul_zero, pow_zero, one_mul]
  exact prod_Ioc_zero_eq_Icc_one n q

lemma Q_aux_at_n_eq_prod {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) :
    Q_aux q n = ∏ r ∈ Finset.Icc 1 n, (1 - q ^ r) := by
  have h₁ : q ^ (n + 2) = 0 := pow_eq_zero_of_ge hq (by omega)
  unfold Q_aux
  rw [show Finset.Icc 1 (n + 2) = Finset.Icc 1 n ∪ {n + 1, n + 2} from by
    ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.prod_union (by
    simp [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega)]
  rw [Finset.prod_pair (show (n + 1 : ℕ) ≠ n + 2 by omega), hq, h₁]
  ring

lemma L_aux_eq_Q_aux_at_n {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) :
    L_aux q n n = Q_aux q n := by
  rw [L_aux_at_n_eq_prod n q hq, Q_aux_at_n_eq_prod n q hq]

lemma L_aux_eq_Q_aux_1 {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) (j : ℕ) (hj : j ≤ n) :
    L_aux q n j = Q_aux q j := by
  suffices H : ∀ d : ℕ, ∀ j : ℕ, j ≤ n → n - j = d → L_aux q n j = Q_aux q j by
    exact H (n - j) j hj rfl
  intro d
  induction d with
  | zero =>
    intro j hj hd
    have hjn : j = n := by omega
    rw [hjn]
    exact L_aux_eq_Q_aux_at_n n q hq
  | succ d ih =>
    intro j hj hd
    have hjlt : j < n := by omega
    have hj1 : j + 1 ≤ n := hjlt
    have hd' : n - (j + 1) = d := by omega
    have ih1 : L_aux q n (j + 1) = Q_aux q (j + 1) := ih (j + 1) hj1 hd'
    have hL : L_aux q n (j + 1) = (1 - q ^ (j + 3)) * L_aux q n j :=
      L_aux_recurrence n q hq j
    have hQ : Q_aux q (j + 1) = Q_aux q j * (1 - q ^ (j + 3)) :=
      Q_aux_recurrence q j
    have heq : (1 - q ^ (j + 3)) * L_aux q n j = Q_aux q j * (1 - q ^ (j + 3)) := by
      rw [← hL, ih1, hQ]
    have hunit : IsUnit (1 - q ^ (j + 3)) := isUnit_one_sub_pow hq (j + 3) (by omega)
    have heq' : (1 - q ^ (j + 3)) * L_aux q n j = (1 - q ^ (j + 3)) * Q_aux q j := by
      rw [heq]; ring
    exact hunit.mul_left_cancel heq'

/-- **Step 4 of proof.md** (Truncated q-geometric):
    For each `k ∈ [0,n]`, the inverse of `P_s := ∏_{r=1}^s (1-q^r)` satisfies
    ∑_{s=0}^n q^{(k+3)s} * U_s = P_{k+2} * U_n where `U_s` denotes the inverse of `P_s`.
    Equivalently (multiplying through by `P_n`), if `Us : ℕ → R` is defined as the
    inverse of `Ps s := ∏ r ∈ Finset.Icc 1 s, (1 - q^r)`, then
    `∑_{s=0}^n q^{(k+3)s} * Us s = (P_{k+2}) * (Us n)`. -/
lemma q_geometric_truncated {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) (k : ℕ) (hk : k ≤ n)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1) :
    (∑ s ∈ Finset.range (n + 1), q ^ ((k + 3) * s) * Us s)
      = (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * Us n := by
  set Pn := ∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)
  have hPnUnit : IsUnit Pn := isUnit_pochhammer_prod hq n
  apply hPnUnit.mul_left_cancel
  have hRHS : Pn * ((∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * Us n)
      = ∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r) := by
    have hUsn : Pn * Us n = 1 := hUs n le_rfl
    have : Pn * ((∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * Us n)
        = (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * (Pn * Us n) := by ring
    rw [this, hUsn, mul_one]
  have hLHS : Pn * (∑ s ∈ Finset.range (n + 1), q ^ ((k + 3) * s) * Us s)
      = ∑ s ∈ Finset.range (n + 1),
          q ^ ((k + 3) * s) * (∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    have hsn : s ≤ n := Nat.lt_succ_iff.mp hs
    have hPs : (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1 := hUs s hsn
    have hIoc : (∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) = Pn * Us s :=
      prod_Ioc_eq_full_mul_inverse s n q (Us s) hsn hPs
    calc Pn * (q ^ ((k + 3) * s) * Us s)
        = q ^ ((k + 3) * s) * (Pn * Us s) := by ring
      _ = q ^ ((k + 3) * s) * (∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) := by rw [← hIoc]
  rw [hLHS, hRHS]
  exact L_aux_eq_Q_aux_1 n q hq k hk

lemma Us_zero_eq_one {R : Type*} [CommRing R] {q : R} (Us : ℕ → R)
    (hUs : ∀ s ≤ 0, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1) :
    Us 0 = 1 := by
  have h₁ : (∏ r ∈ Finset.Icc 1 0, (1 - q ^ r)) * Us 0 = 1 := hUs 0 (by norm_num)
  have h₂ : (∏ r ∈ Finset.Icc 1 0, (1 - q ^ r)) = 1 := by
    simp
  rw [h₂, one_mul] at h₁
  exact h₁

lemma Us_recurrence {R : Type*} [CommRing R] {q : R} {n : ℕ}
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1)
    (j : ℕ) (hj : j + 1 ≤ n) :
    Us j = (1 - q ^ (j + 1)) * Us (j + 1) := by
  have hj_le : j ≤ n := le_of_lt (Nat.lt_of_succ_le hj)
  have h_j : (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) * Us j = 1 := hUs j hj_le
  have h_jp1 : (∏ r ∈ Finset.Icc 1 (j + 1), (1 - q ^ r)) * Us (j + 1) = 1 := hUs (j + 1) hj
  have hsplit : ∏ r ∈ Finset.Icc 1 (j + 1), (1 - q ^ r)
      = (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) * (1 - q ^ (j + 1)) :=
    prod_Icc_succ_split q j
  rw [hsplit] at h_jp1
  have h_jp1' : (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) * ((1 - q ^ (j + 1)) * Us (j + 1)) = 1 := by
    rw [← mul_assoc]; exact h_jp1
  have hP_unit : IsUnit (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) :=
    isUnit_pochhammer_prod hq j
  have heq : (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) * Us j
           = (∏ r ∈ Finset.Icc 1 j, (1 - q ^ r)) * ((1 - q ^ (j + 1)) * Us (j + 1)) := by
    rw [h_j, h_jp1']
  exact hP_unit.mul_left_cancel heq

lemma prod_Ioc_pull_first {R : Type*} [CommRing R] (c q : R) (s n : ℕ) (hsn : s < n) :
    ∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r)
      = (1 - c * q ^ (s + 1)) * ∏ r ∈ Finset.Ioc (s + 1) n, (1 - c * q ^ r) := by
  have h₁ : Finset.Ioc s n = {s + 1} ∪ Finset.Ioc (s + 1) n := by
    apply Finset.ext
    intro x
    simp [Finset.mem_Ioc]
    omega
  have h₂ : Disjoint ({s + 1} : Finset ℕ) (Finset.Ioc (s + 1) n) := by
    simp [Finset.mem_Ioc]
  calc
    ∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r) = ∏ r ∈ ({s + 1} ∪ Finset.Ioc (s + 1) n : Finset ℕ), (1 - c * q ^ r) := by
      rw [h₁]
    _ = (∏ r ∈ ({s + 1} : Finset ℕ), (1 - c * q ^ r)) * (∏ r ∈ Finset.Ioc (s + 1) n, (1 - c * q ^ r)) := by
      rw [Finset.prod_union h₂]
    _ = (1 - c * q ^ (s + 1)) * ∏ r ∈ Finset.Ioc (s + 1) n, (1 - c * q ^ r) := by
      simp [Finset.prod_singleton]

lemma euler_truncated_at_n {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1) :
    (∏ r ∈ Finset.Ioc n n, (1 - c * q ^ r))
      = ∑ k ∈ Finset.range (n + 1),
          ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * n) * Us k := by
  have exponent_ge_succ : ∀ (k : ℕ), 1 ≤ k → n + 1 ≤ triangular k + k * n := by
    intro k hk
    have h₂ : triangular k ≥ 1 := by
      have := triangular_strictMono (Nat.zero_lt_of_lt hk)
      simp [triangular] at this ⊢
      omega
    have h₃ : k * n ≥ n := by
      have h₅ : k * n ≥ 1 * n := Nat.mul_le_mul_right n hk
      linarith
    linarith
  have hIoc : Finset.Ioc n n = (∅ : Finset ℕ) := Finset.Ioc_self n
  rw [hIoc, Finset.prod_empty]
  have hUs0_local : ∀ s ≤ 0, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1 := by
    intro s hs
    exact hUs s (le_trans hs (Nat.zero_le _))
  have hU0 : Us 0 = 1 := Us_zero_eq_one Us hUs0_local
  have hSum : (∑ k ∈ Finset.range (n + 1),
        ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * n) * Us k) = 1 := by
    have h0_mem : 0 ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]; omega
    rw [← Finset.sum_erase_add _ _ h0_mem]
    have hzero_term :
        ((-1 : R) ^ 0 * c ^ 0) * q ^ (triangular 0 + 0 * n) * Us 0 = 1 := by
      simp [triangular, hU0]
    rw [hzero_term]
    have hrest : (∑ k ∈ (Finset.range (n + 1)).erase 0,
          ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * n) * Us k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_erase, Finset.mem_range] at hk
      obtain ⟨hk0, _⟩ := hk
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hqk : q ^ (triangular k + k * n) = 0 :=
        pow_eq_zero_of_ge hq (exponent_ge_succ k hk1)
      rw [hqk]; ring
    rw [hrest, zero_add]
  rw [hSum]

private lemma exponent_ge_succ_boundary_step (n s : ℕ) :
    n + 1 ≤ triangular n + n * (s + 1) + (s + 1) := by
  unfold triangular
  have : n * (n + 1) / 2 ≥ 0 := Nat.zero_le _
  have h2 : n * (s + 1) ≥ n := by nlinarith
  linarith

private lemma step_combine_boundary_term_zero_step {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R) (s : ℕ) :
    c * q ^ (s + 1) * (((-1 : R) ^ n * c ^ n) * q ^ (triangular n + n * (s + 1)) * Us n) = 0 := by
  have hq_zero : q ^ (s + 1 + (triangular n + n * (s + 1))) = 0 := by
    apply pow_eq_zero_of_ge hq
    have h := exponent_ge_succ_boundary_step n s
    linarith
  have key : q ^ (s + 1) * q ^ (triangular n + n * (s + 1)) = 0 := by
    rw [← pow_add]; exact hq_zero
  have : c * q ^ (s + 1) * ((-1 : R) ^ n * c ^ n * q ^ (triangular n + n * (s + 1)) * Us n)
       = ((-1 : R) ^ n * c ^ n * c)
         * (q ^ (s + 1) * q ^ (triangular n + n * (s + 1))) * Us n := by ring
  rw [this, key]; ring

private lemma per_term_combine_algebra_step {R : Type*} [CommRing R] (q c : R) (U : R) (s k T : ℕ) :
    ((-1 : R) ^ (k + 1) * c ^ (k + 1)) * q ^ ((T + (k + 1)) + (k + 1) * (s + 1)) * U
        - c * q ^ (s + 1) *
            (((-1 : R) ^ k * c ^ k) * q ^ (T + k * (s + 1)) * ((1 - q ^ (k + 1)) * U))
      = ((-1 : R) ^ (k + 1) * c ^ (k + 1)) * q ^ ((T + (k + 1)) + (k + 1) * s) * U := by
  have h1 : q ^ ((T + (k + 1)) + (k + 1) * (s + 1)) = q ^ (T + (k + 1) * s + (k + 1)) * q ^ (k + 1) := by
    rw [← pow_add]; congr 1; ring
  have h2 : q ^ (s + 1) * q ^ (T + k * (s + 1)) = q ^ (T + (k + 1) * s + (k + 1)) := by
    rw [← pow_add]; congr 1; ring
  have h3 : q ^ ((T + (k + 1)) + (k + 1) * s) = q ^ (T + (k + 1) * s + (k + 1)) := by
    congr 1; ring
  set A := q ^ (T + (k + 1) * s + (k + 1))
  rw [h1, h3]
  have hrewrite : c * q ^ (s + 1) *
      (((-1 : R) ^ k * c ^ k) * q ^ (T + k * (s + 1)) * ((1 - q ^ (k + 1)) * U)) =
      ((-1 : R) ^ k * c ^ (k + 1)) * (q ^ (s + 1) * q ^ (T + k * (s + 1))) *
        ((1 - q ^ (k + 1)) * U) := by ring
  rw [hrewrite, h2]
  have hneg : (-1 : R) ^ (k + 1) = -((-1) ^ k) := by
    rw [pow_succ]; ring
  rw [hneg]
  ring

private lemma per_term_combine_step {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (Us : ℕ → R)
    (hUs_rec : ∀ j, j + 1 ≤ n → Us j = (1 - q ^ (j + 1)) * Us (j + 1))
    (s k : ℕ) (hkn : k + 1 ≤ n) :
    ((-1 : R) ^ (k + 1) * c ^ (k + 1)) * q ^ (triangular (k + 1) + (k + 1) * (s + 1)) * Us (k + 1)
        - c * q ^ (s + 1) * (((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * (s + 1)) * Us k)
      = ((-1 : R) ^ (k + 1) * c ^ (k + 1)) * q ^ (triangular (k + 1) + (k + 1) * s) * Us (k + 1) := by
  rw [hUs_rec k hkn]
  rw [triangular_succ k]
  exact per_term_combine_algebra_step q c (Us (k + 1)) s k (triangular k)

private lemma step_combine_step {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1)
    (s : ℕ) (_hsn : s < n) :
    (1 - c * q ^ (s + 1)) *
        (∑ k ∈ Finset.range (n + 1),
            ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * (s + 1)) * Us k)
      = ∑ k ∈ Finset.range (n + 1),
          ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k := by
  set f : ℕ → R := fun k =>
    ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * (s + 1)) * Us k with hf_def
  set g : ℕ → R := fun k =>
    ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k with hg_def
  have hUs_rec : ∀ j, j + 1 ≤ n → Us j = (1 - q ^ (j + 1)) * Us (j + 1) :=
    Us_recurrence hq Us hUs
  have step1 :
      (1 - c * q ^ (s + 1)) * (∑ k ∈ Finset.range (n + 1), f k)
        = (∑ k ∈ Finset.range (n + 1), f k)
          - (∑ k ∈ Finset.range (n + 1), c * q ^ (s + 1) * f k) := by
    rw [sub_mul, one_mul, Finset.mul_sum]
  rw [step1]
  have hbdry : c * q ^ (s + 1) * f n = 0 :=
    step_combine_boundary_term_zero_step n q c hq Us s
  have split2 :
      (∑ k ∈ Finset.range (n + 1), c * q ^ (s + 1) * f k)
        = ∑ k ∈ Finset.range n, c * q ^ (s + 1) * f k := by
    rw [Finset.sum_range_succ]
    rw [hbdry, add_zero]
  rw [split2]
  have split1 :
      (∑ k ∈ Finset.range (n + 1), f k)
        = f 0 + ∑ k ∈ Finset.range n, f (k + 1) := by
    rw [Finset.sum_range_succ' f n]
    ring
  rw [split1]
  have combine_step :
      (f 0 + ∑ k ∈ Finset.range n, f (k + 1)) - ∑ k ∈ Finset.range n, c * q ^ (s + 1) * f k
        = f 0 + ∑ k ∈ Finset.range n, (f (k + 1) - c * q ^ (s + 1) * f k) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [combine_step]
  have per_term : ∀ k ∈ Finset.range n,
      f (k + 1) - c * q ^ (s + 1) * f k = g (k + 1) := by
    intro k hk
    have hkn : k + 1 ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    simp only [hf_def, hg_def]
    exact per_term_combine_step n q c Us hUs_rec s k hkn
  rw [Finset.sum_congr rfl per_term]
  have hf0g0 : f 0 = g 0 := by
    simp only [hf_def, hg_def, Nat.zero_mul]
  rw [hf0g0]
  rw [Finset.sum_range_succ' g n]
  ring

lemma euler_truncated_step {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1)
    (s : ℕ) (hsn : s < n)
    (ih : (∏ r ∈ Finset.Ioc (s + 1) n, (1 - c * q ^ r))
            = ∑ k ∈ Finset.range (n + 1),
                ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * (s + 1)) * Us k) :
    (∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r))
      = ∑ k ∈ Finset.range (n + 1),
          ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k := by
  rw [prod_Ioc_pull_first c q s n hsn, ih]
  exact step_combine_step n q c hq Us hUs s hsn

/-- **Step 3 of proof.md** (Truncated Euler expansion):
    For each `s ∈ [0,n]`,
    ∏_{r∈(s,n]} (1 - c*q^r) = ∑_{k=0}^n (-1)^k * c^k * q^{T_k + k*s} * U_k,
    where `T_k = triangular k` and `U_k` is the inverse of `P_k = ∏_{r=1}^k (1-q^r)`. -/
lemma euler_truncated_expansion {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1)
    (s : ℕ) (hs : s ≤ n) :
    (∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r))
      = ∑ k ∈ Finset.range (n + 1),
          ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k := by
  suffices h : ∀ d : ℕ, d ≤ n →
      (∏ r ∈ Finset.Ioc (n - d) n, (1 - c * q ^ r))
        = ∑ k ∈ Finset.range (n + 1),
            ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * (n - d)) * Us k by
    have := h (n - s) (by omega)
    have hns : n - (n - s) = s := by omega
    rw [hns] at this
    exact this
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    exact euler_truncated_at_n n q c hq Us hUs
  | succ d ih =>
    intro hd_le
    have hd_le' : d ≤ n := by omega
    have ih_applied := ih hd_le'
    have hsn : n - (d + 1) < n := by omega
    have heq : n - (d + 1) + 1 = n - d := by omega
    have ih' : (∏ r ∈ Finset.Ioc (n - (d + 1) + 1) n, (1 - c * q ^ r))
              = ∑ k ∈ Finset.range (n + 1),
                  ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * (n - (d + 1) + 1)) * Us k := by
      rw [heq]
      exact ih_applied
    exact euler_truncated_step n q c hq Us hUs (n - (d + 1)) hsn ih'

/-- An "inverse function" `Us : ℕ → R` for the Pochhammer products always exists,
    by choosing inverses pointwise. -/
lemma exists_pochhammer_inverse {R : Type*} [CommRing R] {q : R} {n : ℕ}
    (hq : q ^ (n + 1) = 0) :
    ∃ Us : ℕ → R, ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1 := by
  classical
  have hunit : ∀ s : ℕ, IsUnit (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) :=
    fun s => isUnit_pochhammer_prod hq s
  refine ⟨fun s => ((hunit s).unit)⁻¹.val, fun s _ => ?_⟩
  exact (hunit s).unit.val_inv

/-- The reformulated LHS using inverses `Us`: rewrite `∏_{r∈(s,n]} (1-q^r) = P_n * U_s`.
    This is the result of Step 2 in proof.md. -/
lemma lhs_rewrite_using_inverses {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1) :
    (∑ s ∈ Finset.range (n + 1),
        q ^ (3 * s) *
          ((∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) *
            (∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r))))
      = (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r))
          * ∑ s ∈ Finset.range (n + 1),
              q ^ (3 * s) * Us s
                * (∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsn : s ≤ n := by
    have := Finset.mem_range.mp hs
    omega
  have hkey : (∏ r ∈ Finset.Ioc s n, (1 - q ^ r))
      = (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us s :=
    prod_Ioc_eq_full_mul_inverse s n q (Us s) hsn (hUs s hsn)
  rw [hkey]
  ring

/-- Algebraic simplification: `(Us k) * P_{k+2} = (1 - q^{k+1}) * (1 - q^{k+2})`.
    Here `P_{k+2} = P_k * (1-q^{k+1}) * (1-q^{k+2})` by definition. -/
lemma pochhammer_split_two {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r))
      = (∏ r ∈ Finset.Icc 1 k, (1 - q ^ r)) * (1 - q ^ (k + 1)) * (1 - q ^ (k + 2)) := by
  have h1 : Finset.Icc 1 (k + 2) = Finset.Icc 1 (k + 1) ∪ {k + 2} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
    omega
  have h2 : Finset.Icc 1 (k + 1) = Finset.Icc 1 k ∪ {k + 1} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
    omega
  have hd1 : Disjoint (Finset.Icc 1 (k + 1)) ({k + 2} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right, Finset.mem_Icc]
  have hd2 : Disjoint (Finset.Icc 1 k) ({k + 1} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right, Finset.mem_Icc]
  rw [h1, Finset.prod_union hd1, h2, Finset.prod_union hd2]
  simp [mul_assoc]

lemma inverse_times_extended_pochhammer {R : Type*} [CommRing R] (q : R) (Us : ℕ → R) (k : ℕ)
    (hUs : (∏ r ∈ Finset.Icc 1 k, (1 - q ^ r)) * Us k = 1) :
    Us k * (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r))
      = (1 - q ^ (k + 1)) * (1 - q ^ (k + 2)) := by
  rw [pochhammer_split_two]
  linear_combination ((1 - q ^ (k + 1)) * (1 - q ^ (k + 2))) * hUs

/-- The final assembly step: given a particular `Us : ℕ → R` with the inverse property,
    after substituting the Euler expansion (Step 3) and the q-geometric identity (Step 4),
    one obtains the RHS of the main identity.
    Specifically: P_n * Σ_s [q^{3s} * Us s * Σ_k [(-1)^k c^k q^{T_k + ks} Us k]]
                = Σ_k [(-1)^k c^k * q^{T_k} * (1 - q^{k+1}) * (1 - q^{k+2})]
    using:
      - sum swap and reorder
      - Σ_s q^{(k+3)s} Us s = P_{k+2} * Us n (q-geometric)
      - P_n * Us n = 1
      - Us k * P_{k+2} = (1-q^{k+1})(1-q^{k+2}) (inverse_times_extended_pochhammer) -/
lemma lhs_swap_and_factor {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (Us : ℕ → R) :
    (∑ s ∈ Finset.range (n + 1),
        q ^ (3 * s) * Us s
          * (∑ k ∈ Finset.range (n + 1),
              ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k))
      = ∑ k ∈ Finset.range (n + 1),
          ((-1 : R) ^ k * c ^ k) * q ^ (triangular k) * Us k
            * (∑ s ∈ Finset.range (n + 1), q ^ ((k + 3) * s) * Us s) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h1 : q ^ (triangular k + k * s) = q ^ triangular k * q ^ (k * s) := pow_add q _ _
  have h2 : q ^ ((k + 3) * s) = q ^ (k * s) * q ^ (3 * s) := by
    rw [← pow_add]; congr 1; ring
  rw [h1, h2]
  ring

lemma inner_sum_eq_pochhammer {R : Type*} [CommRing R] (n : ℕ) (q : R)
    (hq : q ^ (n + 1) = 0) (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1) :
    ∀ k ∈ Finset.range (n + 1),
      (∑ s ∈ Finset.range (n + 1), q ^ ((k + 3) * s) * Us s)
        = (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * Us n := by
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact q_geometric_truncated n q hq k hk' Us hUs

lemma term_simplify_final {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (Us : ℕ → R) (k : ℕ)
    (hUsk : (∏ r ∈ Finset.Icc 1 k, (1 - q ^ r)) * Us k = 1) :
    (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r))
        * (((-1 : R) ^ k * c ^ k) * q ^ (triangular k) * Us k
            * ((∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * Us n))
      = ((-1 : R) ^ k * c ^ k) * q ^ (triangular k)
          * (1 - q ^ (k + 1)) * (1 - q ^ (k + 2))
          * ((∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us n) := by
  have hUk : Us k * (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r))
      = (1 - q ^ (k + 1)) * (1 - q ^ (k + 2)) :=
    inverse_times_extended_pochhammer q Us k hUsk
  calc (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r))
        * (((-1 : R) ^ k * c ^ k) * q ^ (triangular k) * Us k
            * ((∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r)) * Us n))
      = ((-1 : R) ^ k * c ^ k) * q ^ (triangular k) *
          (Us k * (∏ r ∈ Finset.Icc 1 (k + 2), (1 - q ^ r))) *
          ((∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us n) := by ring
    _ = ((-1 : R) ^ k * c ^ k) * q ^ (triangular k) *
          ((1 - q ^ (k + 1)) * (1 - q ^ (k + 2))) *
          ((∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us n) := by rw [hUk]
    _ = ((-1 : R) ^ k * c ^ k) * q ^ (triangular k) *
          (1 - q ^ (k + 1)) * (1 - q ^ (k + 2)) *
          ((∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us n) := by ring

lemma final_assembly {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0)
    (Us : ℕ → R)
    (hUs : ∀ s ≤ n, (∏ r ∈ Finset.Icc 1 s, (1 - q ^ r)) * Us s = 1) :
    (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r))
        * ∑ s ∈ Finset.range (n + 1),
            q ^ (3 * s) * Us s
              * (∑ k ∈ Finset.range (n + 1),
                  ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k)
      = ∑ k ∈ Finset.range (n + 1),
          ((-1 : R) ^ k * c ^ k) *
            q ^ (triangular k) *
            (1 - q ^ (k + 1)) *
            (1 - q ^ (k + 2)) := by
  rw [lhs_swap_and_factor, Finset.mul_sum]
  have hInner := inner_sum_eq_pochhammer n q hq Us hUs
  have hUsn : (∏ r ∈ Finset.Icc 1 n, (1 - q ^ r)) * Us n = 1 := hUs n le_rfl
  apply Finset.sum_congr rfl
  intro k hk
  rw [hInner k hk]
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
  have hUsk : (∏ r ∈ Finset.Icc 1 k, (1 - q ^ r)) * Us k = 1 := hUs k hkn
  rw [term_simplify_final n q c Us k hUsk, hUsn, mul_one]

/-- **Abstract algebraic identity (Steps 3–6 of proof.md).**
Given any commutative ring `R`, a nilpotent element `q : R` with
`q^(n+1) = 0`, and any scalar `c : R`, the following equality holds in `R`:
  ∑_{s=0}^n q^{3s} * (∏_{r∈(s,n]} (1-q^r)) * (∏_{r∈(s,n]} (1-c*q^r))
  = ∑_{k=0}^n ((-1)^k * c^k) * q^{T_k} * (1-q^{k+1}) * (1-q^{k+2})
where `T_k = triangular k = k(k+1)/2`. -/
lemma abstract_qseries_identity {R : Type*} [CommRing R] (n : ℕ) (q c : R)
    (hq : q ^ (n + 1) = 0) :
    (∑ s ∈ Finset.range (n + 1),
        q ^ (3 * s) *
          ((∏ r ∈ Finset.Ioc s n, (1 - q ^ r)) *
            (∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r))))
      =
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : R) ^ k * c ^ k) *
        q ^ (triangular k) *
        (1 - q ^ (k + 1)) *
        (1 - q ^ (k + 2)) := by
  obtain ⟨Us, hUs⟩ := exists_pochhammer_inverse hq
  rw [lhs_rewrite_using_inverses n q c Us hUs]
  rw [show (∑ s ∈ Finset.range (n + 1), q ^ (3 * s) * Us s
            * (∏ r ∈ Finset.Ioc s n, (1 - c * q ^ r)))
        = ∑ s ∈ Finset.range (n + 1), q ^ (3 * s) * Us s
            * (∑ k ∈ Finset.range (n + 1),
                ((-1 : R) ^ k * c ^ k) * q ^ (triangular k + k * s) * Us k) from by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_range] at hs
      rw [euler_truncated_expansion n q c hq Us hUs s (Nat.lt_succ_iff.mp hs)]]
  exact final_assembly n q c hq Us hUs

/-- Push the quotient map `Ideal.Quotient.mk` through the LHS sum-of-products. -/
lemma quot_map_LHS (ω : ℂ) (n : ℕ) :
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}))
      (∑ s ∈ Finset.range (n + 1),
        Polynomial.X ^ (3 * s) *
          ((∏ r ∈ Finset.Ioc s n, (1 - Polynomial.X ^ r)) *
            (∏ r ∈ Finset.Ioc s n, (1 - Polynomial.C (ω ^ 2) * Polynomial.X ^ r))))
      =
    ∑ s ∈ Finset.range (n + 1),
      ((Ideal.Quotient.mk
          (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (3 * s) *
        ((∏ r ∈ Finset.Ioc s n, (1 -
            ((Ideal.Quotient.mk
                (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ r)) *
          (∏ r ∈ Finset.Ioc s n, (1 -
              ((Ideal.Quotient.mk
                  (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}))
                (Polynomial.C (ω ^ 2))) *
              ((Ideal.Quotient.mk
                  (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ r))) := by
  simp only [map_sum, map_mul, map_prod, map_pow, map_sub, map_one]

lemma quot_map_H_poly_summand (ω : ℂ) (n k : ℕ) :
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}))
      (Polynomial.C ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        Polynomial.X ^ (triangular k) *
        (1 - Polynomial.X ^ (k + 1)) *
        (1 - Polynomial.X ^ (k + 2)))
      =
    ((-1 : Polynomial ℂ ⧸ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}) ^ k *
        ((Ideal.Quotient.mk
            (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}))
          (Polynomial.C (ω ^ 2))) ^ k) *
      ((Ideal.Quotient.mk
          (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (triangular k) *
      (1 - ((Ideal.Quotient.mk
                (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (k + 1)) *
      (1 - ((Ideal.Quotient.mk
                (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (k + 2)) := by
  have h₂ : Polynomial.C ((-1 : ℂ) ^ k * ω ^ (2 * k))
      = (Polynomial.C (-1 : ℂ)) ^ k * (Polynomial.C (ω ^ 2)) ^ k := by
    rw [show (ω : ℂ) ^ (2 * k) = (ω ^ 2) ^ k from by rw [pow_mul],
      Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_pow]
  rw [h₂]
  simp

/-- Push the quotient map through `H_poly ω n`.
Uses:
* Ring hom respects finite sums, products, multiplication, subtraction,
  one, and powers.
* For the constant `(-1)^k * ω^(2k)`:
    `Polynomial.C ((-1)^k * ω^(2k)) = Polynomial.C ((-1)^k) * Polynomial.C (ω^2)^k`
  (by `Polynomial.C_mul`, `Polynomial.C_pow`, ring algebra in `ℂ`).
* `(Ideal.Quotient.mk _) (Polynomial.C (-1)) = -1` in the quotient ring
  (since `Polynomial.C` and `Ideal.Quotient.mk` are ring homs and both
  preserve `-1`).
The right-hand side keeps `π(C(ω^2))` as a single scalar element `c` of
the quotient ring, matching the form expected by `abstract_qseries_identity`. -/
lemma quot_map_H_poly (ω : ℂ) (n : ℕ) :
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) (H_poly ω n)
      =
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : Polynomial ℂ ⧸ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}) ^ k *
          ((Ideal.Quotient.mk
              (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}))
            (Polynomial.C (ω ^ 2))) ^ k) *
        ((Ideal.Quotient.mk
            (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (triangular k) *
        (1 - ((Ideal.Quotient.mk
                  (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (k + 1)) *
        (1 - ((Ideal.Quotient.mk
                  (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) Polynomial.X) ^ (k + 2)) := by
  unfold H_poly
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact quot_map_H_poly_summand ω n k

/-- **Main quotient-ring q-series identity.** In the quotient ring
`R := Polynomial ℂ ⧸ Ideal.span {X^(n+1)}`, the images of the factored `G_omega`
and `H_poly` agree, packaging the truncated Euler expansion and q-geometric identity. -/
lemma G_omega_factored_quot_eq_H_poly_quot (ω : ℂ) (n : ℕ)
    (_hω3 : ω ^ 3 = 1) (_hω1 : ω ≠ 1) :
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)}))
      (∑ s ∈ Finset.range (n + 1),
        Polynomial.X ^ (3 * s) *
          ((∏ r ∈ Finset.Ioc s n, (1 - Polynomial.X ^ r)) *
            (∏ r ∈ Finset.Ioc s n, (1 - Polynomial.C (ω ^ 2) * Polynomial.X ^ r))))
      =
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) (H_poly ω n) := by
  rw [quot_map_LHS, quot_map_H_poly]
  exact abstract_qseries_identity n _ _ (quot_X_pow_nilpotent n)

/-- **Main quotient-ring identity (Steps 4–7 of proof.md).**
In the quotient ring `R := Polynomial ℂ ⧸ Ideal.span {X^(n+1)}`, the
images of `G_omega ω n` and `H_poly ω n` are equal. -/
lemma G_omega_quot_eq_H_poly_quot (ω : ℂ) (n : ℕ)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) (G_omega ω n)
      =
    (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)})) (H_poly ω n) := by
  have hω : ω ^ 2 + ω + 1 = 0 := omega_sq_sum_eq_zero ω hω3 hω1
  rw [G_omega_factored ω n hω]
  exact G_omega_factored_quot_eq_H_poly_quot ω n hω3 hω1

/-- **Main lemma (Step 1 & 8).** Combine the quotient-ring equality with the
standard equivalence `p ∈ I ↔ π(p) = 0`. -/
lemma G_omega_sub_H_poly_mem_ideal (ω : ℂ) (n : ℕ)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    G_omega ω n - H_poly ω n ∈
      Ideal.span {(Polynomial.X : Polynomial ℂ) ^ (n + 1)} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact G_omega_quot_eq_H_poly_quot ω n hω3 hω1

/-- **NEW helper / q-series content.**
The `n`-th coefficient of the explicit generating polynomial `G_omega ω n`
equals the `n`-th coefficient of `H_poly ω n` whenever `ω^3 = 1` and `ω ≠ 1`.
Proof: by Helper (C), `G_omega ω n - H_poly ω n` lies in the ideal generated
by `X^{n+1}`. By Helper (A), this implies equality of `n`-th coefficients. -/
lemma G_omega_coeff_eq_H_poly_coeff (ω : ℂ) (n : ℕ)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (G_omega ω n).coeff n = (H_poly ω n).coeff n := by
  exact coeff_eq_of_sub_mem_span_X_pow n (G_omega ω n) (H_poly ω n)
    (G_omega_sub_H_poly_mem_ideal ω n hω3 hω1)

lemma omega_pow4_pow2_one (ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ^ 4 + ω ^ 2 + 1 = 0 := by
  have h₁ : ω ^ 2 + ω + 1 = 0 := omega_sq_sum_eq_zero ω hω3 hω1
  have h₄ : ω ^ 4 = ω := by
    rw [show (4 : ℕ) = 3 + 1 by rfl, pow_add, hω3, one_mul, pow_one]
  linear_combination h₁ + h₄

/-- **Helper 2.** Coefficient extraction: `(H_poly ω n).coeff n` equals an explicit finite
sum over `k ∈ Finset.range (n + 1)` of products of `(-1)^k * ω^(2k)` with four Kronecker
deltas, one for each monomial of `X^(triangular k) * (1 - X^(k+1)) * (1 - X^(k+2))`. -/
lemma H_poly_coeff_eq_indicator_sum (ω : ℂ) (n : ℕ) :
    (H_poly ω n).coeff n =
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) -
         (if triangular k + (k + 2) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0)) := by
  unfold H_poly
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  exact H_poly_summand_coeff ω n k

/-- If `n = triangular t` with `1 ≤ n` and `∀ r, n ≠ triangular r + 1`, then `t ≥ 2`. -/
lemma triangular_eq_implies_ge_two (n t : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1) (ht : n = triangular t) : 2 ≤ t := by
  by_contra hlt
  push_neg at hlt
  interval_cases t
  · simp [triangular] at ht; omega
  · have h10 : triangular 1 = triangular 0 + 1 := by simp [triangular]
    rw [h10] at ht
    exact h 0 ht

/-- The reduced sum (with third indicator removed) vanishes for `n` not triangular. -/
lemma reduced_sum_zero_of_not_triangular (n : ℕ) (ω : ℂ)
    (hnotri : ∀ t : ℕ, n ≠ triangular t) :
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have h1 : (if triangular k = n then (1 : ℂ) else 0) = 0 := by
    rw [if_neg]; intro he; exact hnotri k he.symm
  have h2 : (if triangular k + (k + 1) = n then (1 : ℂ) else 0) = 0 := by
    rw [if_neg]; intro he
    apply hnotri (k + 1)
    rw [triangular_succ]; omega
  have h3 : (if triangular k + (2 * k + 3) = n then (1 : ℂ) else 0) = 0 := by
    rw [if_neg]; intro he
    apply hnotri (k + 2)
    rw [triangular_add_two]; omega
  rw [h1, h2, h3]; ring

/-- The main cancellation: For `t ≥ 2`, the three contributing terms satisfy:
`(-1)^t ω^(2t) - (-1)^(t-1) ω^(2(t-1)) + (-1)^(t-2) ω^(2(t-2)) = 0`,
using `ω^4 + ω^2 + 1 = 0`. -/
lemma cancellation_at_triangular (t : ℕ) (ht : 2 ≤ t) (ω : ℂ)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (-1 : ℂ) ^ t * ω ^ (2 * t) -
      (-1) ^ (t - 1) * ω ^ (2 * (t - 1)) +
      (-1) ^ (t - 2) * ω ^ (2 * (t - 2)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  have homega : ω ^ 4 + ω ^ 2 + 1 = 0 := omega_pow4_pow2_one ω hω3 hω1
  rw [show 2 + k - 1 = k + 1 from by omega, show 2 + k - 2 = k from by omega,
    show 2 * (2 + k) = 2 * k + 4 from by ring, show 2 * (k + 1) = 2 * k + 2 from by ring,
    show ((-1 : ℂ))^(2 + k) = (-1)^k from by rw [pow_add]; ring,
    show ((-1 : ℂ))^(k + 1) = -(-1)^k from by rw [pow_succ]; ring,
    show ω^(2*k + 4) = ω^(2*k) * ω^4 from pow_add _ _ _,
    show ω^(2*k + 2) = ω^(2*k) * ω^2 from pow_add _ _ _]
  linear_combination ((-1 : ℂ)^k * ω^(2*k)) * homega

/-- For `n = T_t` with `t ≥ 2`, the sum over `k ∈ range (n+1)` of the indicator-weighted sum
equals exactly the three contributing terms at `k = t-2`, `k = t-1`, `k = t`. -/
lemma reduced_sum_eq_three_terms (n t : ℕ) (ht : 2 ≤ t) (htn : n = triangular t)
    (ω : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0)) =
    (-1 : ℂ) ^ t * ω ^ (2 * t) -
      (-1) ^ (t - 1) * ω ^ (2 * (t - 1)) +
      (-1) ^ (t - 2) * ω ^ (2 * (t - 2)) := by
  have hbounds := indices_le_n n t ht htn
  obtain ⟨hle2, hle1, hle0⟩ := hbounds
  set S : Finset ℕ := {t - 2, t - 1, t} with hS_def
  have hS_sub : S ⊆ Finset.range (n + 1) := by
    intro k hk
    simp [hS_def] at hk
    rcases hk with rfl | rfl | rfl
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle2)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle1)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle0)
  rw [← Finset.sum_subset hS_sub (fun k hk hkS => by
    have hkne0 : k ≠ t := by
      intro h; apply hkS; simp [hS_def, h]
    have hkne1 : k ≠ t - 1 := by
      intro h; apply hkS; simp [hS_def, h]
    have hkne2 : k ≠ t - 2 := by
      intro h; apply hkS; simp [hS_def, h]
    rw [indicator_expr_eq_zero_of_ne n t k ht htn hkne0 hkne1 hkne2]
    ring)]
  have hne01 : t - 1 ≠ t := by omega
  have hne02 : t - 2 ≠ t := by omega
  have hne12 : t - 2 ≠ t - 1 := by omega
  rw [show S = {t - 2, t - 1, t} from rfl,
    Finset.sum_insert (by simp; exact ⟨hne12, hne02⟩),
    Finset.sum_insert (by simp; exact hne01), Finset.sum_singleton,
    indicator_expr_at_t_sub_two n t ht htn, indicator_expr_at_t_sub_one n t ht htn,
    indicator_expr_at_t n t ht htn]
  ring

/-- The reduced sum (with third indicator removed) vanishes for `n = triangular t` with `t ≥ 2`. -/
lemma reduced_sum_zero_of_triangular (n t : ℕ) (ht : 2 ≤ t) (htn : n = triangular t)
    (ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0)) = 0 := by
  rw [reduced_sum_eq_three_terms n t ht htn ω]
  exact cancellation_at_triangular t ht ω hω3 hω1

/-- **Helper 3.** The main indicator-sum vanishing lemma. -/
lemma indicator_sum_vanishes (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1)
    (ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) -
         (if triangular k + (k + 2) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0)) = 0 := by
  have h3 : ∀ k, (if triangular k + (k + 2) = n then (1 : ℂ) else 0) = 0 := by
    intro k
    rw [if_neg]
    intro he
    apply h (k + 1)
    rw [triangular_succ]; omega
  have hrewrite : ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) -
         (if triangular k + (k + 2) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0))
    = ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k * ω ^ (2 * k)) *
        ((if triangular k = n then (1 : ℂ) else 0) -
         (if triangular k + (k + 1) = n then 1 else 0) +
         (if triangular k + (2 * k + 3) = n then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [h3 k]; ring
  rw [hrewrite]
  by_cases hcase : ∃ t, n = triangular t
  · obtain ⟨t, ht⟩ := hcase
    have ht2 : 2 ≤ t := triangular_eq_implies_ge_two n t hn h ht
    exact reduced_sum_zero_of_triangular n t ht2 ht ω hω3 hω1
  · push_neg at hcase
    exact reduced_sum_zero_of_not_triangular n ω hcase

/-! ## Inserted helpers complete -/

/-- **Factor expansion (pure algebra).** Each local factor of the product in
`G_omega` is rewritten as a 3-term sum over the multiplicity `e ∈ {0, 1, 2}`
of the part `r`:
`1 + ω X^r + ω² X^{2r} = ∑_{e ∈ Finset.range 3} C(ω^e) · X^{e·r}`.

Pure ring/polynomial identity: expand `Finset.sum_range_succ` three times,
then simplify with `pow_zero`, `pow_one`, `mul_one`, `Polynomial.C_1`. No
hypotheses on `ω` or `r`. -/
lemma factor_eq_sum_three (ω : ℂ) (r : ℕ) :
    (1 + Polynomial.C ω * Polynomial.X ^ r +
        Polynomial.C (ω ^ 2) * Polynomial.X ^ (2 * r) : Polynomial ℂ) =
    ∑ e ∈ Finset.range 3, Polynomial.C (ω ^ e) * Polynomial.X ^ (e * r) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp

/-- **Step A: Coefficient extraction.** The `n`-th coefficient of `G_omega ω n` equals the
explicit finite sum `coeffSum n ω`. -/
lemma coeff_G_omega_eq_coeffSum (n : ℕ) (ω : ℂ) :
    (G_omega ω n).coeff n = coeffSum n ω := by
  unfold G_omega coeffSum
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  exact coeff_G_omega_term_eq_filtered_sum n s ω

/-- **Combinatorial bijection.** The explicit `(s, f)`-sum `coeffSum n ω` equals the
τ-weighted sum over `D3Set n`, via the bijection `μ ↦ (smallestPart μ, count μ)`. -/
lemma coeffSum_eq_partition_sum (n : ℕ) (ω : ℂ) (hfin : (D3Set n).Finite) :
    coeffSum n ω = ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) := by
  rw [sum_partition_group_by_smallestPart n ω hfin]
  unfold coeffSum
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hs
  refine Finset.sum_bij'
      (fun f _ => fromPair s n f)
      (fun μ _ => toCounts μ s n)
      ?i_mem ?j_mem ?left_inv ?right_inv ?weights
  case i_mem =>
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨_, hdeg⟩ := hf
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fromPair_mem_D3Set s n hs f hdeg, smallestPart_fromPair s n f⟩
  case j_mem =>
    intro μ hμ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hμ
    obtain ⟨hμD3, hsmall⟩ := hμ
    rw [Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr (fun _ => Finset.mem_univ _), ?_⟩
    have := toCounts_degree_constraint μ n hμD3
    rw [hsmall] at this
    exact this
  case left_inv =>
    intro f _
    exact toCounts_fromPair s n f
  case right_inv =>
    intro μ hμ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hμ
    obtain ⟨hμD3, hsmall⟩ := hμ
    have := fromPair_toCounts μ n hμD3
    rw [hsmall] at this
    exact this
  case weights =>
    intro f _
    rw [tau_fromPair]

/-! ## More helper lemmas -/

/-- **Step B / q-series identity.** Working modulo `X^{n+1}`, the truncated Euler
q-Pochhammer expansion and the truncated q-geometric summation transform the explicit
`(s, f)`-sum `coeffSum n ω` into `(H_poly ω n).coeff n`. Requires `ω^3 = 1` and `ω ≠ 1`. -/
lemma coeffSum_eq_H_poly_coeff (ω : ℂ) (n : ℕ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    coeffSum n ω = (H_poly ω n).coeff n := by
  rw [← coeff_G_omega_eq_coeffSum]
  exact G_omega_coeff_eq_H_poly_coeff ω n hω3 hω1

/-- **Step C / vanishing of the Euler-side coefficient.** Under the hypotheses
`1 ≤ n`, `n ≠ triangular r + 1` for all `r`, and `ω^3 = 1, ω ≠ 1`,
the `n`-th coefficient of the explicit polynomial `H_poly ω n` vanishes. -/
lemma H_poly_coeff_n_eq_zero (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1)
    (ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (H_poly ω n).coeff n = 0 := by
  rw [H_poly_coeff_eq_indicator_sum]
  exact indicator_sum_vanishes n hn h ω hω3 hω1

/-- The `n`-th coefficient of `G_omega ω n` vanishes under the nonexceptional hypothesis. -/
lemma coeff_G_omega_vanish (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1)
    (ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (G_omega ω n).coeff n = 0 := by
  rw [coeff_G_omega_eq_coeffSum n ω, coeffSum_eq_H_poly_coeff ω n hω3 hω1]
  exact H_poly_coeff_n_eq_zero n hn h ω hω3 hω1

/-- Coefficient extraction (combinatorial bijection step of Andrews–Dhar). -/
lemma coeff_G_omega_eq_sum (n : ℕ) (ω : ℂ) (hfin : (D3Set n).Finite) :
    (G_omega ω n).coeff n = ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) := by
  rw [coeff_G_omega_eq_coeffSum, coeffSum_eq_partition_sum n ω hfin]

/-- **Q-series vanishing (main content).** -/
lemma d3_omega_finite_sum_zero (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1)
    (ω : ℂ) (hω3 : ω^3 = 1) (hω1 : ω ≠ 1)
    (hfin : (D3Set n).Finite) :
    ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) = 0 :=
  (coeff_G_omega_eq_sum n ω hfin).symm.trans (coeff_G_omega_vanish n hn h ω hω3 hω1)

lemma D3iSet_subset_D3Set (i n : ℕ) : D3iSet i n ⊆ D3Set n :=
  fun _ hμ => hμ.1

/-- For any `ω : ℂ` with `ω^3 = 1` and any `k : ℕ`, `ω^k = ω^(k % 3)`. -/
lemma omega_pow_eq_mod3 (ω : ℂ) (hω3 : ω ^ 3 = 1) (k : ℕ) : ω ^ k = ω ^ (k % 3) := by
  conv_lhs => rw [← Nat.mod_add_div k 3]
  simp [pow_add, pow_mul, hω3]

lemma omega_pow_tau_of_mem (i n : ℕ) (_hi : i < 3) (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (μ : List ℕ) (hμ : μ ∈ D3iSet i n) : ω ^ (tau μ) = ω ^ i := by
  have h₁ : tau μ % 3 = i % 3 := hμ.2
  rw [omega_pow_eq_mod3 ω hω3 (tau μ), h₁, ← omega_pow_eq_mod3 ω hω3 i]

/-- For each `i < 3` and any finite version `hfin : (D3iSet i n).Finite`, the sum of
`ω^(tau μ)` over `hfin.toFinset` equals `ω^i * D3i i n`.

This follows because on `D3iSet i n`, `ω^(tau μ) = ω^i` is constant, so the sum is
`ω^i * (D3iSet i n).Finite.toFinset.card = ω^i * (D3iSet i n).ncard = ω^i * D3i i n`. -/
lemma sum_D3iSet_eq (i n : ℕ) (hi : i < 3) (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (hfin : (D3iSet i n).Finite) :
    ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) = ω ^ i * (D3i i n : ℂ) := by
  have hconst : ∀ μ ∈ hfin.toFinset, ω ^ (tau μ) = ω ^ i := by
    intro μ hμ
    have hμ' : μ ∈ D3iSet i n := (Set.Finite.mem_toFinset hfin).1 hμ
    exact omega_pow_tau_of_mem i n hi ω hω3 μ hμ'
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  unfold D3i
  rw [Set.ncard_eq_toFinset_card (D3iSet i n) hfin]

/-- The sum `∑ μ ∈ hfin.toFinset, ω ^ (tau μ)` splits into a sum over the three
residue-class finsets, using `D3Set_eq_union` and `D3iSet_disjoint_of_ne`. -/
lemma sum_D3Set_split (n : ℕ) (ω : ℂ)
    (hfin : (D3Set n).Finite)
    (hfin0 : (D3iSet 0 n).Finite)
    (hfin1 : (D3iSet 1 n).Finite)
    (hfin2 : (D3iSet 2 n).Finite) :
    ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) =
      (∑ μ ∈ hfin0.toFinset, ω ^ (tau μ)) +
      (∑ μ ∈ hfin1.toFinset, ω ^ (tau μ)) +
      (∑ μ ∈ hfin2.toFinset, ω ^ (tau μ)) := by
  have h₁ : hfin.toFinset = (hfin0.toFinset ∪ hfin1.toFinset ∪ hfin2.toFinset) := by
    ext μ
    simp only [Set.Finite.mem_toFinset, Finset.mem_union]
    rw [show (μ ∈ D3Set n) ↔ (μ ∈ D3iSet 0 n ∪ D3iSet 1 n ∪ D3iSet 2 n) from
      by rw [← D3Set_eq_union]]
    simp [Set.mem_union]
  rw [h₁]
  have hd01 : Disjoint hfin0.toFinset hfin1.toFinset := by
    rw [Finset.disjoint_left]
    intro μ hμ0 hμ1
    simp only [Set.Finite.mem_toFinset] at hμ0 hμ1
    exact (D3iSet_disjoint_of_ne n (by norm_num) (by norm_num) (by norm_num)).le_bot ⟨hμ0, hμ1⟩
  have hd02 : Disjoint hfin0.toFinset hfin2.toFinset := by
    rw [Finset.disjoint_left]
    intro μ hμ0 hμ2
    simp only [Set.Finite.mem_toFinset] at hμ0 hμ2
    exact (D3iSet_disjoint_of_ne n (by norm_num) (by norm_num) (by norm_num)).le_bot ⟨hμ0, hμ2⟩
  have hd12 : Disjoint hfin1.toFinset hfin2.toFinset := by
    rw [Finset.disjoint_left]
    intro μ hμ1 hμ2
    simp only [Set.Finite.mem_toFinset] at hμ1 hμ2
    exact (D3iSet_disjoint_of_ne n (by norm_num) (by norm_num) (by norm_num)).le_bot ⟨hμ1, hμ2⟩
  have hd : Disjoint (hfin0.toFinset ∪ hfin1.toFinset) hfin2.toFinset := by
    rw [Finset.disjoint_union_left]
    exact ⟨hd02, hd12⟩
  rw [Finset.sum_union hd, Finset.sum_union hd01]

/-- **Combinatorial repackaging.**
For any `ω : ℂ` with `ω^3 = 1`, the finite weighted sum over `D3Set n` equals the
cube-root-filter linear combination of the three residue-class counts. -/
lemma d3_omega_finite_sum_eq_combo (n : ℕ)
    (ω : ℂ) (hω3 : ω ^ 3 = 1)
    (hfin : (D3Set n).Finite) :
    ∑ μ ∈ hfin.toFinset, ω ^ (tau μ) =
      (D3i 0 n : ℂ) + ω * (D3i 1 n : ℂ) + ω ^ 2 * (D3i 2 n : ℂ) := by
  have hfin0 : (D3iSet 0 n).Finite := hfin.subset (D3iSet_subset_D3Set 0 n)
  have hfin1 : (D3iSet 1 n).Finite := hfin.subset (D3iSet_subset_D3Set 1 n)
  have hfin2 : (D3iSet 2 n).Finite := hfin.subset (D3iSet_subset_D3Set 2 n)
  rw [sum_D3Set_split n ω hfin hfin0 hfin1 hfin2,
    sum_D3iSet_eq 0 n (by norm_num) ω hω3 hfin0,
    sum_D3iSet_eq 1 n (by norm_num) ω hω3 hfin1,
    sum_D3iSet_eq 2 n (by norm_num) ω hω3 hfin2]
  ring

lemma D3i_omega_sum_eq_zero (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1)
    (ω : ℂ) (hω3 : ω^3 = 1) (hω1 : ω ≠ 1) :
    (D3i 0 n : ℂ) + ω * (D3i 1 n : ℂ) + ω^2 * (D3i 2 n : ℂ) = 0 := by
  have hfin := D3Set_finite n
  exact (d3_omega_finite_sum_eq_combo n ω hω3 hfin).symm.trans
    (d3_omega_finite_sum_zero n hn h ω hω3 hω1 hfin)

/-- **Linear algebra over `ℂ`.** For `ω : ℂ` with `ω^3 = 1` and `ω ≠ 1`,
the two equations `a₀ + ω · a₁ + ω² · a₂ = 0` and `a₀ + ω² · a₁ + ω · a₂ = 0`
force `a₀ = a₁ ∧ a₁ = a₂`. -/
lemma cube_root_linear_system (a₀ a₁ a₂ : ℂ) (ω : ℂ) (hω3 : ω^3 = 1) (hω1 : ω ≠ 1)
    (e1 : a₀ + ω * a₁ + ω^2 * a₂ = 0)
    (e2 : a₀ + ω^2 * a₁ + ω * a₂ = 0) :
    a₀ = a₁ ∧ a₁ = a₂ := by
  grind

lemma D3i_eq_of_nonexceptional (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1) :
    D3i 0 n = D3i 1 n ∧ D3i 1 n = D3i 2 n := by
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root
  have hω2_3 : (ω^2)^3 = 1 := by
    rw [show (ω^2)^3 = (ω^3)^2 from by ring, hω3]; ring
  have hω2_1 : ω^2 ≠ 1 := by
    intro heq
    apply hω1
    have : ω^3 = ω := by rw [show ω^3 = ω * ω^2 from by ring, heq, mul_one]
    exact this.symm.trans hω3
  have e1 : (D3i 0 n : ℂ) + ω * (D3i 1 n : ℂ) + ω^2 * (D3i 2 n : ℂ) = 0 :=
    D3i_omega_sum_eq_zero n hn h ω hω3 hω1
  have e2' : (D3i 0 n : ℂ) + ω^2 * (D3i 1 n : ℂ) + (ω^2)^2 * (D3i 2 n : ℂ) = 0 :=
    D3i_omega_sum_eq_zero n hn h (ω^2) hω2_3 hω2_1
  have hω4 : (ω^2)^2 = ω := by
    rw [show (ω^2)^2 = ω^3 * ω from by ring, hω3, one_mul]
  rw [hω4] at e2'
  obtain ⟨h01, h12⟩ := cube_root_linear_system _ _ _ ω hω3 hω1 e1 e2'
  exact ⟨by exact_mod_cast h01, by exact_mod_cast h12⟩

/-! ## `D3iSet_finite` (needed for `D3_eq_sum_D3i`) -/

/-- Each `D3iSet i n` is finite, as a subset of the finite set `D3Set n`. -/
lemma D3iSet_finite (i n : ℕ) : (D3iSet i n).Finite :=
  (D3Set_finite n).subset (D3iSet_subset_D3Set i n)

/-- The set `D3Set n` is the disjoint union of the three residue-class subsets
`D3iSet 0 n`, `D3iSet 1 n`, `D3iSet 2 n`. -/
lemma D3_eq_sum_D3i (n : ℕ) :
    D3 n = D3i 0 n + D3i 1 n + D3i 2 n := by
  unfold D3 D3i
  rw [D3Set_eq_union n]
  have h01 : Disjoint (D3iSet 0 n) (D3iSet 1 n) :=
    D3iSet_disjoint_of_ne n (by norm_num) (by norm_num) (by norm_num)
  have h02 : Disjoint (D3iSet 0 n) (D3iSet 2 n) :=
    D3iSet_disjoint_of_ne n (by norm_num) (by norm_num) (by norm_num)
  have h12 : Disjoint (D3iSet 1 n) (D3iSet 2 n) :=
    D3iSet_disjoint_of_ne n (by norm_num) (by norm_num) (by norm_num)
  have hf0 : (D3iSet 0 n).Finite := D3iSet_finite 0 n
  have hf1 : (D3iSet 1 n).Finite := D3iSet_finite 1 n
  have hf2 : (D3iSet 2 n).Finite := D3iSet_finite 2 n
  rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨h02, h12⟩) (hf0.union hf1) hf2,
      Set.ncard_union_eq h01 hf0 hf1]

-- Main Statement

theorem D3_equidistribution (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ r : ℕ, n ≠ triangular r + 1) :
    D3i 0 n = D3i 1 n ∧ D3i 1 n = D3i 2 n ∧ 3 * D3i 0 n = D3 n := by
  obtain ⟨h01, h12⟩ := D3i_eq_of_nonexceptional n hn h
  refine ⟨h01, h12, ?_⟩
  have hsum : D3 n = D3i 0 n + D3i 1 n + D3i 2 n := D3_eq_sum_D3i n
  rw [hsum, ← h01, ← h01.trans h12]
  ring

end AndrewsDharD3
