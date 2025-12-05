import Mathlib


open scoped Finset

variable {R : Type*} [CommRing R]

open MvPolynomial

open Finsupp

/-- Lemma 2.2 :
A multivariate polynomial that vanishes on a large product finset is the zero polynomial. -/
lemma eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
      exact MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S Hdeg Heval

/-- Definition of elimination polynomials g_i -/
noncomputable def elimination_polynomials (A : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
  fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a)

noncomputable def reduce_polynomial_degrees (P : MvPolynomial (Fin (k + 1)) (ZMod p))
    (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) : MvPolynomial (Fin (k + 1)) (ZMod p) :=

  P.support.sum fun m =>
    let coeff := P.coeff m
    let needs_replacement : Finset (Fin (k + 1)) :=
      Finset.filter (fun i => m i > c i) Finset.univ
    if h : needs_replacement.Nonempty then
      let i : Fin (k + 1) := needs_replacement.min' h
      let new_m : (Fin (k + 1)) →₀ ℕ :=
        Finsupp.update m i (m i - (c i + 1))
      coeff • (MvPolynomial.monomial new_m 1) * (MvPolynomial.X i ^ (c i + 1) - g i)
    else
      coeff • MvPolynomial.monomial m 1

lemma reduce_polynomial_degrees_eq (P : MvPolynomial (Fin (k + 1)) (ZMod p))
  (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p))
  (c : Fin (k + 1) → ℕ) :
  reduce_polynomial_degrees P g c =
    P.support.sum (fun m =>
      let coeff := P.coeff m
      let needs_replacement := Finset.filter (fun i => m i > c i) Finset.univ
      if h : needs_replacement.Nonempty then
        let i := needs_replacement.min' h
        let new_m := Finsupp.update m i (m i - (c i + 1))
        coeff • MvPolynomial.monomial new_m 1 * (MvPolynomial.X i ^ (c i + 1) - g i)
      else
        coeff • MvPolynomial.monomial m 1) := rfl

/-- The sum of variables polynomial -/
noncomputable def sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  ∑ i, MvPolynomial.X i

/-- The restricted sumset S from the ANR theorem -/
def restricted_sumset (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter (fun f => h.eval f ≠ 0)).image (fun f => ∑ i, f i)

/-- The polynomial Q = h * ∏_{e∈E} (∑X_i - e) -/
noncomputable def construction_polynomial
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  h * (E.map (fun e => sumX_polynomial - C e)).prod

/-- The construction of E from S when |S| ≤ m -/
def extend_to_size (S : Finset (ZMod p)) (m : ℕ):
    Multiset (ZMod p) :=
  S.val + Multiset.replicate (m - S.card) (0 : ZMod p)

lemma
extend_to_size_properties (S : Finset (ZMod p)) (m : ℕ) (hS_size : S.card ≤ m) :
    S.val ⊆ extend_to_size S m ∧ (extend_to_size S m).card = m := by
  refine ⟨Multiset.subset_of_le (by simp [extend_to_size]), ?_⟩
  dsimp [extend_to_size]
  simp [hS_size]

/-- Alternative name for clarity -/
noncomputable def product_polynomial (E : Multiset (ZMod p)) : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  (E.map (fun e => sumX_polynomial - C e)).prod

/-- Lemma: construction_polynomial vanishes on ∏ A_i -/
lemma construction_polynomial_vanishes
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (E : Multiset (ZMod p))
    (hE_sub : (restricted_sumset h A).val ⊆ E) :
    ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) →
      eval x (h * (E.map (fun e => sumX_polynomial - C e)).prod) = 0 := by
  intro x hx
  rw [eval_mul]
  by_cases hh : eval x h = 0
  · simp [hh]
  · have h_sum_in_S : (∑ i, x i) ∈ restricted_sumset h A := by
      dsimp [restricted_sumset]
      simp_all only [Finset.mem_image, Finset.mem_filter, Fintype.mem_piFinset]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only [implies_true, not_false_eq_true, and_self]
    have h_sum_in_E : (∑ i, x i) ∈ E := hE_sub h_sum_in_S
    have h_prod_zero : eval x ((E.map (fun e => sumX_polynomial - C e)).prod) = 0 := by
      have factor_zero : eval x (sumX_polynomial - C (∑ i, x i)) = 0 := by
        simp [sumX_polynomial]
      have mem : sumX_polynomial - C (∑ i, x i) ∈
          (show Multiset (MvPolynomial (Fin (k + 1)) (ZMod p)) from
            E.map (fun e => sumX_polynomial - C e)) :=
        Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩
      -- Apply the lemma that states if a multiset contains a zero element, then its product is zero.
      have h_prod_zero : ∀ {m : Multiset (MvPolynomial (Fin (k + 1)) (ZMod p))}, (∃ f ∈ m, MvPolynomial.eval x f = 0) → MvPolynomial.eval x (Multiset.prod m) = 0 := by
        -- If there exists an element in the multiset that evaluates to zero at x, then the product of the multiset also evaluates to zero at x.
        intros m hm
        obtain ⟨f, hf_mem, hf_zero⟩ := hm
        have h_prod_zero : MvPolynomial.eval x (Multiset.prod m) = MvPolynomial.eval x f * MvPolynomial.eval x (Multiset.prod (Multiset.erase m f)) := by
          simp only [← eval_mul, Multiset.prod_erase hf_mem]
        rw [h_prod_zero, hf_zero, MulZeroClass.zero_mul]
      exact h_prod_zero ⟨_, mem, factor_zero⟩
    simp [h_prod_zero]

set_option maxHeartbeats 2000000 in
lemma construction_polynomial_totalDegree
    {p : ℕ} [Fact (Nat.Prime p)]
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (E : Multiset (ZMod p))
    (hm : m + h.totalDegree = ∑ i, c i)
    (hE_card : E.card = m) :
    (construction_polynomial h E).totalDegree = ∑ i, c i := by
  -- delete something
  have h_prod_deg :
      (show MvPolynomial (Fin (k + 1)) (ZMod p) from
        (E.map (fun e => sumX_polynomial - C e)).prod).totalDegree = m := by
    dsimp [sumX_polynomial]
    have degree_of_each : ∀ e : ZMod p,
        (sumX_polynomial - C e : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      intro e
      dsimp [sumX_polynomial]
      have : (∑ i : Fin (k + 1), X i - C e) = (∑ i, X i) + (-C e) := by rw [sub_eq_add_neg]
      rw [MvPolynomial.totalDegree]
      apply le_antisymm
      · refine Finset.sup_le fun d hd => ?_
        simp [this] at hd
        have : (d.sum fun x e ↦ e) ≤ 1 := by
          -- Step 1: Coefficient decomposition of sum X_i - C e
          have coeff_sub_eq :
          coeff d (∑ i, X i - C e) = coeff d (∑ i, X i) + -coeff d (C e) := by
            simp [MvPolynomial.coeff_sub]
            exact sub_eq_add_neg (coeff d (∑ i, X i)) (if 0 = d then e else 0)
          have coeff_C_eq : coeff d (C e) = if d = 0 then e else 0 := by
            simp only [coeff_C]
            aesop
          rw [coeff_C_eq] at coeff_sub_eq
          -- Step 2: d is in the support since its coefficient != 0
          have mem_support : d ∈ (∑ i, X i - C e).support := by
            rw [MvPolynomial.mem_support_iff, coeff_sub_eq]
            aesop
          have support_subset :
          (∑ i, X i - C e).support ⊆
              (Finset.biUnion Finset.univ fun i : Fin (k + 1) => {Finsupp.single i 1})
              ∪ {0} := by
            intro x hx
            rw [MvPolynomial.mem_support_iff] at hx
            have coeff_eq : coeff x (∑ i, X i - C e) = coeff x (∑ i, X i) - coeff x (C e) := by
              simp [MvPolynomial.coeff_sub]
            rw [coeff_eq] at hx
            have coeff_sum_eq :
            coeff x (∑ i, X i) = if ∃ i, x = Finsupp.single i 1 then 1 else 0 := by
              simp [MvPolynomial.coeff_sum]
              have h :
              ∑ x_1, coeff x (X x_1) = if ∃ i, x = Finsupp.single i 1 then 1 else 0 := by
                by_cases h : ∃ i, x = Finsupp.single i 1
                · rcases h with ⟨i, hi⟩
                  have :
                  ∀ j, (if x = Finsupp.single j 1
                  then (1 : ZMod p) else 0) = if i = j then 1 else 0
                  :=
                  by
                    intro j
                    rw [hi]
                    by_cases h : i = j
                    · subst h
                      simp only [↓reduceIte]
                    · simp [h]
                      rw [@Finsupp.single_eq_single_iff]
                      ring_nf
                      simp_all
                  aesop
                · push_neg at h
                  simp [h]
                  have : ∀ i, coeff x (X i) = 0 := by
                    intro i
                    simp [MvPolynomial.coeff_X']
                    exact fun a ↦ h i (id (Eq.symm a))
                  exact fun i => this i
              aesop
            have coeff_C_eq : coeff x (C e) = if x = 0 then e else 0 := by
              simp only [coeff_C]
              aesop
            by_cases h : ∃ i, x = Finsupp.single i 1
            · rcases h with ⟨i, hi⟩
              apply Finset.mem_union_left
              simp [hi]
              use i
            · rw [Finset.mem_union, Finset.mem_singleton]
              right
              have h1 : coeff x (∑ i, X i) = (0 : ZMod p) := by
                have no_single : ¬∃ i, x = Finsupp.single i 1 := h
                rw [MvPolynomial.coeff_sum]
                apply Finset.sum_eq_zero
                intro i
                rw [MvPolynomial.coeff_X']
                split_ifs with h_eq
                · exfalso
                  have h_eq_symm : x = Finsupp.single i 1 := h_eq.symm
                  exact no_single ⟨i, h_eq_symm⟩
                · intro a
                  aesop
              rw [h1] at hx
              rw [coeff_C_eq] at hx
              by_cases h2 : x = 0
              · exact h2
              · simp [h2] at hx
          have :
          d ∈ (Finset.biUnion Finset.univ fun i : Fin (k + 1) => {Finsupp.single i 1}) ∪ {0} :=
            support_subset mem_support
          simp at this
          aesop
        exact this
      simp
      let b : (Fin (k + 1)) →₀ ℕ := Finsupp.single (0 : Fin (k + 1)) 1
      refine ⟨b, ?_, ?_⟩
      · have coeff_eq : coeff (Finsupp.single (0 : Fin (k + 1)) 1) (∑ i, X i) = 1 := by
          simp [coeff_sum, coeff_X', Finsupp.single_eq_single_iff]
        rw [show b = Finsupp.single (0 : Fin (k + 1)) 1 by rfl] at *
        have : b = Finsupp.single (0 : Fin (k + 1)) 1 := rfl
        rw [← this]
        have b_ne_zero : b ≠ 0 := by
          intro H
          aesop
        have : ¬(0 = b) := Ne.symm b_ne_zero
        simp [this]
        change coeff b (∑ i, X i) ≠ 0
        have h1 : (1 : ℕ) ≠ (0 : ZMod p) := by
          simp
        have h : coeff b (∑ i, X i) = (1 : ℕ) := by
          dsimp [b]
          exact coeff_eq
        have : (coeff b (∑ i, X i) : ZMod p) = (1 : ZMod p) := by
          rw [← Nat.cast_one (R := ZMod p)]
          have : (coeff b (∑ i, X i) : ZMod p) = ((coeff b (∑ i, X i) : ℕ) : ZMod p) := by
            simp [coeff_sum, b]
          rw [this, h]
        simp_all
      · simp only [sum_single_index, le_refl, b]
    have h_prod_deg : ((Multiset.map (fun e ↦ ∑ i : Fin (k + 1), X i - C e) E).prod).totalDegree = m := by
      have h1 : ∀ e : ZMod p, (∑ i : Fin (k + 1), X i - C e).totalDegree = 1 := by
        intro e
        aesop
      sorry
    exact h_prod_deg
  have h_h_deg : h.totalDegree = (∑ i, c i) - m := by
    exact Nat.eq_sub_of_add_eq' hm
  sorry

/-- Coefficient of target monomial in the product -/
lemma coeff_prod_sumX_minus_C_target
    (c : Fin (k + 1) → ℕ) (m : ℕ) (E : Multiset (ZMod p)) (hE_card : E.card = m) :
    coeff (Finsupp.equivFunOnFinite.symm c)
      ((E.map (fun e => (∑ i, X i) - C e)).prod) =
    coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m) := by
  sorry

/-- Other terms vanish in the product -/
lemma other_terms_vanish
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (E : Multiset (ZMod p)) (hE_card : E.card = m) :
    ∀ (d : (Fin (k + 1)) →₀ ℕ), d ≠ 0 →
    coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
      ((E.map (fun e => (∑ i, X i) - C e)).prod) = 0 := by
  sorry

/-- Constant term of h is 1 -/
lemma h_constant_term (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (h_coeff : coeff (Finsupp.equivFunOnFinite.symm c)
      ((∑ i, X i) ^ m * h) ≠ 0) :
    coeff 0 h = 1 := by
  sorry

/-- Main coefficient lemma for construction_polynomial -/
lemma construction_polynomial_coeff_target
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : coeff (Finsupp.equivFunOnFinite.symm c)
      ((∑ i, X i) ^ m * h) ≠ 0)
    (E : Multiset (ZMod p)) (hE_card : E.card = m) :
    coeff (Finsupp.equivFunOnFinite.symm c) (construction_polynomial h E) ≠ 0 := by
  dsimp [construction_polynomial]
  rw [coeff_mul]

  have leading_term := coeff_prod_sumX_minus_C_target c m E hE_card
  have other_terms_zero := other_terms_vanish h c m hm E hE_card
  have h_const := h_constant_term h h_coeff
  sorry

set_option maxHeartbeats 2000000 in
/-- **Alon-Nathanson-Ruzsa Theorem** (Theorem 2.1)
Proof strategy: Use Lemma 2.2 (eq_zero_of_eval_zero_at_prod_finset) to prove Theorem 2.1

Proof outline:
1. Assume the conclusion is false, i.e., there exists a set E subset Z_p with |E| = m such that restricted sumset subset E
2. Construct the polynomial Q(x_0,...,x_k) = h(x_0,...,x_k) * prod_{e in E} (x_0+...+x_k - e)
   - deg(Q) = deg(h) + m = sum c_i
   - For all (a_0,...,a_k) in prod A_i, we have Q(a_0,...,a_k) = 0
   - The coefficient of monomial prod x_i^{c_i} in Q is nonzero

3. For each i, define g_i(x_i) = prod_{a in A_i} (x_i - a) = x_i^{c_i+1} - sum_j b_ij x_i^j
4. Construct polynomial Q_bar by replacing all occurrences of x_i^{c_i+1} in Q with sum_j b_ij x_i^j
   - For each a_i in A_i, g_i(a_i) = 0, so Q_bar still vanishes on prod A_i
   - deg_{x_i}(Q_bar) <= c_i

5. Apply Lemma 2.2:
   - Q_bar vanishes on prod A_i
   - Degree in each variable <= c_i
   - Therefore Q_bar = 0

6. But the coefficient of prod x_i^{c_i} in Q_bar is the same as in Q:
   - The replacement process doesn't affect this specific monomial
   - By assumption, this coefficient is nonzero in Q
   - Therefore it's nonzero in Q_bar, contradicting Q_bar = 0

Key points:
- Use polynomial replacement technique to reduce degrees to satisfy Lemma 2.2 conditions
- The replacement process preserves the coefficient of the target monomial
- Proof by contradiction
-/
theorem ANR_polynomial_method {p : ℕ} [Fact (Nat.Prime p)] (k : ℕ)
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p) :=
      (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
    S.card ≥ m + 1 ∧ m < p := by
  -- Define the restricted sumset S
  intro S

  -- Step 1: Prove |S| >= m + 1 by contradiction
  have hS_card : S.card ≥ m + 1 := by
    by_contra! H
    have hS_size : S.card ≤ m := by omega
    set E := extend_to_size S m with hE_def
    have hE_props : S.val ⊆ E ∧ E.card = m := extend_to_size_properties S m hS_size
    obtain ⟨hE_sub, hE_card⟩ := hE_props

    set Q := construction_polynomial h E with hQ_def
    set sumX := sumX_polynomial with hsumX_def

    -- Q vanishes on prod A_i
    have hQ_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q = 0 := fun x a => construction_polynomial_vanishes h A E hE_sub x a
    have hQ_total_deg : Q.totalDegree = ∑ i, c i := by
      rw [hQ_def]
      exact construction_polynomial_totalDegree h c m E hm hE_card
    have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
      rw [hQ_def, coeff_mul]
      -- 1. 证明 ∏_{e∈E}(∑X_i - C e) 的最高次项是 (∑X_i)^m
      have leading_term :
          coeff (Finsupp.equivFunOnFinite.symm c) ((Multiset.map (fun e ↦ ∑ i, X i - C e) E).prod) =
          coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m) := by
        -- 因为乘积的总次数是 m，且目标单项式的次数是 ∑c_i = m + deg(h)
        -- 所以只有最高次项能贡献到这个单项式
        sorry  -- 需要详细证明这个系数相等

      -- 2. 证明当 d ≠ 0 时，coeff d h = 0 或者 coeff (c-d) (∏...) = 0
      have other_terms_zero : ∀ (d : (Fin (k+1)) →₀ ℕ),
          d ≠ 0 → coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
            ((Multiset.map (fun e ↦ ∑ i, X i - C e) E).prod) = 0 := by
        intro d hd
        -- 如果 deg(d) > 0，那么 deg(c-d) < deg(c) = m + deg(h)
        -- 但 ∏_{e∈E}(∑X_i - C e) 的最高次数是 m，所以 coeff (c-d) (...) = 0
        sorry  -- 需要详细证明

      -- 3. 现在求和简化为只有 d = 0 这一项
      rw [Finset.sum_eq_single (0, Finsupp.equivFunOnFinite.symm c)]
      ·
        have h_const : coeff 0 h = 1 := by
          -- 需要证明 h 的常数项为 1
          sorry

        rw [h_const, one_mul, leading_term, ← hsumX_def]
        -- 现在目标：coeff (equivFunOnFinite.symm c) (sumX ^ m) ≠ 0

        -- 从 h_coeff: coeff c (sumX^m * h) ≠ 0 推出 coeff c (sumX^m) ≠ 0
        rw [coeff_mul] at h_coeff
        have key : coeff 0 h * coeff (equivFunOnFinite.symm c) (sumX ^ m) ≠ 0 := by
          contrapose! h_coeff
          apply Finset.sum_eq_zero
          intro x hx
          rcases x with ⟨d1, d2⟩
          have hx_ne : d1 ≠ 0 := by
            intro h
            sorry
          have hx_zero := other_terms_zero d1 hx_ne
          sorry
        rw [h_const, one_mul] at key
        exact key
      · intro x hx hx'
        rcases x with ⟨d1, d2⟩
        have : d1 + d2 = Finsupp.equivFunOnFinite.symm c :=
          (Finset.mem_antidiagonal.mp hx)
        have hzero :
          coeff d1 h *
            coeff (Finsupp.equivFunOnFinite.symm c - d1)
              ((Multiset.map (fun e ↦ ∑ i, X i - C e) E).prod) = 0 :=
        by
          have hd1 : d1 ≠ 0 := by
            intro h
            apply hx'
            simp [h]
            rw [h, zero_add] at this
            exact this
          exact other_terms_zero d1 hd1
        have hd2 :
          d2 = (Finsupp.equivFunOnFinite.symm c - d1) :=
          by
            rw [tsub_eq_of_eq_add_rev (id (Eq.symm this))]
        have hz := hzero
        simpa [hd2, mul_eq_zero] using hz
      · intro h
        simp [Finset.mem_antidiagonal] at h

    -- Define elimination polynomials g_i
    set g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
      elimination_polynomials A with hg_def

    -- Construct Q_bar by reducing degrees
    set Q_bar : MvPolynomial (Fin (k + 1)) (ZMod p) :=
      reduce_polynomial_degrees Q g c with hQ_bar_def

    let target := Finsupp.equivFunOnFinite.symm c
    let P := (E.map (fun e => sumX - C e)).prod
    have hQ_bar_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q_bar = 0 := by sorry

    have hQ_bar_deg : ∀ i, Q_bar.degreeOf i ≤ c i := by
      sorry
    have hQ_bar_zero_poly : Q_bar = 0 :=
      _root_.eq_zero_of_eval_zero_at_prod_finset Q_bar A (fun i => by
        have := hQ_bar_deg i
        grind) hQ_bar_zero

    -- But the coefficient of the target monomial in Q_bar is nonzero
    have hQ_bar_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q_bar ≠ 0 := by
      let target := Finsupp.equivFunOnFinite.symm c
      have h_target_not_replaced : ∀ i, (target i) ≤ c i := by
        intro i
        exact Nat.le_refl (c i)

      have h_coeff_eq : MvPolynomial.coeff target Q_bar = MvPolynomial.coeff target Q := by
        have h_ite : ∀ m ∈ Q.support, m = target →
          (let needs_replacement := Finset.filter (fun i => m i > c i) Finset.univ
          if h : needs_replacement.Nonempty then
            let i := needs_replacement.min' h
            let new_m := Finsupp.update m i (m i - (c i + 1))
            Q.coeff m • MvPolynomial.monomial new_m 1 * (MvPolynomial.X i ^ (c i + 1) - g i)
          else
            Q.coeff m • MvPolynomial.monomial m 1) = Q.coeff m • MvPolynomial.monomial m 1 := by
          intro m hm
          intro a
          subst hE_card a
          simp_all [S, sumX, Q, g, Q_bar, target]

        -- 将 sum 展开，只有 m = target 的贡献才涉及目标单项式
        have sum_eq : MvPolynomial.coeff target Q_bar =
                      Finset.sum Q.support (fun m => if m = target then Q.coeff m else 0) := by
          simp only [Q_bar]
          unfold reduce_polynomial_degrees
          rw [coeff_sum]
          apply Finset.sum_congr rfl
          intros m hm
          let needs_replacement := Finset.filter (fun i => m i > c i) Finset.univ
          by_cases hnr : needs_replacement.Nonempty
          · rw [if_pos]
            rw [MvPolynomial.coeff_mul]
            have target_not_in_branch : ∀ i, target i ≤ c i := h_target_not_replaced
            sorry -- too long
            sorry
          · -- else 分支 monomial = m
            by_cases h_eq : m = target
            · simp [h_eq]
              sorry
            · simp [h_eq, MvPolynomial.coeff_monomial, MulZeroClass.zero_mul]
              sorry


        -- 现在 sum 只剩下 target 自身
        rw [sum_eq]
        simp
        exact fun a ↦ id (Eq.symm a)

      -- Q 中 target 的系数非零，这是假设 h_coeff
      exact h_coeff_eq.symm ▸ hQ_coeff

    -- Contradiction
    rw [hQ_bar_zero_poly] at hQ_bar_coeff
    simp at hQ_bar_coeff

  -- Step 2: Prove m < p first (this is needed for the main argument)
  have hmp : m < p := by
    by_contra! H  -- H: m >= p
    -- If m >= p, use the Frobenius endomorphism property in characteristic p
    have frobenius_identity : ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ p :
    MvPolynomial (Fin (k + 1)) (ZMod p)) = ∑ i, MvPolynomial.X i ^ p := by
      sorry
    sorry
  exact ⟨hS_card, hmp⟩
