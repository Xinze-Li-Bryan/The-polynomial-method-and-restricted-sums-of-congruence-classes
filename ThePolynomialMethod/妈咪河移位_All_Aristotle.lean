/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f69db6e3-806e-415c-ac72-a0457913643d

The following was proved by Aristotle:

- set_option maxHeartbeats 2000000 in
/-- Alon-Nathanson-Ruzsa Polynomial Method (Theorem 2.1)

(Or name it as Thames Shifted Course. As it is really important in the article.)

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
theorem ANR_polynomial_method (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p)
-/

-- One cannot use #min_imports. I don't know why. Something happens in `bound`.
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

open scoped Finset

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

open MvPolynomial

open Finsupp

open MvPolynomial Finsupp

open scoped BigOperators

noncomputable section AristotleLemmas

#check MvPolynomial.eq_zero_of_eval_zero_at_prod_finset

#check MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero

#check MvPolynomial.degreeOf
#check MvPolynomial.eval

lemma coeff_zero_of_m_ge_p {k : ℕ} {p : ℕ} [Fact (Nat.Prime p)]
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (hm : m + h.totalDegree = ∑ i, c i)
    (hc : ∀ i, c i < p)
    (hmp : m ≥ p) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) = 0 := by
      -- In characteristic $p$, we have $(\sum X_i)^p = \sum X_i^p$.
      have h_sum_pow_p : ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m : MvPolynomial (Fin (k + 1)) (ZMod p)) = (∑ j : Fin (k + 1), (MvPolynomial.X j) ^ p) * ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ (m - p) : MvPolynomial (Fin (k + 1)) (ZMod p)) := by
        rw [ ← Nat.add_sub_of_le hmp, pow_add ];
        simp +decide [ add_tsub_cancel_left];
        exact Or.inl ( by exact sum_pow_char p Finset.univ X );
      rw [ h_sum_pow_p, mul_assoc ];
      rw [ MvPolynomial.coeff_mul ];
      rw [ Finset.sum_eq_zero ] ; intros ; 
      rename_i x a
      simp_all only [ge_iff_le, Finset.mem_antidiagonal, mul_eq_zero]
      obtain ⟨fst, snd⟩ := x
      simp_all only
      by_cases h : ∃ j, fst j = p <;> simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_X_pow ];
      · obtain ⟨ j, hj ⟩ := h; replace a := congr_arg ( fun f => f j ) a; 
        subst hj
        simp_all only [Finsupp.coe_add, Pi.add_apply, equivFunOnFinite_symm_apply_apply]
        linarith [ hc j ];
      · rw [ Finset.card_eq_zero.mpr ] <;> aesop;
        exact h x ( Finsupp.single_eq_same )

#check MvPolynomial.totalDegree_add
#check MvPolynomial.totalDegree_C
#check MvPolynomial.totalDegree_X
#check MvPolynomial.totalDegree_zero
#check MvPolynomial.totalDegree_neg

lemma totalDegree_sum_X_le_one {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] :
    MvPolynomial.totalDegree (∑ i : σ, MvPolynomial.X i : MvPolynomial σ R) ≤ 1 := by
      -- The total degree of the sum of the variables is at most 1 because each term in the sum is of the form X_i, which has a total degree of 1.
      simp [MvPolynomial.totalDegree];
      -- If the coefficient of $b$ in the sum of $X_i$ is non-zero, then $b$ must be one of the $X_i$'s.
      intro b hb
      have hb_X : ∃ i, b = Finsupp.single i 1 := by
        contrapose! hb; simp_all +decide [ MvPolynomial.coeff_sum ] ;
        rw [ Finset.sum_eq_zero ] ; intros ; erw [ MvPolynomial.coeff_X' ] ; aesop;
        simpa using hb x;
      -- Since $b$ is equal to $Finsupp.single i 1$ for some $i$, the sum of its exponents is $1$.
      obtain ⟨i, hi⟩ := hb_X;
      simp [hi, Finsupp.sum_single_index]

lemma totalDegree_sum_X_sub_C_le_one {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (e : R) :
    MvPolynomial.totalDegree (∑ i : σ, MvPolynomial.X i - MvPolynomial.C e : MvPolynomial σ R) ≤ 1 := by
      refine' le_trans ( MvPolynomial.totalDegree_sub _ _ ) ( max_le _ _ );
      · exact totalDegree_sum_X_le_one;
      · simp +decide [ MvPolynomial.totalDegree ]

lemma totalDegree_prod_linear_le {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (E : Finset R) :
    MvPolynomial.totalDegree (∏ e ∈ E, (∑ i : σ, MvPolynomial.X i - MvPolynomial.C e : MvPolynomial σ R)) ≤ E.card := by
      -- Applying the fact that the total degree of a product of polynomials is at most the sum of their total degrees.
      have h_deg_prod : MvPolynomial.totalDegree (∏ e ∈ E, (∑ i, MvPolynomial.X i - MvPolynomial.C e) : MvPolynomial σ R) ≤ ∑ e ∈ E, MvPolynomial.totalDegree (∑ i, MvPolynomial.X i - MvPolynomial.C e : MvPolynomial σ R) := by
        exact totalDegree_finset_prod E fun e => ∑ i, X i - C e;
      refine' h_deg_prod.trans ( le_trans ( Finset.sum_le_sum fun e _ => totalDegree_sum_X_sub_C_le_one e ) _ ) ; simp +decide

lemma coeff_prod_linear_eq_coeff_pow {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (E : Finset R)
    (d : σ →₀ ℕ) (hd : d.sum (fun _ n => n) = E.card) :
    MvPolynomial.coeff d (∏ e ∈ E, (∑ i : σ, MvPolynomial.X i - MvPolynomial.C e)) =
    MvPolynomial.coeff d ((∑ i : σ, MvPolynomial.X i) ^ E.card) := by
      revert d hd;
      induction' E using Finset.induction with a E haE ih;
      exact fun d hd => (congrArg (coeff d) ∘ fun a => a) rfl;
      swap;
      apply_rules [ Classical.decEq ];
      intro d hd
      have h_coeff : MvPolynomial.coeff d ((∑ i : σ, MvPolynomial.X i - MvPolynomial.C a) * (∏ e ∈ E, (∑ i : σ, MvPolynomial.X i - MvPolynomial.C e))) = MvPolynomial.coeff d ((∑ i : σ, MvPolynomial.X i) * (∏ e ∈ E, (∑ i : σ, MvPolynomial.X i - MvPolynomial.C e))) := by
        simp +decide [ sub_mul ];
        rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ] ; aesop;
        refine' lt_of_le_of_lt ( totalDegree_prod_linear_le _ ) _;
        simp_all +decide [ Finsupp.sum ];
      have h_coeff : MvPolynomial.coeff d ((∑ i : σ, MvPolynomial.X i) * (∏ e ∈ E, (∑ i : σ, MvPolynomial.X i - MvPolynomial.C e))) = MvPolynomial.coeff d ((∑ i : σ, MvPolynomial.X i) * ((∑ i : σ, MvPolynomial.X i) ^ #E)) := by
        rw [ MvPolynomial.coeff_mul, MvPolynomial.coeff_mul ];
        refine' Finset.sum_congr rfl fun x hx => _;
        by_cases hx1 : x.1.sum ( fun _ n => n ) = 1 <;> simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_X' ];
        · rw [ ← hx, add_comm ] at hd;
          rw [ Finsupp.sum_add_index' ] at hd <;> aesop;
        · rw [ Finset.card_eq_zero.mpr ] <;> aesop;
      simp_all +decide [ pow_succ' ]

lemma coeff_mul_eq_of_high_degree_coeffs_eq {σ R : Type*} [CommRing R] [Fintype σ]
    (f g1 g2 : MvPolynomial σ R) (c : σ →₀ ℕ) (m : ℕ)
    (hf : f.totalDegree + m = c.sum (fun _ n => n))
    (hg1 : g1.totalDegree ≤ m)
    (hg2 : g2.totalDegree ≤ m)
    (h_coeffs : ∀ d, d.sum (fun _ n => n) = m → MvPolynomial.coeff d g1 = MvPolynomial.coeff d g2) :
    MvPolynomial.coeff c (f * g1) = MvPolynomial.coeff c (f * g2) := by
      -- If $m = 0$, then $g_1$ and $g_2$ are constants, and the result follows.
      by_cases hm : m = 0;
      · -- Since $m = 0$, we have $g_1 = g_2$.
        have hg_eq : g1 = g2 := by
          ext d;
          by_cases hd : d = 0 <;> simp_all +decide [ MvPolynomial.totalDegree ];
          grind;
        rw [ hg_eq ];
      · -- Since $m > 0$, we have $\text{totalDegree } (g1 - g2) < m$.
        have h_deg_diff : (g1 - g2).totalDegree < m := by
          refine' lt_of_le_of_ne _ _;
          · exact le_trans ( MvPolynomial.totalDegree_sub _ _ ) ( max_le hg1 hg2 );
          · contrapose! h_coeffs;
            obtain ⟨ d, hd ⟩ := Finset.exists_max_image _ ( fun x => Finsupp.sum x fun x n => n ) ( Finset.nonempty_of_ne_empty ( by aesop_cat : ( MvPolynomial.support ( g1 - g2 ) ) ≠ ∅ ) ) ; use d; aesop;
            refine' le_antisymm _ _;
            · exact Finset.le_sup ( f := fun x => Finsupp.sum x fun x n => n ) ( Finsupp.mem_support_iff.mpr left );
            · exact Finset.sup_le fun x hx => right x <| by aesop;
        -- Since $\text{totalDegree } (f * (g1 - g2)) \le \text{totalDegree } f + \text{totalDegree } (g1 - g2) < \text{degree } c$, we have $\text{coeff } c (f * (g1 - g2)) = 0$.
        have h_coeff_zero : MvPolynomial.coeff c (f * (g1 - g2)) = 0 := by
          rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ];
          refine' lt_of_le_of_lt ( MvPolynomial.totalDegree_mul _ _ ) _;
          linarith!;
        simp_all +decide [ mul_sub ];
        exact eq_of_sub_eq_zero h_coeff_zero

end AristotleLemmas

/-- Alon-Nathanson-Ruzsa Polynomial Method (Theorem 2.1)

(Or name it as Thames Shifted Course. As it is really important in the article.)

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
theorem ANR_polynomial_method (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p) :=
      (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
    S.card ≥ m + 1 ∧ m < p := by
      -- If $m \geq p$, then $h$ would have to be distinct from the zero polynomial modulo $p$, contradicting $h_coeff$.
      by_cases h_ge_p : m ≥ p;
      · apply_mod_cast False.elim <| h_coeff <| coeff_zero_of_m_ge_p h c m hm _ h_ge_p;
        intro i; specialize hA i; have := Finset.card_le_univ ( A i ) ; simp_all +decide ;
        linarith;
      · intro S
        apply And.intro
        · -- Let $E$ be a subset of $\mathbb{Z}_p$ containing $S$ with $|E| = m$.
          by_contra h_contra
          obtain ⟨E, hE₁, hE₂⟩ : ∃ E : Finset (ZMod p), S ⊆ E ∧ E.card = m := by
            have h_card_S : S.card ≤ m := by
              linarith;
            have h_card_S : ∃ T : Finset (ZMod p), T.card = m - S.card ∧ Disjoint S T := by
              have h_card_S : (Finset.univ \ S).card ≥ m - S.card := by
                simp +decide [ Finset.card_sdiff, * ];
                omega
              obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq h_card_S;
              exact ⟨ T, hT.2, Finset.disjoint_left.mpr fun x hxS hxT => Finset.mem_sdiff.mp ( hT.1 hxT ) |>.2 hxS ⟩;
            obtain ⟨ T, hT₁, hT₂ ⟩ := h_card_S; use S ∪ T; aesop;
          -- Consider the polynomial $Q = h * \prod_{e \in E} (\sum X_i - e)$.
          set Q := h * ∏ e ∈ E, (∑ i, MvPolynomial.X i - MvPolynomial.C e) with hQ_def
          have hQ_vanishes : ∀ f ∈ Fintype.piFinset A, Q.eval f = 0 := by
            intro f hf; by_cases hf' : ( MvPolynomial.eval f ) h = 0 <;> simp_all +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ] ;
            exact hE₁ <| Finset.mem_image.mpr ⟨ f, Finset.mem_filter.mpr ⟨ Fintype.mem_piFinset.mpr hf, hf' ⟩, rfl ⟩
          have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
            -- By `coeff_mul_eq_of_high_degree_coeffs_eq`, we have `coeff c Q = coeff c (h * (\sum X_i)^m)`.
            have hQ_coeff_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (∑ i, MvPolynomial.X i) ^ m) := by
              have hQ_coeff_eq : ∀ d : (Fin (k + 1) →₀ ℕ), d.sum (fun _ n => n) = m → MvPolynomial.coeff d (∏ e ∈ E, (∑ i, MvPolynomial.X i - MvPolynomial.C e)) = MvPolynomial.coeff d ((∑ i, MvPolynomial.X i) ^ m) := by
                intros d hd_sum;
                convert coeff_prod_linear_eq_coeff_pow E d _;
                · linarith;
                · linarith;
              apply coeff_mul_eq_of_high_degree_coeffs_eq h (∏ e ∈ E, (∑ i, MvPolynomial.X i - MvPolynomial.C e)) ((∑ i, MvPolynomial.X i) ^ m) (Finsupp.equivFunOnFinite.symm c) m (by
              simp_all +decide [ add_comm, Finsupp.sum_fintype ]) (by
              convert totalDegree_prod_linear_le E using 1 ; aesop;
              infer_instance) (by
              -- The total degree of $(\sum_{i=0}^k X_i)^m$ is $m$.
              have h_total_degree : ∀ m : ℕ, MvPolynomial.totalDegree ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m : MvPolynomial (Fin (k + 1)) (ZMod p)) ≤ m := by
                intro m; induction' m with m ih <;> simp_all +decide [ pow_succ, MvPolynomial.totalDegree_mul ] ;
                exact le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( add_le_add ih ( totalDegree_sum_X_le_one ) );
              exact h_total_degree m) (by
              assumption);
            simp_all +decide [ mul_comm ];
          -- By the Combinatorial Nullstellensatz, there exists $x \in \prod A_i$ such that $Q(x) \neq 0$.
          obtain ⟨x, hx⟩ : ∃ x : Fin (k + 1) → ZMod p, (∀ i, x i ∈ A i) ∧ Q.eval x ≠ 0 := by
            have hQ_totalDegree : Q.totalDegree ≤ ∑ i, c i := by
              refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _;
              refine' le_trans (add_le_add_right (totalDegree_prod_linear_le E) (h.totalDegree)) _ -- Fix here `add_le_add_right`. The origin is `add_le_add_left`.
              aesop;
              linarith;
            have hQ_totalDegree_eq : Q.totalDegree = ∑ i, c i := by
              refine' le_antisymm hQ_totalDegree _;
              refine' le_trans _ ( Finset.le_sup <| MvPolynomial.mem_support_iff.mpr hQ_coeff );
              simp +decide [ Finsupp.sum_fintype ];
            apply MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero;
            exact Ne.symm (Ne.intro (id (Ne.symm hQ_coeff)));
            · simp_all +decide [ Finsupp.degree ];
              rw [ Finset.sum_filter_of_ne ] ; aesop;
            · aesop;
          exact hx.2 ( hQ_vanishes x ( by simpa [ Fintype.mem_piFinset ] using hx.1 ) );
        · exact lt_of_not_ge h_ge_p
