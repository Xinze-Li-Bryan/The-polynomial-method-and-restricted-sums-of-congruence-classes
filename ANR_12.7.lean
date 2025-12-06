import Mathlib

open scoped Finset

variable {R : Type*} [CommRing R]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

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

/- (Unused) -/
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

/-- Alternative name for clarity. Here use k explicitly. -/
noncomputable def product_polynomial (k : ℕ) (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
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

/-- The product polynomial ∏_{e∈E} (∑X_i - C e) is always nonzero -/
lemma product_polynomial_ne_zero (k : ℕ) (E : Multiset (ZMod p)) :
    product_polynomial k E ≠ 0 := by
      by_contra h
      by_cases hE : E.card = 0 <;> simp_all +decide [product_polynomial]
      obtain ⟨a, haE, ha⟩ := h
      replace ha := congr_arg (MvPolynomial.eval (fun i => if i = 0 then a + 1 else 0)) ha
      norm_num [sumX_polynomial] at ha

/-
Induction steps from J.J. Zhang
-/
lemma totalDegree_sumX_sub_C_first {p k : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) :
    (sumX_polynomial - C a : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      refine' le_antisymm _ _;
      · refine' le_trans ( MvPolynomial.totalDegree_sub _ _ ) _;
        -- The total degree of a sum of polynomials is less than or equal to the maximum of the total degrees of the summands.
        have h_total_degree_sum : ∀ (s : Finset (Fin (k + 1))), (∑ i ∈ s, MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree ≤ 1 := by
          -- The total degree of a sum of polynomials is less than or equal to the maximum of their total degrees.
          have h_sum_deg : ∀ (s : Finset (Fin (k + 1))), (∑ i ∈ s, MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree ≤ Finset.sup s (fun i => (MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree) := by
            exact fun s => totalDegree_finset_sum s fun i => X i;
          aesop;
          exact le_trans ( h_sum_deg s ) ( Finset.sup_le fun i hi => le_rfl );
        aesop;
      · refine' le_trans _ ( Finset.le_sup <| show Finsupp.single 0 1 ∈ ( ∑ i : Fin ( k + 1 ), MvPolynomial.X i - MvPolynomial.C a |> MvPolynomial.support ) from _ ) <;> norm_num;
        rw [ MvPolynomial.coeff_sum ] ; aesop;
        simpa using congr_arg ( fun f => f 0 ) h.symm

/-
Induction steps from J.J. Zhang
-/
lemma totalDegree_sumX_sub_C_second (e : ZMod p) :
    totalDegree (∑ i : Fin (k + 1), X i - C e) = 1 := by
  have : (∑ i : Fin (k + 1), X i - C e) = (sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) - C e := by
    simp [sumX_polynomial]
  rw [this]
  exact totalDegree_sumX_sub_C_first e

/-
Induction steps from J.J. Zhang
-/
lemma totalDegree_prod_sumX_sub_C_eq_card (E : Multiset (ZMod p)) :
    ((Multiset.map (fun e ↦ ∑ i : Fin (k + 1), X i - C e) E).prod).totalDegree = E.card := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons x E ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [totalDegree_mul_of_isDomain]
    · have foo : ∀ e : ZMod p, (∑ i : Fin (k + 1), X i - C e).totalDegree = 1 := fun e => totalDegree_sumX_sub_C_second e
      rw [ih, foo, add_comm]
    · simp only [ne_eq, sub_eq_zero]
      intro rid
      have := congr($(rid).coeff (fun₀ | 0 => 1))
      simp only [coeff_sum, coeff_single_X, true_and, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, coeff_C] at this
      rw [if_neg] at this
      · norm_num at this
      · rw [eq_comm, Finsupp.single_eq_zero]
        norm_num
    · intro rid
      rw [Multiset.prod_eq_zero_iff] at rid
      simp only [Multiset.mem_map] at rid
      obtain ⟨a, a_mem, rid⟩ := rid
      have := congr($(rid).coeff (fun₀ | 0 => 1))
      simp only [coeff_sub, coeff_sum, coeff_single_X, true_and, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, coeff_C, coeff_zero] at this
      rw [if_neg] at this
      · norm_num at this
      · rw [eq_comm, Finsupp.single_eq_zero]
        norm_num

set_option maxHeartbeats 2000000 in
/- I may say that this part can be shortened by the induction from J.J. Zhang-/
lemma construction_polynomial_totalDegree
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (h_ne_zero : h ≠ 0)
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (E : Multiset (ZMod p))
    (hm : m + h.totalDegree = ∑ i, c i)
    (hE_card : E.card = m)
    (h_prod_ne_zero : product_polynomial k E ≠ 0) :
    (construction_polynomial h E).totalDegree = ∑ i, c i := by
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
      -- Apply the lemma that the total degree of a product is the sum of the total degrees.
      have h_total_degree : ∀ (s : Multiset (MvPolynomial (Fin (k + 1)) (ZMod p))), (∀ p ∈ s, p.totalDegree = 1) → s.prod.totalDegree = s.card := by
        bound
        induction s using Multiset.induction <;> aesop
        -- Apply the lemma that the total degree of a product is the sum of the total degrees, given that both factors are non-zero.
        have h_total_degree_mul : ∀ (f g : MvPolynomial (Fin (k + 1)) (ZMod p)), f ≠ 0 → g ≠ 0 → (f * g).totalDegree = f.totalDegree + g.totalDegree := by
          exact fun f g a a_3 => totalDegree_mul_of_isDomain a a_3
        by_cases h : a_1 = 0 <;> by_cases h' : s.prod = 0 <;> simp_all +decide [add_comm]
        rw [eq_comm] at a_2
        aesop
      rw [h_total_degree] <;> aesop
    exact h_prod_deg
  have h_h_deg : h.totalDegree = (∑ i, c i) - m := by
    exact Nat.eq_sub_of_add_eq' hm
  -- By definition of construction_polynomial, we have construction_polynomial h E = h * product_polynomial k E.
  have h_construction_eq : construction_polynomial h E = h * product_polynomial k E := by
    exact rfl
  -- Apply the property that the total degree of a product of two polynomials is the sum of their total degrees.
  have h_total_deg : (h * product_polynomial k E).totalDegree = h.totalDegree + (product_polynomial k E).totalDegree := by
    exact totalDegree_mul_of_isDomain h_ne_zero h_prod_ne_zero
  subst h_prod_deg
  simp_all only [ne_eq]
  -- Apply the hypothesis `hm` directly to conclude the proof.
  convert hm using 1
  exact
    Nat.add_comm (∑ i, c i - (Multiset.map (fun e => sumX_polynomial - C e) E).prod.totalDegree)
      (product_polynomial k E).totalDegree

/-- If (∑X_i)^m * h has nonzero coefficient at x^c, then h has nonzero constant term -/
lemma h_constant_term_nonzero (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ)  -- 需要c和m作为参数
    (hm : m + h.totalDegree = ∑ i, c i)  -- 需要次数关系
    (h_coeff : coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m * h) ≠ 0) :
    coeff 0 h ≠ 0 := by
  sorry

/-- Other terms vanish in the product -/
lemma other_terms_vanish
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (E : Multiset (ZMod p)) (hE_card : E.card = m)
    (h_prod_total_deg : ((E.map (fun e : ZMod p => (∑ i : Fin (k + 1), X i) - C e)).prod).totalDegree = m) :
    -- 添加：乘积的总次数为m (Really right?)
    ∀ (d : (Fin (k + 1)) →₀ ℕ), d ≠ 0 →
    coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
      ((E.map (fun e => (∑ i, X i) - C e)).prod) = 0 := by
  sorry

/-
The coefficient of a term of maximal degree in the product $\prod (S - e)$ is the same as in $S^{|E|}$.
-/
open MvPolynomial Finsupp
open scoped BigOperators

lemma coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq
    {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}
    (E : Multiset (ZMod p)) (x : (Fin (k+1)) →₀ ℕ) (hx : ∑ i, x i = Multiset.card E) :
    MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod) =
    MvPolynomial.coeff x ((∑ i : Fin (k+1), MvPolynomial.X i) ^ Multiset.card E) := by
  revert x;
  induction' E using Multiset.induction with a E ih <;> aesop;
  rw [ pow_succ' ];
  simp +decide [ sub_mul, mul_assoc, MvPolynomial.coeff_mul ];
  rw [ ← Finset.sum_sub_distrib, Finset.sum_congr rfl ] ; aesop;
  · rw [ MvPolynomial.coeff_sum ] ; aesop;
    refine' Or.inr ( _ );
    rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ];
    refine' lt_of_le_of_lt ( MvPolynomial.totalDegree_multiset_prod _ ) _;
    refine' lt_of_le_of_lt ( Multiset.sum_le_card_nsmul _ _ _ ) _;
    exact 1;
    · aesop;
      norm_num [ MvPolynomial.totalDegree ];
      intro b hb; contrapose! hb; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_X' ] ;
      rw [ Finset.card_eq_zero.mpr ] <;> aesop;
    · rw [ Finset.sum_subset ( Finset.subset_univ snd.support ) ] <;> aesop;
  · simp_all +decide [ Finset.sum_add_distrib ];
    by_cases h_snd : ∑ i, snd i = E.card;
    · exact Or.inl <| ih snd h_snd;
    · right;
      rw [ MvPolynomial.coeff_sum, Finset.sum_eq_zero ] ; aesop;
      -- Since $fst \neq Finsupp.single x 1$, the coefficient of $fst$ in $X x$ is zero.
      have h_coeff_zero : fst ≠ Finsupp.single x 1 := by
        intro H; simp_all +decide [ Finsupp.single_apply ] ;
        exact h_snd ( by linarith );
      rw [ MvPolynomial.coeff_X' ] ; aesop

set_option maxHeartbeats 2000000 in
/- The condition of the three h seems hard to use-/
lemma construction_polynomial_coeff_target_generalized
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m * h) ≠ 0)
    (E : Multiset (ZMod p)) (hE_card : E.card = m)
    (coeff_prod_sumX_minus_C_target :
      coeff (Finsupp.equivFunOnFinite.symm c) ((E.map (fun e => (∑ i, X i) - C e)).prod) =
      coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m))
    (other_terms_vanish : ∀ (d : (Fin (k + 1)) →₀ ℕ), d ≠ 0 →
      coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
        ((E.map (fun e => (∑ i, X i) - C e)).prod) = 0)
    (h_constant_term_nonzero : coeff 0 h ≠ 0) :
    coeff (Finsupp.equivFunOnFinite.symm c) (construction_polynomial h E) ≠ 0 := by
      -- By combining the results from `coeff_prod_sumX_minus_C_target` and `other_terms_vanish`, we can conclude that the coefficient of $c$ in the product is equal to the coefficient of $c$ in $S^m$ times the constant term of $h$.
      have h_final : MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin (k + 1) → ℕ) → Fin (k + 1) →₀ ℕ) c) (construction_polynomial h E) = MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin (k + 1) → ℕ) → Fin (k + 1) →₀ ℕ) c) (Multiset.prod (Multiset.map (fun e => (∑ i, MvPolynomial.X i) - MvPolynomial.C e) E)) * MvPolynomial.coeff 0 h := by
        rw [ construction_polynomial, MvPolynomial.coeff_mul ];
        rw [ Finset.sum_eq_single ( 0, ( Finsupp.equivFunOnFinite.symm c ) ) ] <;> aesop;
        · rw [ mul_comm, ← coeff_prod_sumX_minus_C_target ];
          rfl;
        · by_cases h : fst = 0 <;> specialize other_terms_vanish fst <;> aesop;
          rw [ ← a, add_tsub_cancel_left ] at h_3 ; aesop;
      contrapose! h_coeff; simp_all +decide [ mul_comm ] ;
      rw [ MvPolynomial.coeff_mul ];
      rw [ Finset.sum_eq_single ( 0, ( Finsupp.equivFunOnFinite.symm c ) ) ] <;> aesop;
      by_cases h_fst : fst = 0 <;> specialize other_terms_vanish fst <;> aesop;
      contrapose! h_2;
      convert h_2.2 using 1;
      rw [ ← a, add_tsub_cancel_left ];
      convert coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq E snd _ using 1;
      replace a := congr_arg ( fun x => ∑ i, x i ) a ; aesop;
      simp_all +decide [ Finset.sum_add_distrib ];
      have h_deg_snd : ∑ i, snd i ≤ E.card := by
        contrapose! right;
        rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ];
        refine' lt_of_le_of_lt _ ( lt_of_lt_of_le right _ );
        · induction' E.card with n ih <;> simp_all +decide [ pow_succ];
          refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) ( add_le_add ih _ );
          norm_num [ MvPolynomial.totalDegree ];
          -- Since the sum of X_i's is just the polynomial where each term is X_i, any non-zero coefficient of this polynomial must be one of the X_i's.
          intro b hb_nonzero
          have hb_X : ∃ i, b = Finsupp.single i 1 := by
            simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_X' ];
            obtain ⟨ i, hi ⟩ := Finset.nonempty_of_ne_empty ( by aesop_cat : ( Finset.filter ( fun x => ( Finsupp.single x 1 ) = b ) Finset.univ ) ≠ ∅ ) ; use i; aesop;
          aesop;
        · rw [ Finset.sum_subset ( show snd.support ⊆ Finset.univ from Finset.subset_univ _ ) ] ; aesop;
      linarith [ show h.totalDegree ≥ ∑ i, fst i from Finset.le_sup ( f := fun s => s.sum fun x e => e ) ( Finsupp.mem_support_iff.mpr left ) |> le_trans ( by simp +decide [ Finsupp.sum_fintype ] ) ]

/-
(Not used)
sumX_polynomial is homogeneous of degree 1.
-/
lemma sumX_is_homogeneous_one {p k : ℕ} [Fact (Nat.Prime p)] :
    IsHomogeneous (sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) 1 := by
      -- Each X_i is a monomial of degree 1, so their sum is also homogeneous of degree 1.
      have h_homogeneous : ∀ i : Fin (k + 1), (MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).IsHomogeneous 1 := by
        exact fun i => isHomogeneous_X (ZMod p) i;
      -- Apply the lemma that the sum of homogeneous polynomials is homogeneous.
      have h_sum_homogeneous : ∀ (s : Finset (Fin (k + 1))), (∀ i ∈ s, (MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).IsHomogeneous 1) → (Finset.sum s (fun i => MvPolynomial.X i) : MvPolynomial (Fin (k + 1)) (ZMod p)).IsHomogeneous 1 := by
        exact fun s a => IsHomogeneous.sum s X 1 a;
      exact h_sum_homogeneous _ fun i _ => h_homogeneous i

/-
(Not used)
Properties of sumX - C a regarding its degree and coefficients in X_0.
-/
lemma sumX_sub_C_properties {p k : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) :
    let Q := (sumX_polynomial - C a : MvPolynomial (Fin (k + 1)) (ZMod p))
    Q.degreeOf 0 = 1 ∧
    Q.coeff (Finsupp.single 0 1) = 1 ∧
    (∀ m ∈ Q.support, m 0 ≤ 1) ∧
    (∀ m ∈ Q.support, m 0 = 1 → m = Finsupp.single 0 1) := by
      unfold sumX_polynomial;
      norm_num [ MvPolynomial.degreeOf_eq_sup, MvPolynomial.coeff_sum ];
      refine' ⟨ _, _, _, _ ⟩;
      · refine' le_antisymm _ _;
        · simp +zetaDelta at *;
          intro b hb; contrapose! hb; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_X' ] ;
          rw [ Finset.card_eq_zero.mpr ] <;> aesop;
          rw [ Finsupp.single_apply ] at hb ; aesop;
        · refine' le_trans _ ( Finset.le_sup <| show Finsupp.single 0 1 ∈ _ from _ ) <;> norm_num;
          rw [ MvPolynomial.coeff_sum ] ; aesop;
          simpa using congr_arg ( fun f => f 0 ) h.symm;
      · exact fun h => absurd h ( ne_of_apply_ne ( fun f => f 0 ) ( by norm_num ) );
      · intro m hm; contrapose! hm; simp_all +decide [ MvPolynomial.coeff_X' ] ;
        rw [ Finset.card_eq_zero.mpr ] <;> aesop;
        rw [ Finsupp.single_apply ] at hm ; aesop;
      · intro m hm₁ hm₂; rw [ Finset.sum_eq_single 0 ] at hm₁ <;> aesop;
        · rw [ MvPolynomial.coeff_X' ] at hm₁ ; aesop;
        · rw [ MvPolynomial.coeff_X' ] ; aesop

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
  -- Define the restricted sumset S
  intro S
  have h_ne_zero : h ≠ 0 := by
    intro h_zero
    rw [h_zero, mul_zero, coeff_zero] at h_coeff
    exact h_coeff rfl

  -- Step 1: Prove |S| >= m + 1 by contradiction
  have hS_card : S.card ≥ m + 1 := by
    by_contra! H
    have hS_size : S.card ≤ m := by omega
    set E := extend_to_size S m with hE_def
    have extend_to_size_properties :
    S.val ⊆ extend_to_size S m ∧ (extend_to_size S m).card = m := by
      refine ⟨Multiset.subset_of_le (by simp [extend_to_size]), ?_⟩
      dsimp [extend_to_size]
      simp [hS_size]
    have hE_props : S.val ⊆ E ∧ E.card = m := by exact extend_to_size_properties
    obtain ⟨hE_sub, hE_card⟩ := hE_props

    set Q := construction_polynomial h E with hQ_def

    -- Q vanishes on prod A_i
    have hQ_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q = 0 := fun x a => construction_polynomial_vanishes h A E hE_sub x a
    have h_prod_ne_zero : product_polynomial k E ≠ 0 := by exact product_polynomial_ne_zero k E
    have hQ_total_deg : Q.totalDegree = ∑ i, c i := by
      exact construction_polynomial_totalDegree h h_ne_zero c m E hm hE_card h_prod_ne_zero
    have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
      rw [hQ_def]
      apply construction_polynomial_coeff_target_generalized h c m hm h_coeff E hE_card
      · sorry
      · -- 需要提供 h_prod_total_deg: 乘积的总次数 = m
        have h_prod_total_deg : ((E.map (fun e : ZMod p => (∑ i : Fin (k + 1), X i) - C e)).prod).totalDegree = m := by sorry
        exact other_terms_vanish h c m hm E hE_card h_prod_total_deg
      · exact h_constant_term_nonzero h c m hm h_coeff  -- 现在需要传递c和m
    -- Define elimination polynomials g_i
    set g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
      elimination_polynomials A with hg_def

    -- Construct Q_bar by reducing degrees
    set Q_bar : MvPolynomial (Fin (k + 1)) (ZMod p) :=
      reduce_polynomial_degrees Q g c with hQ_bar_def

    let target := Finsupp.equivFunOnFinite.symm c
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
          aesop

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
