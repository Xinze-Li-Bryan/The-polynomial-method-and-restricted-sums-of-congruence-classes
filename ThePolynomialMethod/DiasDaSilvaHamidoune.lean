/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7257b62c-6371-4fa8-a5b5-ea19029f0f1f

The following was proved by Aristotle:

- theorem dias_da_silva_hamidoune (A : Finset (ZMod p)) (s : ℕ)
    (h_nonempty : A.Nonempty) (h_s_le_card : s ≤ A.card) :
    (distinct_sum_set A s).card ≥ min p (s * A.card - s ^ 2 + 1)
-/

import Mathlib
import ThePolynomialMethod.RestrictedSumDistinctSizes


open MvPolynomial

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}


/-- The compressed sizes b'_i defined recursively:
    b'_0 = b_0, b'_i = min{b'_{i-1} - 1, b_i} for i ≥ 1 -/
def compressed_sizes (b : Fin (k+1) → ℕ) : Fin (k+1) → ℕ :=
  λ i =>
    match i with
    | 0 => b 0
    | ⟨i+1, hi⟩ =>
      let prev : Fin (k+1) := ⟨i, by omega⟩
      min (compressed_sizes b prev - 1) (b ⟨i+1, hi⟩)

/-
Theorem 3.2:
Let p be a prime, and let A₀, ..., Aₖ be nonempty subsets of Z_p, where |A_i| = b_i,
and suppose b₀ ≥ b₁ ≥ ... ≥ bₖ. Define b′₀, ..., b′ₖ by:
  b′₀ = b₀ and b′_i = min{b′_{i-1} - 1, b_i} for 1 ≤ i ≤ k.
If b′_k > 0 then
  |{a₀ + ... + aₖ : a_i ∈ A_i, a_i ≠ a_j}| ≥ min{p, ∑_{i=0}^k b′_i - (k+2 choose 2) + 1}.
Moreover, this estimate is sharp for all p ≥ b₀ ≥ ... ≥ bₖ.

Proof from the paper (pages 6-7):

If b′_i ≤ 0 for some i then b′_k ≤ 0, thus b′_i > 0 for all i.
For each i, 1 ≤ i ≤ k, let A′_i be an arbitrary subset of cardinality b′_i of A_i.
Note that the cardinalities of the sets A′_i are pairwise distinct and that
⊕_{i=0}^k A′_i ⊂ ⊕_{i=0}^k A_i.

If ∑_{i=0}^k b′_i ≤ p + (k+2 choose 2) - 1 then
  |⊕_{i=0}^k A_i| ≥ |⊕_{i=0}^k A′_i| ≥ ∑_{i=0}^k b′_i - (k+2 choose 2) + 1,
by Proposition 1.2, as needed.

Otherwise, we claim that there are 1 ≤ b″_k < b″_{k-1} < ... < b″_0,
where b″_i ≤ b′_i for all i and ∑_{i=0}^k b″_i = p + (k+2 choose 2) - 1.
To prove this claim, consider the operator T that maps sequences of integers
(d₀, ..., dₖ) with d₀ > d₁ > ... > dₖ ≥ 1 to sequences of the same kind defined as follows.
The sequence (k+1, ..., 1) is mapped to itself.
For any other sequence (d₀, ..., dₖ), let j be the largest index for which
d_j > k+1-j and define T(d₀, ..., dₖ) = (d₀, ..., d_{j-1}, d_j - 1, d_{j+1}, ..., dₖ).
Clearly, the sum of the elements in T(D) is one less than the sum of the elements of D
for every D that differs from (k+1, ..., 1), and thus, by repeatedly applying T to our
sequence (b′₀, ..., b′_k) we get the desired sequence (b″₀, ..., b″_k), proving the claim.

Returning to the proof of the theorem in case ∑_{i=0}^k b′_i > p + (k+2 choose 2) - 1,
let b″_i be as in the claim, and apply Proposition 1.2 to arbitrary subsets A″_i
of cardinality b″_i of A′_i.

It remains to show that the estimate is best possible for all p ≥ b₀ ≥ ... ≥ bₖ ≥ 1.
This is shown by defining A_i = {1, 2, 3, ..., b_i} for all i.
It is easy to check that for these sets A_i, the set ⊕_{i=0}^k A_i is empty if b′_k ≤ 0
and in any case it is contained in the set of consecutive residues
  (k+2 choose 2), (k+2 choose 2) + 1, ..., ∑_{i=0}^k b′_i,
where the numbers b′_i are defined by (2). This completes the proof.
-/
set_option maxHeartbeats 0 in
theorem compressed_sizes_restricted_sum  (A : Fin (k+1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sizes_noninc : ∀ i j, i ≤ j → (A j).card ≤ (A i).card)
    (h_last_pos : compressed_sizes (λ i => (A i).card) (Fin.last k) > 0) :
    (restricted_sum_set k A).card ≥
    min p (∑ i : Fin (k+1), compressed_sizes (λ i => (A i).card) i - (Nat.choose (k+2) 2) + 1) := by admit

/-- The set of all sums of s distinct elements of A -/
def distinct_sum_set (A : Finset (ZMod p)) (s : ℕ) : Finset (ZMod p) :=
  (A.powerset.filter (λ B => B.card = s)).image (λ B => ∑ x ∈ B, x)

/--
Theorem 3.3 (Dias da Silva and Hamidoune):
Let p be a prime and let A be a nonempty subset of Z_p.
Let s∧A denote the set of all sums of s distinct elements of A.
Then |s∧A| ≥ min{p, s|A| - s² + 1}.

Proof from the paper:
If |A| < s there is nothing to prove.
Otherwise put s = k+1 and apply Theorem 3.2 with A_i = A for all i.
Here b′_i = |A| - i for all 0 ≤ i ≤ k and hence
|(k+1)∧A| = |⊕_{i=0}^k A_i| ≥ min{p, ∑_{i=0}^k (|A| - i) - (k+2 choose 2) + 1}
= min{p, (k+1)|A| - (k+1 choose 2) - (k+2 choose 2) + 1}
= min{p, (k+1)|A| - (k+1)² + 1}.

Detailed calculation:
Let k = s - 1, so s = k+1.
For Theorem 3.2 with all A_i = A, we have b_i = |A| for all i.
The compressed sizes are:
  b′₀ = |A|
  b′₁ = min{b′₀ - 1, |A|} = |A| - 1
  b′₂ = min{b′₁ - 1, |A|} = |A| - 2
  ...
  b′_k = min{b′_{k-1} - 1, |A|} = |A| - k = |A| - (s - 1)

Then ∑_{i=0}^k b′_i = ∑_{i=0}^k (|A| - i) = (k+1)|A| - ∑_{i=0}^k i
                    = (k+1)|A| - (k(k+1))/2
                    = (k+1)|A| - (k+1 choose 2)

Now (k+2 choose 2) = (k+1)(k+2)/2 = (k+1 choose 2) + (k+1)

So ∑ b′_i - (k+2 choose 2) + 1 = [(k+1)|A| - (k+1 choose 2)] - [(k+1 choose 2) + (k+1)] + 1
                              = (k+1)|A| - 2*(k+1 choose 2) - (k+1) + 1
                              = (k+1)|A| - [2*(k(k+1))/2] - k
                              = (k+1)|A| - k(k+1) - k
                              = (k+1)|A| - (k+1)k - k
                              = (k+1)|A| - (k+1)² + 1
                              = s|A| - s² + 1

Thus by Theorem 3.2, we get the desired bound.
-/
theorem dias_da_silva_hamidoune (A : Finset (ZMod p)) (s : ℕ)
    (h_nonempty : A.Nonempty) (h_s_le_card : s ≤ A.card) :
    (distinct_sum_set A s).card ≥ min p (s * A.card - s ^ 2 + 1) := by
  by_cases hs : s = 0;
  · aesop;
    exact Or.inr ⟨ 0, Finset.mem_image.mpr ⟨ ∅, by aesop ⟩ ⟩;
  · -- Apply Theorem 3.2 with k = s - 1 and A_i = A for all i.
    have h_theorem : ∀ (A : Finset (ZMod p)) (k : ℕ) (hk : k + 1 ≤ A.card), (restricted_sum_set k (fun _ => A)).card ≥ min p ((k + 1) * A.card - (k + 1) ^ 2 + 1) := by
      intros A k hk
      have h_compressed : ∀ i : Fin (k + 1), compressed_sizes (fun _ => A.card) i = A.card - i.val := by
        intro i
        induction' i using Fin.induction with i ih;
        · unfold compressed_sizes; aesop;
        · unfold compressed_sizes; aesop;
          rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ Nat.sub_sub ];
      -- Apply Theorem 3.2 with the given parameters.
      have h_apply_theorem : (restricted_sum_set k (fun _ => A)).card ≥ min p ((∑ i : Fin (k + 1), (A.card - i.val)) - (Nat.choose (k + 2) 2) + 1) := by
        convert compressed_sizes_restricted_sum ( fun _ => A ) _ _ _ using 1;
        · aesop;
        · exact fun i => Finset.card_pos.mp ( by linarith );
        · aesop;
        · aesop;
      -- Simplify the sum $\sum_{i=0}^{k} (A.card - i)$.
      have h_sum_simplified : ∑ i : Fin (k + 1), (A.card - i.val) = (k + 1) * A.card - (k + 1) * k / 2 := by
        have h_sum_simplified : ∑ i ∈ Finset.range (k + 1), (A.card - i) = (k + 1) * A.card - (k + 1) * k / 2 := by
          have h_sum_simplified : ∑ i ∈ Finset.range (k + 1), (A.card - i) = ∑ i ∈ Finset.range (k + 1), A.card - ∑ i ∈ Finset.range (k + 1), i := by
            exact eq_tsub_of_add_eq <| by rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun i hi => tsub_add_cancel_of_le <| by linarith [ Finset.mem_range.mp hi ] ;
          simp_all +decide [ Finset.sum_range_id ];
        rw [ ← h_sum_simplified, Finset.sum_range ];
      simp_all +decide [ Nat.choose_two_right ];
      grind;
    specialize h_theorem A ( s - 1 ) ; rcases s <;> aesop;
    · -- By definition of $restricted\_sum\_set$, we have $restricted\_sum\_set n (fun _ => A) \subseteq distinct\_sum\_set A (n + 1)$.
      have h_subset : restricted_sum_set n (fun _ => A) ⊆ distinct_sum_set A (n + 1) := by
        intro x hx; unfold restricted_sum_set at hx; unfold distinct_sum_set; aesop;
        use Finset.image w Finset.univ;
        exact ⟨ ⟨ Finset.image_subset_iff.mpr fun i _ => left i, by rw [ Finset.card_image_of_injective _ fun i j hij => le_antisymm ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm ) ( le_of_not_gt fun hj => right_1 _ _ hj hij ), Finset.card_fin ] ⟩, by rw [ Finset.sum_image <| fun i _ j _ hij => le_antisymm ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm ) ( le_of_not_gt fun hj => right_1 _ _ hj hij ) ] ⟩;
      exact Or.inl ( le_trans h ( Finset.card_le_card h_subset ) );
    · refine' Or.inr ( le_trans h_1 _ );
      refine Finset.card_le_card ?_;
      intro x hx;
      unfold restricted_sum_set at hx; unfold distinct_sum_set; aesop;
      exact ⟨ Finset.image w Finset.univ, ⟨ Finset.image_subset_iff.mpr fun i _ => left i, by rw [ Finset.card_image_of_injective _ fun i j hij => le_antisymm ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm ) ( le_of_not_gt fun hj => right_1 _ _ hj hij ), Finset.card_fin ] ⟩, by rw [ Finset.sum_image <| fun i _ j _ hij => le_antisymm ( le_of_not_gt fun hi => right_1 _ _ hi hij.symm ) ( le_of_not_gt fun hj => right_1 _ _ hj hij ) ] ⟩
