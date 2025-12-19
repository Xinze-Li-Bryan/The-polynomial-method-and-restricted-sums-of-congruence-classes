import Mathlib

open MvPolynomial

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-- S = {a₀ + ... + aₖ | aᵢ ∈ Aᵢ, aᵢ ≠ aⱼ for all i ≠ j} -/
def restricted_sum_set (k : ℕ) (A : Fin (k+1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter fun f =>
    ∀ (i j : Fin (k+1)), i < j → f i ≠ f j)
    |>.image (fun f => ∑ i, f i)

/-- Vandermonde: ∏_{i>j} (Xᵢ - Xⱼ) -/
noncomputable def vandermonde_polynomial (k : ℕ) : MvPolynomial (Fin (k+1)) (ZMod p) :=
  ∏ i : Fin (k+1), ∏ j : Fin (k+1),
    if j.val < i.val then (X i - X j) else 1

set_option maxHeartbeats 2000000 in
theorem restricted_sum_distinct_sizes (A : Fin (k+1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sizes_distinct : ∀ i j, i < j → (A i).card ≠ (A j).card)
    (h_sum_bound : ∑ i, (A i).card ≤ p + (Nat.choose (k+2) 2) - 1) :
    (restricted_sum_set k A).card ≥ ∑ i, (A i).card - (Nat.choose (k+2) 2) + 1 := by
  admit

/-- The compressed sizes b'_i defined recursively:
    b'_0 = b_0, b'_i = min{b'_{i-1} - 1, b_i} for i ≥ 1 -/
def compressed_sizes (b : Fin (k+1) → ℕ) : Fin (k+1) → ℕ :=
  λ i =>
    match i with
    | 0 => b 0
    | ⟨i+1, hi⟩ =>
      let prev : Fin (k+1) := ⟨i, by omega⟩
      min (compressed_sizes b prev - 1) (b ⟨i+1, hi⟩)

/--
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
theorem theorem_3_2 (A : Fin (k+1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sizes_noninc : ∀ i j, i ≤ j → (A j).card ≤ (A i).card)
    (h_last_pos : compressed_sizes (λ i => (A i).card) (Fin.last k) > 0) :
    (restricted_sum_set k A).card ≥
    min p (∑ i : Fin (k+1), compressed_sizes (λ i => (A i).card) i - (Nat.choose (k+2) 2) + 1) := by
  sorry
