import Mathlib

open MvPolynomial
open Finset
open Matrix
open BigOperators

variable {R : Type*} [CommRing R]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-- Expected value: m! / (∏ cᵢ!) * ∏_{i>j} (cᵢ - cⱼ) -/
def expected_value (c : Fin (k+1) → ℕ) (m : ℕ) : ℚ :=
  (m.factorial : ℚ) * (∏ i : Fin (k+1), ∏ j : Fin (k+1),
    if j.val < i.val then ((c i : ℚ) - (c j : ℚ)) else 1) /
    (∏ i : Fin (k+1), ((c i).factorial : ℚ))

/-- Convert a function c : Fin (k+1) → ℕ to Finsupp -/
def toFinsupp (c : Fin (k+1) → ℕ) : (Fin (k+1)) →₀ ℕ :=
  ⟨Finset.univ.filter (λ i => c i ≠ 0), c, λ i => by simp⟩

theorem ANR_polynomial_method (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p) :=
      (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
    S.card ≥ m + 1 ∧ m < p := by admit

theorem Vandermonde_coefficient_formula (c : Fin (k+1) → ℕ) (m : ℕ)
    (h_sum : ∑ i : Fin (k+1), c i = m + ((k+1).choose 2)) :
    MvPolynomial.coeff (toFinsupp c)
      ((∑ i : Fin (k+1), X i) ^ m *
       ∏ i : Fin (k+1), ∏ j : Fin (k+1), if j < i then (X i - X j) else 1)
    = expected_value c m := by admit

/-- S = {a₀ + ... + aₖ | aᵢ ∈ Aᵢ, aᵢ ≠ aⱼ for all i ≠ j} -/
def restricted_sum_set (k : ℕ) (A : Fin (k+1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter fun f =>
    ∀ (i j : Fin (k+1)), i < j → f i ≠ f j)
    |>.image (fun f => ∑ i, f i)

/-- Vandermonde: ∏_{i>j} (Xᵢ - Xⱼ) -/
noncomputable def vandermonde_polynomial (k : ℕ) : MvPolynomial (Fin (k+1)) (ZMod p) :=
  ∏ i : Fin (k+1), ∏ j : Fin (k+1),
    if j.val < i.val then (X i - X j) else 1

/--
Proposition 1.2:
Let p be a prime, and let A₀, A₁, ..., Aₖ be nonempty subsets of Z_p.
If |A_i| ≠ |A_j| for all 0 ≤ i < j ≤ k and ∑_{i=0}^k |A_i| ≤ p + (k+2 choose 2) - 1,
then |{a₀ + ... + aₖ : a_i ∈ A_i, a_i ≠ a_j for all i ≠ j}| ≥ ∑_{i=0}^k |A_i| - (k+2 choose 2) + 1.

Detailed proof:
1. Define the Vandermonde polynomial h(x₀, ..., xₖ) = ∏_{k ≥ i > j ≥ 0} (x_i - x_j).
   This polynomial is nonzero exactly when all x_i are distinct.

2. Let c_i = |A_i| - 1, so that |A_i| = c_i + 1.

3. Compute m = ∑_{i=0}^k c_i - (k+1 choose 2)
            = (∑_{i=0}^k |A_i| - (k+1)) - (k+1 choose 2)
            = ∑_{i=0}^k |A_i| - (k+2 choose 2)

4. We need m < p. From the hypothesis ∑ |A_i| ≤ p + (k+2 choose 2) - 1,
   we get m = ∑ |A_i| - (k+2 choose 2) ≤ p - 1 < p.

5. By Lemma 3.1, the coefficient of the monomial ∏ x_i^{c_i} in h·(∑ x_i)^m is:
      (m! / ∏ c_i!) · ∏_{i>j} (c_i - c_j)
   Since the c_i are all distinct and m < p, this coefficient is nonzero modulo p.

6. Apply Theorem 2.1 with this h, the sets A_i, and parameters c_i, m.
   The theorem gives:
      |⊕_h ∑_{i=0}^k A_i| ≥ m + 1

7. Note that ⊕_h ∑ A_i = {∑ a_i : a_i ∈ A_i, h(a) ≠ 0}
                     = {∑ a_i : a_i ∈ A_i, a_i ≠ a_j for all i ≠ j}
   since h(a) = 0 iff some a_i = a_j for i ≠ j.

8. Therefore:
      |{∑ a_i : a_i ∈ A_i, a_i distinct}| ≥ m + 1
                                        = ∑ |A_i| - (k+2 choose 2) + 1
   which completes the proof.
-/
theorem restricted_sum_distinct_sizes (A : Fin (k+1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sizes_distinct : ∀ i j, i < j → (A i).card ≠ (A j).card)
    (h_sum_bound : ∑ i, (A i).card ≤ p + (Nat.choose (k+2) 2) - 1) :
    (restricted_sum_set k A).card ≥ ∑ i, (A i).card - (Nat.choose (k+2) 2) + 1 := by sorry
