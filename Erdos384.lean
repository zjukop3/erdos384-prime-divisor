/-!
# Erdős Problem 384

The problem-page formulation uses the strict bound `p < n / 2`.
Ecklund's published theorem uses the non-strict bound `p ≤ n / 2`.
The strict formulation is false for `n = 4`, `k = 2`, since every
prime is at least 2, so `2 * p ≥ 4 = n`, contradicting `2 * p < n`.

Reference: https://www.erdosproblems.com/384
Mathematical source: E. F. Ecklund, Jr., "On prime divisors of the
binomial coefficient", Pacific J. Math. 29 (1969), 267–270.
-/

namespace Erdos384

/-- A natural number is prime if n ≥ 2 and no d with 2 ≤ d < n divides n. -/
structure IsPrime (n : Nat) : Prop where
  two_le : 2 ≤ n
  no_div : ∀ d : Nat, 2 ≤ d → d < n → ¬ (d ∣ n)

/-- Factorial: n! = 1 * 2 * ... * n (structural recursion, no axioms). -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Binomial coefficient C(n, k) = n! / (k! * (n-k)!). -/
def binom (n k : Nat) : Nat :=
  factorial n / (factorial k * factorial (n - k))

/-- Erdős Problem 384 (strict formulation) is false.
    Counterexample: n = 4, k = 2. C(4,2) = 6.
    Every prime p ≥ 2, so 2*p ≥ 4 = n, contradicting 2*p < n. -/
theorem not_erdos_384 :
    ¬ (∀ n k : Nat, 1 < k → k < n - 1 →
      ∃ p : Nat, IsPrime p ∧ 2 * p < n ∧ p ∣ binom n k) := by
  intro h
  have hwitness : ∃ p, IsPrime p ∧ 2 * p < 4 ∧ p ∣ binom 4 2 :=
    h 4 2 (by decide) (by decide)
  match hwitness with
  | ⟨p, hp⟩ =>
    match hp with
    | ⟨hp_prime, hp_rest⟩ =>
      match hp_rest with
      | ⟨hlt, _⟩ =>
        have hp2 : 2 ≤ p := hp_prime.two_le
        omega

end Erdos384
