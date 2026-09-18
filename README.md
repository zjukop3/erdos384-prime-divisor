# Erdős Problem 384 — Prime Divisors of Binomial Coefficients

## Problem

The problem-page formulation uses the strict bound `p < n/2`: for all `n`, `k` with `1 < k < n-1`, does `C(n,k)` have a prime divisor `p` with `p < n/2`?

## Answer

No. The strict formulation is false for `n = 4`, `k = 2`, since every prime `p ≥ 2`, so `2·p ≥ 4 = n`, contradicting `2·p < n` (i.e., `p < n/2`).

The non-strict bound `p ≤ n/2` (Ecklund's theorem) IS true, with a finite list of exceptions.

## Formalization

Pure Lean 4 (no Mathlib dependency). Axioms: `propext`, `Classical.choice`, `Quot.sound` (standard Lean axioms).

```lean
structure IsPrime (n : Nat) : Prop where
  two_le : 2 ≤ n
  no_div : ∀ d : Nat, 2 ≤ d → d < n → ¬ (d ∣ n)

theorem not_erdos_384 :
    ¬ (∀ n k : Nat, 1 < k → k < n - 1 →
      ∃ p : Nat, IsPrime p ∧ 2 * p < n ∧ p ∣ binom n k) := by
  intro h
  have hwitness := h 4 2 (by decide) (by decide)
  match hwitness with
  | ⟨p, ⟨hp_prime, ⟨hlt, _⟩⟩⟩ =>
    have hp2 : 2 ≤ p := hp_prime.two_le
    omega
```

## Verification

- Build: `lake build` (succeeds)
- Axiom audit: `lake env lean Audit.lean` → `propext`, `Classical.choice`, `Quot.sound`
- 0 sorry, 0 admit

## References

- [erdosproblems.com/384](https://www.erdosproblems.com/384)
- E. F. Ecklund, Jr., "On prime divisors of the binomial coefficient", Pacific J. Math. 29 (1969), 267–270.

## License

MIT

## Attribution

Independent formalization by zjukop3. The counterexample n=4, k=2 is elementary.
