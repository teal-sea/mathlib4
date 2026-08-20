/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Lince
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Double counting for the number of distinct prime factors

This file proves the two counting identities that express the first and second moments of
`ω`, the number of distinct prime factors, as sums over primes:

$$ \sum_{n \le N} \omega(n) = \sum_{p \le N} \left\lfloor N/p \right\rfloor $$

and the corresponding expansion of `∑ ω(n)²` as a sum over ordered pairs of primes. Both are
unconditional and purely combinatorial: they count the pairs `(p, n)`, resp. triples
`(p, q, n)`, with `p ∣ n` in two ways.

These are the first step of Turán's variance estimate, which is in turn the route to the
Hardy–Ramanujan theorem on the normal order of `ω`.

## Main results

* `Nat.primeFactors_eq_filter_Ioc`: for `0 < n ≤ N`, the prime factors of `n` are the primes
  in `(0, N]` dividing `n`.
* `ArithmeticFunction.sum_cardDistinctFactors_Ioc`: the first moment, `∑ ω n = ∑ N / p`.
* `ArithmeticFunction.sum_cardDistinctFactors_sq_Ioc`: the second moment, as a double sum
  over primes.
* `Nat.card_filter_dvd_pair`: the pair count behind the second moment.
-/

@[expose] public section

open Finset

namespace Nat

/-- For `0 < n ≤ N`, the prime factors of `n` are exactly the primes in `(0, N]` dividing `n`. -/
theorem primeFactors_eq_filter_Ioc {N n : ℕ} (hn : n ∈ Finset.Ioc 0 N) :
    n.primeFactors = {p ∈ Finset.Ioc 0 N | p.Prime ∧ p ∣ n} := by
  rw [Finset.mem_Ioc] at hn
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hp, hpd, -⟩
    exact ⟨⟨hp.pos, (Nat.le_of_dvd hn.1 hpd).trans hn.2⟩, hp, hpd⟩
  · rintro ⟨-, hp, hpd⟩
    exact ⟨hp, hpd, hn.1.ne'⟩

/-- The number of `n ∈ (0, N]` divisible by both of the primes `p` and `q`: `⌊N/p⌋` on the
diagonal, and `⌊N/(pq)⌋` off it, since distinct primes are coprime. -/
theorem card_filter_dvd_pair {p q : ℕ} (N : ℕ) (hp : p.Prime) (hq : q.Prime) :
    #{n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n} = if p = q then N / p else N / (p * q) := by
  rcases eq_or_ne p q with rfl | hpq
  · rw [ite_eq_left rfl]
    simp only [and_self]
    exact Nat.Ioc_filter_dvd_card_eq_div N p
  · rw [ite_eq_right hpq]
    have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hiff : ∀ n ∈ Finset.Ioc 0 N, (p ∣ n ∧ q ∣ n) ↔ p * q ∣ n := fun n _ =>
      ⟨fun ⟨h1, h2⟩ => hco.mul_dvd_of_dvd_of_dvd h1 h2,
        fun h => ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩⟩
    rw [Finset.filter_congr hiff]
    exact Nat.Ioc_filter_dvd_card_eq_div N (p * q)

end Nat

namespace ArithmeticFunction

open scoped ArithmeticFunction.omega

/-- `ω n` is the cardinality of `n.primeFactors`. -/
theorem cardDistinctFactors_eq_card_primeFactors (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- For `0 < n ≤ N`, `ω n` counts the primes `p ≤ N` dividing `n`. -/
theorem cardDistinctFactors_eq_sum_ite {N n : ℕ} (hn : n ∈ Finset.Ioc 0 N) :
    ω n = ∑ p ∈ Finset.Ioc 0 N with p.Prime, if p ∣ n then 1 else 0 := by
  rw [cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_eq_filter_Ioc hn,
    Finset.card_filter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ => by
    by_cases h1 : p.Prime <;> by_cases h2 : p ∣ n <;> simp [h1, h2]

/-- **The first moment of `ω`**: `∑_{n ≤ N} ω n = ∑_{p ≤ N prime} ⌊N/p⌋`.

Both sides count the pairs `(p, n)` with `p` prime, `p ∣ n` and `0 < n ≤ N`. -/
theorem sum_cardDistinctFactors_Ioc (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ω n = ∑ p ∈ Finset.Ioc 0 N with p.Prime, N / p := by
  have hL : ∑ n ∈ Finset.Ioc 0 N, ω n
      = ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ Finset.Ioc 0 N,
          if p.Prime ∧ p ∣ n then 1 else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_eq_filter_Ioc hn,
      Finset.card_filter]
  rw [hL, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · rw [ite_eq_left hp]
    simp only [hp, true_and]
    rw [← Finset.card_filter]
    exact Nat.Ioc_filter_dvd_card_eq_div N p
  · simp [hp]

/-- **The second moment of `ω`**: `∑_{n ≤ N} ω(n)²` counts the triples `(p, q, n)` with
`p, q` prime and `p ∣ n`, `q ∣ n`, grouped by the pair. -/
theorem sum_cardDistinctFactors_sq_Ioc (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ω n ^ 2
      = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          #{n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n} := by
  calc ∑ n ∈ Finset.Ioc 0 N, ω n ^ 2
      = ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ Finset.Ioc 0 N with p.Prime,
          ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((if p ∣ n then 1 else 0) * if q ∣ n then 1 else 0) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [sq, cardDistinctFactors_eq_sum_ite hn, Finset.sum_mul_sum]
    _ = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ∑ n ∈ Finset.Ioc 0 N,
          ((if p ∣ n then 1 else 0) * if q ∣ n then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          #{n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n} := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]

end ArithmeticFunction
