/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Lince
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Real.Basic

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
* `ArithmeticFunction.sum_cardDistinctFactors_Ioc_le` and
  `ArithmeticFunction.le_sum_cardDistinctFactors_Ioc`: the first moment is `N * ∑ 1/p` up to
  an error of at most `N`.
* `ArithmeticFunction.sum_cardDistinctFactors_sq_Ioc_le`: the second moment is at most
  `N * S ^ 2 + N * S`, where `S = ∑ 1/p`.
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

/-- The lower half of the floor bracket, cast to an ordered field: `N / p - 1 < ⌊N / p⌋`.
The upper half is `Nat.cast_div_le`. -/
theorem sub_one_lt_cast_div {p : ℕ} (N : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 < ((N / p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h1 : N < p * (N / p) + p := by
    have hdm := Nat.div_add_mod N p
    have hm := Nat.mod_lt N hp
    omega
  have h2 : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) : ℝ) + p := by exact_mod_cast h1
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp0]
  nlinarith

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

/-- **First moment, upper bound**: `∑_{n ≤ N} ω n ≤ N * ∑_{p ≤ N} 1/p`. -/
theorem sum_cardDistinctFactors_Ioc_le (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N, ω n : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
  rw [sum_cardDistinctFactors_Ioc, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
  rwa [div_eq_mul_inv] at h

/-- **First moment, lower bound**: `N * ∑_{p ≤ N} 1/p - N ≤ ∑_{n ≤ N} ω n`. The loss is one
unit per prime, and there are at most `N` primes in `(0, N]`. -/
theorem le_sum_cardDistinctFactors_Ioc (N : ℕ) :
    (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - N
      ≤ ((∑ n ∈ Finset.Ioc 0 N, ω n : ℕ) : ℝ) := by
  have hterm : ∀ p ∈ {p ∈ Finset.Ioc 0 N | p.Prime},
      (N : ℝ) * (p : ℝ)⁻¹ - 1 ≤ ((N / p : ℕ) : ℝ) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have h := Nat.sub_one_lt_cast_div N hpp.pos
    rw [div_eq_mul_inv] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hsum
  have hcard : ((#{p ∈ Finset.Ioc 0 N | p.Prime} : ℕ) : ℝ) ≤ N := by
    have h1 := Finset.card_filter_le (Finset.Ioc 0 N) Nat.Prime
    have h2 : (Finset.Ioc 0 N).card = N := by rw [Nat.card_Ioc, Nat.sub_zero]
    exact_mod_cast h1.trans_eq h2
  rw [sum_cardDistinctFactors_Ioc, Nat.cast_sum]
  linarith

/-- **Second moment, upper bound**: `∑_{n ≤ N} ω(n)^2 ≤ N * S ^ 2 + N * S`, where
`S = ∑_{p ≤ N} 1/p`. The off-diagonal pairs are dominated by the full square `N * S ^ 2`,
the diagonal by `N * S`. -/
theorem sum_cardDistinctFactors_sq_Ioc_le (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N, ω n ^ 2 : ℕ) : ℝ)
      ≤ (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2
        + (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
  have hpair : ∀ p ∈ {p ∈ Finset.Ioc 0 N | p.Prime}, ∀ q ∈ {q ∈ Finset.Ioc 0 N | q.Prime},
      ((#{n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n} : ℕ) : ℝ)
        ≤ (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
          + if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0 := by
    intro p hp q hq
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hqq : q.Prime := (Finset.mem_filter.mp hq).2
    rw [Nat.card_filter_dvd_pair N hpp hqq]
    rcases eq_or_ne p q with rfl | hpq
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      have h1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) * (p : ℝ)⁻¹ := by
        have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
        rwa [div_eq_mul_inv] at h
      have h2 : (0 : ℝ) ≤ (N : ℝ) * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by positivity
      linarith
    · rw [ite_eq_right hpq, ite_eq_right hpq, add_zero]
      calc ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) * (q : ℝ)) := by
            have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p * q)
            rwa [Nat.cast_mul] at h
        _ = (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ := by rw [div_eq_mul_inv, mul_inv]; ring
  have hfirst : ∑ p ∈ Finset.Ioc 0 N with p.Prime,
      ∑ q ∈ Finset.Ioc 0 N with q.Prime, (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
      = (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2 := by
    calc ∑ p ∈ Finset.Ioc 0 N with p.Prime,
          ∑ q ∈ Finset.Ioc 0 N with q.Prime, (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
        = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((N : ℝ) * (p : ℝ)⁻¹)
            * ∑ q ∈ Finset.Ioc 0 N with q.Prime, ((q : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
      _ = (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, sq]; ring
  have hdiag : ∑ p ∈ Finset.Ioc 0 N with p.Prime,
      ∑ q ∈ Finset.Ioc 0 N with q.Prime, (if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0)
      = (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
    have h1 : ∀ p ∈ {p ∈ Finset.Ioc 0 N | p.Prime},
        ∑ q ∈ Finset.Ioc 0 N with q.Prime, (if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0)
        = (N : ℝ) * (p : ℝ)⁻¹ := by
      intro p hp
      rw [Finset.sum_ite_eq _ p fun _ => (N : ℝ) * (p : ℝ)⁻¹, ite_eq_left hp]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  calc ((∑ n ∈ Finset.Ioc 0 N, ω n ^ 2 : ℕ) : ℝ)
      = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((#{n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n} : ℕ) : ℝ) := by
        rw [sum_cardDistinctFactors_sq_Ioc]; push_cast; rfl
    _ ≤ ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ + if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hpair p hp q hq
    _ = (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2
        + (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
        rw [← hfirst, ← hdiag, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib

end ArithmeticFunction
