import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Arbitrarily long arithmetic progressions force small multiplicative gaps

Problem: https://lefttosolve.com/p/mo-475837
Source: https://mathoverflow.net/questions/475837

This independent proof establishes the exact statement from the site's merged
statement file. It first proves a stronger assertion: for every factor L > 1
and every starting index K, a suitable consecutive pair occurs at an index
k >= K. Thus, for each L > 1, there are infinitely many suitable indices.

Choose a natural number N larger than both s K and 1 / (L - 1). Take the last
two terms x = a + N*d and y = x + d of an (N + 2)-term arithmetic progression
in the sequence. Then x > s K, and d < (L - 1)*x gives y < L*x. The successor
of x in the original sequence is no greater than y.

Pinned environment: Lean 4.33.1; Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474.
The final commands report the kernel axioms used by both theorems.
-/

/-- Small multiplicative gaps occur after every prescribed starting index. -/
theorem mo475837_small_gaps_arbitrarily_late :
    ∀ s : ℕ → ℕ, StrictMono s →
    (∀ m : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ j < m, a + j * d ∈ Set.range s) →
    ∀ L : ℝ, 1 < L → ∀ K : ℕ,
      ∃ k : ℕ, K ≤ k ∧ (s (k + 1) : ℝ) < L * s k := by
  intro s hs hAP L hL K
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / (L - 1)) (s K : ℝ))
  obtain ⟨a, d, hd, hAP⟩ := hAP (N + 2)
  obtain ⟨k, hk⟩ := hAP N (by omega)
  obtain ⟨j, hj⟩ := hAP (N + 1) (by omega)
  have hNK : s K < N := by
    exact_mod_cast (le_max_right (1 / (L - 1)) (s K : ℝ)).trans_lt hN
  have hNmul : N ≤ N * d := Nat.le_mul_of_pos_right _ hd
  have hKk : K ≤ k := hs.le_iff_le.mp (by rw [hk]; omega)
  have hkj : k < j := hs.lt_iff_lt.mp (by
    rw [hk, hj, Nat.add_mul, Nat.one_mul]
    omega)
  have hnext : s (k + 1) ≤ a + (N + 1) * d := by
    simpa only [hj] using hs.monotone (Nat.succ_le_of_lt hkj)
  have hnext' : (s (k + 1) : ℝ) ≤ (a + (N + 1) * d : ℕ) := by
    exact_mod_cast hnext
  refine ⟨k, hKk, lt_of_le_of_lt hnext' ?_⟩
  rw [hk]
  push_cast
  have hLN : 1 < (N : ℝ) * (L - 1) :=
    (div_lt_iff₀ (sub_pos.mpr hL)).mp ((le_max_left _ _).trans_lt hN)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hbound := mul_lt_mul_of_pos_right hLN hd'
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (le_of_lt (sub_pos.mpr hL))]

/-- The exact statement of LeftToSolve problem mo-475837. -/
theorem mo475837_solution :
    ∀ s : ℕ → ℕ, StrictMono s →
    (∀ m : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ j < m, a + j * d ∈ Set.range s) →
    ∀ L : ℝ, 1 < L → ∃ k : ℕ, (s (k + 1) : ℝ) < L * s k := by
  intro s hs hAP L hL
  obtain ⟨k, _, hk⟩ := mo475837_small_gaps_arbitrarily_late s hs hAP L hL 0
  exact ⟨k, hk⟩

#print axioms mo475837_small_gaps_arbitrarily_late
#print axioms mo475837_solution
