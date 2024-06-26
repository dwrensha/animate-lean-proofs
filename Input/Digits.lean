import Mathlib.Data.Nat.Digits

open Nat

theorem digits_len_le_digits_len_succ (b n : ℕ) :
    (digits b n).length ≤ (digits b (n + 1)).length := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases le_or_lt b 1 with hb | hb
  · interval_cases b <;> simp_arith [digits_zero_succ', hn]
  simpa [digits_len, hb, hn] using log_mono_right (le_succ _)

theorem digit_sum_le (p n : ℕ) : (digits p n).sum ≤ n := by
  induction' n with n
  · rw [digits_zero]
    exact Nat.le_refl (List.sum [])
  · induction' p with p
    · rw [digits_zero_succ, List.sum_cons]
      rw [List.sum_nil, add_zero]
    · nth_rw 2 [← ofDigits_digits p.succ (n + 1)]
      rw [← ofDigits_one (digits p.succ n.succ)]
      refine ofDigits_monotone (digits p.succ n.succ) ?_
      exact Nat.succ_pos p
