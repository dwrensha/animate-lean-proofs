import Lean
import Lean.Elab.Tactic.Induction
import Mathlib.Tactic

namespace NNG

section tactics

-- Make `rw` mean `rewrite`, so that it does not automatically close goals with `rfl`.
macro (name := rwSeq) "rw " c:Lean.Parser.Tactic.optConfig s:Lean.Parser.Tactic.rwRuleSeq l:(Lean.Parser.Tactic.location)? : tactic => do
    `(tactic| (rewrite $c $s:rwRuleSeq $(l)?))

end tactics

section power

-- level 7
theorem mul_pow
    (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with t Ht
  · rw [pow_zero]
    rw [pow_zero]
    rw [pow_zero]
    rw [mul_one]
    rfl
  · rw [pow_succ]
    rw [pow_succ]
    rw [pow_succ]
    rw [Ht]
    simp only [mul_assoc]
    rw [mul_comm a (_ * b)]
    rw [mul_assoc]
    rw [mul_comm b a]
    rfl

-- level 9
theorem add_sq
    (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [pow_two]
  rw [pow_two]
  rw [pow_two]
  rw [add_right_comm]
  rw [mul_add]
  rw [add_mul]
  rw [add_mul]
  rw [two_mul]
  rw [add_mul]
  rw [mul_comm b a]
  rw [← add_assoc]
  rw [← add_assoc]
  rfl

end power
