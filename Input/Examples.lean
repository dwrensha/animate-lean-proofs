import Mathlib.Tactic

theorem foo0 {A : Prop} : A → A := by
  intro h
  exact h

theorem foo1 (n : ℕ) : n = n := by
  rfl

theorem foo2 (n : ℕ) : n = n := by
  have : True := True.intro
  have : True := by exact True.intro
  induction n with
  | zero => have : True := True.intro; rfl
  | succ _ _ => rfl

theorem foo3 (n : ℕ) : n = n := by
  induction' n with n _ih
  · rfl
  · rfl

theorem foo4 (A B C : Prop) : A ∧ B ∧ C → C ∧ B ∧ A := by
  intro habc
  obtain ⟨ha, hb, hc⟩ := habc
  exact ⟨hc, (by have := True.intro; exact hb), by exact ha⟩

theorem foo5 (a b : ℕ) (hab : a ≤ b) : b - a + a - a + a = b := by
  simp only [show b - a + a = b by exact Nat.sub_add_cancel hab]

theorem foo6 (m n : ℕ) : m = m ∧ n = n := by
  constructor <;> rfl

theorem foo7 (m n : ℕ) : m = m ∧ n = n := by
  constructor <;> (have := True.intro; rfl)

theorem foo8 (A B C : Prop) : A ∧ B ∧ C → C ∧ A ∧ B := by
  rintro ⟨ha, hb, hc⟩
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · exact ha
  · exact hb
  · exact hc

theorem foo9 (a b : ℕ) (h : a > b + 1) : b + 1 < a := by
  change b + 1 < a at h
  exact h

theorem foo10 : 1 < 5 := by
  calc 1 < 2 := by exact Nat.one_lt_two
       _ < 5 := by exact Nat.lt_of_sub_eq_succ rfl

theorem foo11 (m n : ℕ) : m = m ∧ n + 1 > n := by
  constructor <;> (have := True.intro; try rfl)
  exact lt_add_one n

/-
Exception: start state does not match previous end state
⊢ 0 = 0
 vs
case zero
⊢ 0 = 0
-/
theorem foo12 (n : ℕ) : n = n := by
  induction n
  case zero =>
    have := True.intro
    rfl
  case succ m _ih =>
    rfl
