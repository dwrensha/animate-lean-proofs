
theorem tutorial (a b c : Prop) (hab : a = b) (hc : c)
    : a → b ∧ c := by
  intro ha
  constructor
  · rwa [←hab]
  · exact hc

theorem test (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  obtain p | q := h
  · right
    exact p
  · left
    exact q
