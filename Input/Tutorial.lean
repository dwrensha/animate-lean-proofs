
theorem tutorial (a b c : Prop) (hab : a = b) (hc : c)
    : a → b ∧ c := by
  intro ha
  constructor
  · rwa [←hab]
  · exact hc
