-- From Kim Morrison, LFTCM 2020.
-- https://www.youtube.com/watch?v=b59fpAJ8Mfs
-- https://leanprover.zulipchat.com/#narrow/stream/238830-Lean-for-the-curious-mathematician-2020/topic/Zoom/near/203703811

import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Linarith

open scoped Nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N

  let M := N ! + 1
  let p := Nat.minFac M

  have pp : Nat.Prime p := by
    refine Nat.minFac_prime ?_
    have : N ! > 0 := Nat.factorial_pos N
    omega

  use p
  constructor
  · by_contra H
    have h₁ : p ∣ N ! + 1 := Nat.minFac_dvd M
    have h₂ : p ∣ N ! := (Nat.Prime.dvd_factorial pp).mpr (le_of_not_ge H)
    have h : p ∣ 1 := (Nat.dvd_add_right h₂).mp h₁
    exact Nat.Prime.not_dvd_one pp h
  · exact pp

