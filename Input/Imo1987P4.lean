/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Aesop
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

namespace Imo1987P4

theorem imo1987_p4 : ¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987 := by
  -- Informal solution by Sawa Pavlov, listed at
  -- https://artofproblemsolving.com/wiki/index.php/1987_IMO_Problems/Problem_4

  -- We will prove a more general statement.
  suffices generalized :
    ∀ m : ℕ, ¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + (2 * m + 1) from
      generalized 993

  rintro m ⟨f, hf⟩

  -- Note that f is injective, because if f(x) = f(y),
  -- then f(f(x)) = f(f(y)), so x = y.
  have f_inj : f.Injective := by
    intro x y hxy;
    have hfx := hf x;
    rw [hxy] at hfx
    rw [hf y] at hfx
    exact Nat.add_right_cancel hfx.symm

  -- Let A := ℕ - f(ℕ) and B := f(A).
  let A : Set ℕ := Set.univ \ (f '' Set.univ)
  let B : Set ℕ := f '' A

  -- A ∪ B = {0, 1, ... , 2 * m}.
  have ab_range : A ∪ B = {n | n < 2 * m + 1} := by
    calc A ∪ B
       = Set.univ \ (f '' (f '' Set.univ)) := ?_
       _ = {n | n < 2 * m + 1} := ?_
    · -- Note that B = f(ℕ) - f(f(ℕ)).
      unfold_let B
      rw [Set.image_diff f_inj]
      unfold_let A
      have sub1 : f '' Set.univ ⊆ Set.univ := Set.subset_univ _
      have sub2 : f '' (f '' Set.univ) ⊆ f '' Set.univ := Set.image_mono sub1
      generalize Set.univ = X at *
      generalize f '' X = Y at *
      generalize f '' Y = Z at *
      exact Set.diff_union_diff_cancel sub1 sub2
    · apply Set.eq_of_subset_of_subset
      · intro x hx
        simp only [Set.mem_diff, Set.mem_univ, true_and] at hx
        simp only [Set.image_univ, Set.mem_image, Set.mem_range,
                   exists_exists_eq_and, not_exists] at hx
        rw [Set.mem_setOf_eq]
        by_contra! H
        obtain ⟨z, hz⟩ : ∃ z, x = z + (2 * m + 1) := Nat.exists_eq_add_of_le' H
        specialize hx z
        rw [hz, hf z, add_comm] at hx
        exact (hx rfl).elim
      · intro x hx
        rw [Set.mem_setOf_eq] at hx
        simp only [Set.mem_diff, Set.mem_univ, true_and]
        intro hfx
        obtain ⟨y, hz, hzy⟩ := hfx
        obtain ⟨z, _, hz2⟩ := hz
        specialize hf z
        rw [hz2] at hf
        rw [hzy] at hf
        rw [hf] at hx
        rw [add_lt_iff_neg_right] at hx
        exact Nat.not_succ_le_zero z hx

  -- A and B are disjoint.
  have ab_disj : Disjoint A B := by
    rw [Set.disjoint_right]
    aesop

  -- But since f is injective, A and B have the
  -- same number of elements, which is impossible since {0, 1, ... , 2 * m}
  -- has an odd number of elements.

  have ab_card : Set.ncard (A ∪ B) = 2 * m + 1 := by
    rw [ab_range, Set.Iio_def, ←Finset.coe_range, Set.ncard_coe_Finset]
    exact Finset.card_range (2 * m + 1)

  replace ab_card : A.ncard + B.ncard = 2 * m + 1 := by
    have ab_finite : (A ∪ B).Finite := by
      rw [ab_range]; exact Set.finite_lt_nat _
    obtain ⟨a_finite, b_finite⟩ := Set.finite_union.mp ab_finite
    rwa [Set.ncard_union_eq ab_disj a_finite b_finite] at ab_card

  rw [Set.ncard_image_of_injective _ f_inj] at ab_card
  omega
