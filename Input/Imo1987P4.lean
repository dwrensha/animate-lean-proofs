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
      refine Set.diff_union_diff_cancel ?_ ?_
      · exact Set.subset_univ _
      · exact Set.image_mono (Set.subset_univ _)
    · ext x
      rw [Set.mem_setOf_eq]
      rw [←not_iff_not]
      rw [←Set.compl_eq_univ_diff]
      rw [Set.not_mem_compl_iff]
      rw [not_lt]
      simp only [Set.mem_image, Set.mem_univ, true_and, exists_exists_eq_and]
      simp only [hf]
      rw [le_iff_exists_add']
      simp_rw [eq_comm]

  -- |A ∪ B| = 2 * m + 1
  have ab_card : Set.ncard (A ∪ B) = 2 * m + 1 := by
    rw [ab_range, Set.Iio_def, ←Finset.coe_range, Set.ncard_coe_Finset]
    exact Finset.card_range (2 * m + 1)

  -- A and B are disjoint.
  have ab_disj : Disjoint A B := by
    rw [Set.disjoint_right]
    aesop

  -- Since f is injective, A and B have the same number of elements,
  -- which is impossible since 2 * m + 1 is odd.

  replace ab_card : A.ncard + B.ncard = 2 * m + 1 := by
    obtain ⟨a_finite, b_finite⟩ :=
      Set.finite_union.mp (ab_range ▸ Set.finite_lt_nat _)
    rw [Set.ncard_union_eq ab_disj a_finite b_finite] at ab_card
    exact ab_card

  rw [Set.ncard_image_of_injective _ f_inj] at ab_card
  omega
