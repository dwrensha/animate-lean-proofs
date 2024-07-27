-- This file contains a heavily cleaned up version of the
-- solution [1] that AlphaProof produced for problem 2 on IMO 2024.
-- See the video [2] for more commentary about how this proof.
-- See also DeepMind's announcement blog post [3].
--
-- [1] https://storage.googleapis.com/deepmind-media/DeepMind.com/Blog/imo-2024-solutions/P2/index.html
-- [2] https://youtu.be/5IARsdn78xE
-- [3] https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Have
import Annotations

open scoped Nat

theorem imo_2024_p2 :
    {(a, b) |  0 < a ∧ 0 < b ∧
      ∃ g N, 0 < g ∧ 0 < N ∧
        ∀ n ≥ N, Nat.gcd (a ^ n + b) (b ^ n + a) = g} =
    {(1, 1)} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · simp only [Set.mem_setOf]
    use one_pos; use one_pos
    use 2; use 1
    use two_pos; use one_pos
    rintro n -
    simp only [one_pow]
    exact Nat.gcd_self 2

  rintro ⟨a, b⟩
  rintro ⟨a_pos, b_pos, g, N, -, -, D⟩

  have a_coprime : a.Coprime (1 + a * b) := by
    rw [Nat.coprime_add_mul_left_right]
    exact Nat.coprime_one_right _
  have b_coprime : b.Coprime (1 + a * b) := by
    rw [Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right _

  have a_euler := Nat.ModEq.pow_totient a_coprime
  have b_euler := Nat.ModEq.pow_totient b_coprime
  rw [←ZMod.natCast_eq_natCast_iff] at a_euler b_euler

  have totient_pos :=
    ((1 + a*b).totient_pos).mpr ((zero_le _).trans_lt (lt_one_add _))

  suffices h : 1 + a * b ∣ g
  · specialize D (φ (1+a*b)*N) (Nat.le_mul_of_pos_left N totient_pos)
    have ⟨Ha, Hb⟩ :=
      D ▸ Nat.gcd_dvd (a ^ (φ (1 + a * b) * N) + b) (b ^ (φ (1 + a * b) * N) + a)
    atomic (replace Ha := h.trans Ha; replace Hb := h.trans Hb)
    clear g D a_coprime b_coprime totient_pos h
    reverse_s1_s2(rw [←ZMod.natCast_zmod_eq_zero_iff_dvd, pow_mul] at Ha Hb)
    push_cast at a_euler b_euler Ha Hb
    reverse_s1_s2(rw [a_euler] at Ha; clear a_euler)
    reverse_s1_s2(rw [b_euler] at Hb; clear b_euler)
    rw [one_pow] at Ha Hb
    norm_cast at Ha Hb
    reverse_s2(rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at Ha Hb)
    atomic(replace Ha := Nat.le_of_dvd (Nat.add_pos_right 1 b_pos) Ha
           replace Hb := Nat.le_of_dvd (Nat.add_pos_right 1 a_pos) Hb)
    rw [Prod.mk.injEq]
    atomic(constructor <;> nlinarith only [a_pos, b_pos, Ha, Hb])

  suffices h : ∃ n ≥ N, 1 + a * b ∣ a * (a ^ n + b) ∧
                        1 + a * b ∣ b * (b ^ n + a)
  · obtain ⟨n, hn, h⟩ := h
    replace h := And.intro
      (Nat.Coprime.dvd_of_dvd_mul_left a_coprime.symm h.1)
      (Nat.Coprime.dvd_of_dvd_mul_left b_coprime.symm h.2)
    replace h := Nat.dvd_gcd h.1 h.2
    rw [D _ hn] at h
    exact h
  clear D g a_coprime b_coprime a_pos b_pos

  use φ (1 + a * b) * (N + 1) - 1
  use N.le_sub_of_add_le (Nat.le_mul_of_pos_left (N + 1) totient_pos)

  atomic(
   obtain ⟨w, h : _ = w + 1⟩ := Nat.exists_eq_add_of_le' totient_pos
   clear totient_pos
  )
  simp only [←ZMod.natCast_zmod_eq_zero_iff_dvd, pow_add]
  push_cast at a_euler b_euler ⊢
  atomic (rw [h] at a_euler b_euler ⊢; clear h)
  constructor <;>
  simp only [mul_add, ←pow_succ', mul_one, Nat.add_succ_sub_one] <;>
  rw [add_assoc, ←mul_add_one] <;>
  rw [pow_mul] <;>
  atomic(simp only [a_euler, b_euler]; clear a_euler b_euler) <;>
  simp only [one_pow] <;>
  norm_cast <;>
  simp only [ZMod.natCast_zmod_eq_zero_iff_dvd] <;>
  ring_nf <;>
  exact dvd_refl _

#print axioms imo_2024_p2
