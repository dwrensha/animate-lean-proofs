import Lean.Data.Json.FromToJson
import Batteries.Data.List

namespace Animate

structure IndexMaps where
  s1_to_s2 : Array (Option Nat)
  s2_to_s1 : Array (Option Nat)
deriving Lean.ToJson, Lean.FromJson

structure BestMatch where
  start_ii : Nat
  start_jj : Nat
  length : Nat

def get_hyps_start (s1 : List Char) : Nat :=
  match (s1.findIdx? (· = '\n'), s1.findIdx? (· = ':')) with
  | (none, none) => 0
  | (none, some _) => 0
  | (some n, none) => n + 1
  | (some nn, some nc) =>
      if nn < nc then nn + 1 else 0

def get_next_best_match (s1 s2 : List Char) (im : IndexMaps) (nonmatchers : String := "")
    (s1_reverse_order := false)
    (s2_reverse_order := false)
    : BestMatch := Id.run do
  let mut best : BestMatch := ⟨0, 0, 0⟩

  -- HACK
  let s1_hyps_start := get_hyps_start s1
  let s2_hyps_start := get_hyps_start s2

  let s1 := s1.toArray
  let s2 := s2.toArray

  let s1range := if s1_reverse_order then (List.range s1.size).reverse else List.range s1.size
  let s2range := if s2_reverse_order then (List.range s2.size).reverse else List.range s2.size

  for ii in s1range do
    for jj in s2range do
      let mut kk := 0
      if s1[ii + kk]! ∉ nonmatchers.toList then
      while ii + kk < s1.size && jj + kk < s2.size &&
            s1[ii + kk]! = s2[jj + kk]! &&
            im.s1_to_s2[ii + kk]! = none &&
            im.s2_to_s1[jj + kk]! = none do
        kk := kk + 1

      if ii < s1_hyps_start ∧ s2_hyps_start ≤ jj
      then continue

      if s1_hyps_start ≤ ii ∧ jj < s2_hyps_start
      then continue

      if kk > best.length then
        best := ⟨ii, jj, kk⟩
  return best

def do_match (s1 s2 : String) (min_match_len : Nat := 1) (nonmatchers : String := "")
    (s1_reverse_order := false)
    (s2_reverse_order := false)
    : IndexMaps := Id.run do
  let mut result := ⟨Array.replicate s1.length none, Array.replicate s2.length none⟩

  let cs1 := s1.toList
  let cs2 := s2.toList

  -- HACK : don't let the ⊢ combine with stuff around it.
  if let ⟨some idx1, some idx2⟩ := (cs1.findIdx? (· = '⊢'), cs2.findIdx? (· = '⊢')) then
    result :=
      ⟨result.s1_to_s2.set! idx1 (some idx2),
       result.s2_to_s1.set! idx2 (some idx1)⟩
    pure ()

  while True do
    let m := get_next_best_match cs1 cs2 result (nonmatchers := nonmatchers)
               (s1_reverse_order := s1_reverse_order)
               (s2_reverse_order := s2_reverse_order)
    if m.length < min_match_len then
      return result
    for kk in [0 : m.length] do
      result :=
        ⟨result.s1_to_s2.set! (m.start_ii + kk) (some (m.start_jj + kk)),
         result.s2_to_s1.set! (m.start_jj + kk) (some (m.start_ii + kk))⟩
    pure ()
  return result

