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
    : BestMatch := Id.run do
  let mut best : BestMatch := ⟨0, 0, 0⟩

  -- HACK
  let s1_hyps_start := get_hyps_start s1
  let s2_hyps_start := get_hyps_start s2

  for ii in [0 : s1.length] do
    for jj in [0 : s2.length] do
      let mut kk := 0
      if s1.get! (ii + kk) ∉ nonmatchers.toList then
      while ii + kk < s1.length && jj + kk < s2.length &&
            s1.get! (ii + kk) = s2.get! (jj + kk) &&
            im.s1_to_s2.get! (ii + kk) = none &&
            im.s2_to_s1.get! (jj + kk) = none do
        kk := kk + 1

      if ii < s1_hyps_start ∧ s2_hyps_start ≤ jj
      then continue

      if s1_hyps_start ≤ ii ∧ jj < s2_hyps_start
      then continue

      if kk > best.length then
        best := ⟨ii, jj, kk⟩
  return best

def do_match (s1 s2 : String) (min_match_len : Nat := 1) (nonmatchers : String := "")
    : IndexMaps := Id.run do
  let mut result := ⟨Array.mkArray s1.length none, Array.mkArray s2.length none⟩

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
    if m.length < min_match_len then
      return result
    for kk in [0 : m.length] do
      result :=
        ⟨result.s1_to_s2.set! (m.start_ii + kk) (some (m.start_jj + kk)),
         result.s2_to_s1.set! (m.start_jj + kk) (some (m.start_ii + kk))⟩
    pure ()
  return result

