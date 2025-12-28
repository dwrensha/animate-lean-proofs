import Lean
import Std.Internal.Parsec

namespace HighlightSyntax

/-- For each character index in the text, a
    Nat represting the color at that index.
-/
abbrev ColorMap := Array Nat


def cat_to_color : String → Nat
| "Token.Text" => 1
| "Token.Text.Whitespace" => 2
| "Token.Keyword" => 3
| "Token.Name" => 4
| "Token.Name.Builtin.Pseudo" => 5
| "Token.Operator" => 6
| "Token.Literal.Number.Integer" => 7
| _ => 0


section parse

/-
This section is a lightly adapted copy of some stuff from Lean/Data/Json/Parser.lean.
-/

open Lean

namespace Parse

def hexChar : Std.Internal.Parsec.String.Parser Nat := do
  let c ← Std.Internal.Parsec.any
  if '0' ≤ c ∧ c ≤ '9' then
    pure $ c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    pure $ c.val.toNat - 'a'.val.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then
    pure $ c.val.toNat - 'A'.val.toNat + 10
  else
    Std.Internal.Parsec.fail "invalid hex character"

def escapedChar : Std.Internal.Parsec.String.Parser Char := do
  let c ← Std.Internal.Parsec.any
  match c with
  | '\\' => return '\\'
  | '"'  => return '"'
  | '/'  => return '/'
  | 'b'  => return '\x08'
  | 'f'  => return '\x0c'
  | 'n'  => return '\n'
  | 'r'  => return '\x0d'
  | 't'  => return '\t'
  | 'u'  =>
    let u1 ← hexChar; let u2 ← hexChar; let u3 ← hexChar; let u4 ← hexChar
    return Char.ofNat $ 4096*u1 + 256*u2 + 16*u3 + u4
  | 'x'  =>
    let b1 ← hexChar; let b2 ← hexChar
    return Char.ofNat $ 16*b1 + b2

  | _ => Std.Internal.Parsec.fail "illegal \\u escape"

partial def strCore (acc : String) : Std.Internal.Parsec.String.Parser String := do
  let c ← Std.Internal.Parsec.peek!
  if c = '"' then -- "
    Std.Internal.Parsec.skip
    return acc
  else
    let c ← Std.Internal.Parsec.any
    if c = '\\' then
      strCore (acc.push (← escapedChar))
    -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
    -- the JSON standard is not definite: both directly printing the character
    -- and encoding it with multiple \u is allowed. we choose the former.
    else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
      strCore (acc.push c)
    else
      Std.Internal.Parsec.fail "unexpected character in string"

def str : Std.Internal.Parsec.String.Parser String := strCore ""

end Parse
end parse

def assign_colors (s : String) : IO ColorMap := do
  -- TODO randomize? or use stdio
  let filename := "/tmp/animate-lean.txt"

  IO.FS.writeFile filename s
  let child ← IO.Process.spawn {
    cmd := "pygmentize"
    args := #["-l", "lean4", "-f", "raw", filename]
    stdout := .piped
  }

  let output ← child.stdout.readToEnd
  let exitCode ← child.wait
  if exitCode != 0
  then throw (IO.userError "pygmentize failed")

  let mut result := #[]
  let mut idx := 0
  for line in output.splitToList (· = '\n') do
    if line = "" then continue
    let [cat, val] := line.splitToList (· = '\t') |
      throw (IO.userError s!"bad pygmentize output: {line}")
    let val' := (val.drop 1).dropRight 1 ++ "\""
    match Std.Internal.Parsec.String.Parser.run Parse.str val' with
    | .ok v =>
      for _c in v.toList do
        result := result.push (cat_to_color cat)
        idx := idx + 1

    | .error err  =>
      throw (IO.userError s!"failed to parse string {val}: {err}")

  let _ := s.length
  --dbg_trace "lengths : {s.length} vs {result.size}"

  --dbg_trace result
  return result
