import Lean

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
  for line in output.split (· = '\n') do
    if line = "" then continue
    let [cat, val] := line.split (· = '\t') |
      throw (IO.userError s!"bad pygmentize output: {line}")
    let val := (val.drop 1).dropRight 1 ++ "\""
    match Lean.Json.Parser.str val.mkIterator with
    | Lean.Parsec.ParseResult.success _ v =>
      for _c in v.toList do
        result := result.push (cat_to_color cat)
        idx := idx + 1

    | Lean.Parsec.ParseResult.error _ err  =>
      throw (IO.userError s!"failed to parse string: {err}")

  let _ := s.length
  --dbg_trace "lengths : {s.length} vs {result.size}"

  --dbg_trace result
  return result
