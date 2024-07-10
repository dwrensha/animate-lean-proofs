namespace HighlightSyntax

/-- For each character index in the text, a
    Nat represting the color at that index.
-/
abbrev ColorMap := Array Nat


def assign_colors (s : String) : IO ColorMap := do
  -- TODO randomize? or use stdio
  let filename := "/tmp/animate-lean.txt"

  IO.FS.writeFile filename s
  let child ← IO.Process.spawn {
    cmd := "pygmentize"
    args := #["-l", "lean4", "-f", "raw", filename]
    stdout := .piped
  }

  let x ← child.stdout.readToEnd
  dbg_trace "{x}"
  let exitCode ← child.wait

  dbg_trace "exit code {exitCode}"

  pure #[]
