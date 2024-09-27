import Lean
import Chess.Widgets

open Lean Meta Elab Tactic Chess

/-- Calls an external Python script and retrieves its output. -/
def callNextMoveScript (input : String): IO String := do
  let path := ("./scripts/get_next_move.py" : System.FilePath)
  unless ← path.pathExists do
    throw <| IO.userError s!"Python script '{path}' not found."
  let out ← IO.Process.output { cmd := "python3", args := #[path.toString, input] }
  if out.exitCode != 0 then
    throw <| IO.userError s!"Script '{path}' exited with code {out.exitCode}:\n{out.stderr}"
  return "move \"" ++ out.stdout.trim ++ "\""

/-- A tactic that runs a Python script and uses its output as a Lean tactic.
    Right now, this only works if `stockfish` is installed in your system.
    If not, consider running
    ```
    sudo apt install stockfish
    ```
    -/
elab "guess_next_move" : tactic => do
  -- Get the current goal
  let goal ← getMainGoal
  -- Extract the position from a `ForcedWin` goal
  let posOpt ← extractPositionFromForcedWinGoal goal
  match posOpt with
  | some posVal =>
    -- Convert the position to a FEN string
    let fenStr := fenFromPosition posVal
    -- Pass the FEN string to the Python script
    let nextMove ← liftM <| callNextMoveScript fenStr

    -- Log the output for debugging
    -- logInfo s!"Python script output: {nextMove}"

    -- Interpret the Python output as Lean syntax and apply it
    let env ← getEnv
    match Parser.runParserCategory env `tactic nextMove with
    | Except.error errMsg => throwError s!"Failed to parse tactic from Python script: {errMsg}"
    | Except.ok stx => do
      -- Add the suggestion to the tactic
      Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) nextMove

      -- Execute the parsed tactic
      evalTactic stx
  | none => throwError "No ForcedWin goal found or invalid goal type."
