import Lean
import Lean.Data.Json.FromToJson

import Batteries.Data.RBMap.Basic
import Mathlib.Data.String.Defs

import Annotations
import HighlightSyntax
import StringMatching

namespace Animate

--- animate.lean command line arguments
structure Config where
  file_path : System.FilePath := "."
  const_name : Lean.Name := `Unknown
  print_infotree : Bool := false
  min_match_len : Nat := 2
  nonmatchers : String := ""

def parseArgs (args : Array String) : IO Config := do
  if args.size < 2 then
    throw <| IO.userError "usage: animate FILE_PATH CONST_NAME"
  let mut cfg : Config := {}
  cfg := { cfg with file_path := ⟨args[0]!⟩ }
  cfg := { cfg with const_name := args[1]!.toName }
  let mut idx := 2
  while idx < args.size do
    match args[idx]! with
    | "--print-infotree" =>
       cfg := {cfg with print_infotree := true}
    | "--min-match-len" =>
       idx := idx + 1
       let x := args[idx]!.toNat!
       cfg := {cfg with min_match_len := x}
    | "--nonmatchers" =>
       idx := idx + 1
       let x := args[idx]!
       cfg := {cfg with nonmatchers := x}
    | s => throw <| IO.userError s!"unknown argument {s}"
    idx := idx + 1

  return cfg

--------------------------------------------------

-- json that we send to animate.py for blender rendering

structure Goal where
  --- MVarId
  goalId : String
  state : String
deriving Lean.ToJson, Lean.FromJson, BEq

------------------

-- intermediate representation
-- stage 1: tree of tactic sequences

instance : Lean.ToJson String.Pos.Raw where
  toJson := fun p ↦ Lean.Json.num p.byteIdx

instance : Lean.FromJson String.Pos.Raw where
    fromJson? := fun j ↦ do
  let idx ← j.getNat?
  return ⟨idx⟩

structure StringSpan where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
deriving Lean.ToJson, Lean.FromJson, BEq

structure TacticStepData where
  name : String
  goals_before : List Goal
deriving Lean.ToJson, Lean.FromJson

inductive TacticStep where
| node (data : TacticStepData)
       (children : List TacticStep)
deriving Lean.ToJson, Lean.FromJson

def TacticStep.goals_before : TacticStep →  List Goal
| .node data _ => data.goals_before

section syntax_manip

open Lean

def StringSpan.ofSyntax (stx : Syntax) : Option StringSpan := Id.run do
  let some p1 := stx.getPos? | return none
  let some p2 := stx.getTailPos? | return none
  return .some ⟨p1, p2⟩

def replace_inner_syntax (src : String) (outer : StringSpan) (inners : List StringSpan)
    (replacement : String := "?_") :
    String := Id.run do
  let mut result := ""
  let mut curPos := outer.startPos
  for inner in inners do
    result := result ++
      (Substring.mk src curPos inner.startPos).toString ++ replacement
    curPos := inner.endPos
  result := result ++ (Substring.mk src curPos outer.endPos).toString
  return result

--#eval replace_inner_syntax
--       "have h := by rfl" ⟨⟨0⟩, ⟨17⟩⟩ [⟨⟨13⟩, ⟨17⟩⟩]

def left_trim_lines (lines : String) (col : Nat) : String := Id.run do
  let mut lines := lines.splitOn "\n"
  let mut rev_result := []
  for line in lines do
    let pfx := Substring.mk line ⟨0⟩ ⟨col⟩
    if pfx.toString = String.replicate col ' '
    then rev_result := line.drop col :: rev_result
    else rev_result := line :: rev_result
  return String.intercalate "\n" rev_result.reverse

-- #eval left_trim_lines "a\n  bc\n   d" 2

def StringSpan.union (s1 s2 : StringSpan) : StringSpan :=
  { startPos := ⟨min s1.startPos.byteIdx s2.startPos.byteIdx⟩,
    endPos := ⟨max s1.endPos.byteIdx s2.endPos.byteIdx⟩,
  }

def EMPTY_SPAN : StringSpan := {startPos := ⟨0xffffffffffffffff⟩, endPos := ⟨0⟩}

def StringSpan.union_list : List StringSpan → StringSpan
| [] => EMPTY_SPAN
| s :: ss => s.union (StringSpan.union_list ss)

end syntax_manip

section infotrees

open Lean Elab

def collectNodesBottomUpM {α : Type} {m : Type → Type} [Monad m]
    (p : ContextInfo → Info → PersistentArray InfoTree → List α → m (List α))
    (i : InfoTree) : m (List α) := do
  let x ← i.visitM
   (m := m)
   (postNode := fun ci i cs as => p ci i cs (as.filterMap id).flatten)
  let y := x.getD []
  return y

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def _root_.Lean.Elab.TacticInfo.name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

def GOAL_PP_WIDTH : Nat := 80

unsafe def visitTacticInfo (ci : ContextInfo) (ti : TacticInfo)
    (acc : List TacticStep) : IO (List TacticStep) := do
  let stx := ti.stx

  let mut goals_before := []
  for g in ti.goalsBefore do
    let doprint : MetaM _ := Meta.ppGoal g
    let cm := doprint.run' (s := { mctx := ti.mctxBefore })
    let fm ← ci.runCoreM cm
    goals_before := goals_before ++ [⟨g.name.toString, fm.pretty (width := GOAL_PP_WIDTH)⟩]

    let _x := ti.mctxAfter.getExprAssignmentCore? g
    -- collect all fvars that appear in x ...
    --
    --dbg_trace x

  let mut goals_after := []
  for g in ti.goalsAfter do
    let doprint : MetaM _ := Meta.ppGoal g
    let cm := doprint.run' (s := { mctx := ti.mctxAfter })
    let fm ← ci.runCoreM cm
    goals_after := goals_after ++ [⟨g.name.toString, fm.pretty (width := GOAL_PP_WIDTH)⟩]

  if let some ``Lean.Parser.Tactic.tacticSeq1Indented := ti.name?
  then
    if acc.length > 0 then
    return acc

  if let .atom _ "by" := ti.stx then
    return acc.foldr (fun node prev =>
      match node with
      | .node data _ =>
        [TacticStep.node data prev]
    ) []

  match stx.getHeadInfo? with
  | .some (.synthetic ..) =>
    -- Not actual concrete syntax the user wrote. Ignore.
    return acc
  | _ => pure ()

  -- Tactic step is a no-op. Ignore it.
  if goals_before == goals_after then return acc

  let .some name := ti.name? | return acc
  match name with
  | `null => return acc
--  | ``Lean.Parser.Term.byTactic =>
--      return [TacticStep.seq ⟨span, goals_before, goals_after⟩ acc]
  | ``cdotTk => return acc
  | ``atomicTac =>
     if let .node _ ``atomicTac #[_, _, _, _] := ti.stx then
       let d := { name := name.toString
                  goals_before}
       return [TacticStep.node d []]
     else
       panic! "bad atomic syntax"
  | ``reverseS2Tac =>
     if let .node _ ``reverseS2Tac #[_, _, _, _] := ti.stx then
       let d := { name := name.toString
                  goals_before}
       return [TacticStep.node d []]
     else
       panic! "bad reverse_s2 syntax"

  | ``reverseS1S2Tac =>
     if let .node _ ``reverseS1S2Tac #[_, _, _, _] := ti.stx then
       let d := { name := name.toString
                  goals_before}
       return [TacticStep.node d []]
     else
       panic! "bad reverse_s1_s2 syntax"


  | ``reverseS1Tac =>
     if let .node _ ``reverseS1Tac #[_, _, _, _] := ti.stx then
       let d := { name := name.toString
                  goals_before}
       return [TacticStep.node d []]
     else
       panic! "bad reverse_s1 syntax"


  | ``Lean.Parser.Tactic.inductionAlt =>
    -- induction alternative. We want the direct children
    -- of `induction` to be `seq` nodes, so we collapse these.
    return acc
  | ``Lean.Parser.Tactic.tacticSeq =>
    -- let's just get rid of these; I don't think they're that important
    return acc
  | ``Lean.cdot =>
    -- bullet points don't need to be in the output
    return acc
  | _ => pure ()

  let d := { name := name.toString
             goals_before}
  return [TacticStep.node d acc]

unsafe def visitNode (ci : ContextInfo) (info : Info)
    (_children : PersistentArray InfoTree)
    (acc : List TacticStep) : IO (List TacticStep) :=
  match info with
  | .ofTacticInfo ti => visitTacticInfo ci ti acc
  | _ => pure acc

unsafe def extractToplevelStep (tree : InfoTree) : IO TacticStep := do
  let steps ← collectNodesBottomUpM (m := IO) visitNode tree
  let [step] := steps | throw <| IO.userError "got more than one toplevel step"
  return step


unsafe def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  let done ← Lean.Elab.Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  let env' := st.commandState.env

  -- clear the infostate
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env', infoState)]
  else
    return (env', infoState) :: (←processCommands)

unsafe def processFile (config : Config) : IO Unit := do
  initSearchPath (← findSysroot)
  let mut input ← IO.FS.readFile config.file_path
  Lean.enableInitializersExecution
  let inputCtx := Lean.Parser.mkInputContext input config.file_path.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw <| IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← Lean.moduleNameOfFileName config.file_path none)

  if env.contains config.const_name then
    throw <| IO.userError s!"constant of name {config.const_name} is already in environment"

  let commandState := { Lean.Elab.Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  -----
  for ⟨env, s⟩ in steps do
    if env.contains config.const_name then
      for tree in s.trees do
        if config.print_infotree then
           IO.println (Format.pretty (←tree.format))
        let step ← extractToplevelStep tree
        IO.println ((Lean.toJson step).pretty (lineWidth := 200))
      -- we're done
      return ()

  throw <| IO.userError s!"no constant of name {config.const_name} was found"

end infotrees

end Animate

unsafe def main (args : List String) : IO Unit := do
  let cfg ← Animate.parseArgs args.toArray

  Animate.processFile cfg
