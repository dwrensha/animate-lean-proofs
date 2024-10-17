import Lean
import Lean.Data.Json.FromToJson
import Mathlib.Tactic

import Annotations
import HighlightSyntax
import StringMatching

namespace Animate

--- animate.lean command line arguments
structure Config where
  file_path : System.FilePath := "."
  const_name : Lean.Name := `Unknown
  print_infotree : Bool := false
  print_stage1 : Bool := false
  print_stage2 : Bool := false
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
    | "--print-stage1" =>
       cfg := {cfg with print_stage1 := true}
    | "--print-stage2" =>
       cfg := {cfg with print_stage2 := true}
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

structure TransformedGoal where
  goal : Goal
  indexMaps : IndexMaps
deriving Lean.ToJson, Lean.FromJson

structure GoalAction where
  --- MVarId from before the tactic is applied.
  startGoalId : String

  --- Pretty-printed goal state before the tactic is applied.
  startState : String

  -- empty means the goal has been closed.
  results : List TransformedGoal
deriving Lean.ToJson, Lean.FromJson

--- Application of a single tactic.
--- It may act on multiple goals (e.g. when using the <;> combinator).
structure Action where
  tacticText : String
  goalActions : List GoalAction
deriving Lean.ToJson, Lean.FromJson

structure GoalHighlighting where
  goalId : String
  colors : HighlightSyntax.ColorMap
deriving Lean.ToJson, Lean.FromJson

-- Result of stage 3.
-- To be jsonified and consumed by animate.py in Blender
structure Movie where
  theoremName : String
  startGoal : Goal
  actions: List Action
  highlighting: Array GoalHighlighting
deriving Lean.ToJson, Lean.FromJson

------------------

-- intermediate representation
-- stage 1: tree of tactic sequences

instance : Lean.ToJson String.Pos where
  toJson := fun p ↦ Lean.Json.num p.byteIdx

instance : Lean.FromJson String.Pos where
    fromJson? := fun j ↦ do
  let idx ← j.getNat?
  return ⟨idx⟩

structure StringSpan where
  startPos : String.Pos
  endPos : String.Pos
deriving Lean.ToJson, Lean.FromJson, BEq

structure TacticStepData where
  elaborator : String
  name : String

  --- The text of the tactic, with any child tactic
  --- text replaced by "_?"
  text : String

  tacticSpan : StringSpan
  goals_before : List Goal
  goals_after : List Goal
  reverse_s1 : Bool := false
  reverse_s2 : Bool := false
deriving Lean.ToJson, Lean.FromJson

structure SeqData where
  tacticSpan : StringSpan
  goals_before : List Goal
  goals_after : List Goal
deriving Lean.ToJson, Lean.FromJson

inductive TacticStep where
| node (data : TacticStepData)
       (children : List TacticStep)
| seq (span: StringSpan) (children : List TacticStep)
deriving Lean.ToJson, Lean.FromJson

def TacticStep.goals_before : TacticStep →  List Goal
| .node data _ => data.goals_before
| .seq _ [] => []
| .seq _ (c::_) => c.goals_before

--------------------
-- stage 2: flattened map of tactic steps.

structure TacticStep' where
  text : String
  span : StringSpan
  goal_before : Goal
  goals_after : List Goal -- include children
  reverse_s1 : Bool := false
  reverse_s2 : Bool := false
deriving Lean.ToJson, Lean.FromJson

/-- map from goalId to tactic step that consumes that goal.
    That should be the latest, most specific step
    that lists the goal in its before state but not in its after state.
-/
abbrev StepMap := Std.HashMap String TacticStep'

structure Stage2State where
  startGoal : Goal
  steps : StepMap

def Stage2State.dump (s : Stage2State) : IO Unit := do
  IO.println <| "stage2 with top goal " ++ s.startGoal.goalId
  for ⟨_, ts⟩ in s.steps.toList do
    IO.println <| s!"{Lean.ToJson.toJson ts}"
  -- TODO

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

unsafe def TacticStep.span_union : TacticStep → StringSpan
| .node data children =>
     let children_spans := children.map (fun c ↦ c.span_union)
     data.tacticSpan.union (StringSpan.union_list children_spans)
| .seq span children =>
     span.union (StringSpan.union_list (children.map (fun c ↦ c.span_union)))


end syntax_manip

section infotrees

open Lean Elab

def collectNodesBottomUpM {α : Type} {m : Type → Type} [Monad m]
    (p : ContextInfo → Info → PersistentArray InfoTree → List α → m (List α))
    (i : InfoTree) : m (List α) := do
  let x ← i.visitM
   (m := m)
   (postNode := fun ci i cs as => p ci i cs (as.filterMap id).join)
  let y := x.getD []
  return y

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def _root_.Lean.Elab.TacticInfo.name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

def GOAL_PP_WIDTH : Nat := 80

unsafe def visitTacticInfo (ci : ContextInfo) (ti : TacticInfo)
    (_children : PersistentArray InfoTree)
    (acc : List TacticStep) : IO (List TacticStep) := do
  let src := ci.fileMap.source
  let stx := ti.stx

  let .some startPos := stx.getPos? | return acc
  let startPosition := ci.fileMap.toPosition startPos
  let .some span := StringSpan.ofSyntax stx | return acc

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
    return [TacticStep.seq EMPTY_SPAN acc]

  if let .atom _ "by" := ti.stx then
    if acc.length > 0 then
      return [TacticStep.seq span acc]
    else return acc

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
     if let .node _ ``atomicTac #[_, _, inner, _] := ti.stx then
       let .some span' := StringSpan.ofSyntax inner | panic! "bad atomic span"
       let .some startPos := inner.getPos? | panic! "bad inner span"
       let startPosition := ci.fileMap.toPosition startPos
       let text := replace_inner_syntax src span' []
       let text := left_trim_lines text startPosition.column

       let d := { elaborator := ti.elaborator.toString
                  name := name.toString
                  tacticSpan := span'
                  text
                  goals_before, goals_after }
       return [TacticStep.node d []]
     else
       panic! "bad atomic syntax"
  | ``reverseS2Tac =>
     if let .node _ ``reverseS2Tac #[_, _, inner, _] := ti.stx then
       let .some span' := StringSpan.ofSyntax inner | panic! "bad reverse_s2 span"
       let .some startPos := inner.getPos? | panic! "bad inner span"
       let startPosition := ci.fileMap.toPosition startPos
       let text := replace_inner_syntax src span' []
       let text := left_trim_lines text startPosition.column

       let d := { elaborator := ti.elaborator.toString
                  name := name.toString
                  tacticSpan := span'
                  text
                  reverse_s2 := true
                  goals_before, goals_after }
       return [TacticStep.node d []]
     else
       panic! "bad reverse_s2 syntax"

  | ``reverseS1S2Tac =>
     if let .node _ ``reverseS1S2Tac #[_, _, inner, _] := ti.stx then
       let .some span' := StringSpan.ofSyntax inner | panic! "bad reverse_s1_s2 span"
       let .some startPos := inner.getPos? | panic! "bad inner span"
       let startPosition := ci.fileMap.toPosition startPos
       let text := replace_inner_syntax src span' []
       let text := left_trim_lines text startPosition.column

       let d := { elaborator := ti.elaborator.toString
                  name := name.toString
                  tacticSpan := span'
                  text
                  reverse_s1 := true
                  reverse_s2 := true
                  goals_before, goals_after }
       return [TacticStep.node d []]
     else
       panic! "bad reverse_s1_s2 syntax"


  | ``reverseS1Tac =>
     if let .node _ ``reverseS1Tac #[_, _, inner, _] := ti.stx then
       let .some span' := StringSpan.ofSyntax inner | panic! "bad reverse_s1 span"
       let .some startPos := inner.getPos? | panic! "bad inner span"
       let startPosition := ci.fileMap.toPosition startPos
       let text := replace_inner_syntax src span' []
       let text := left_trim_lines text startPosition.column

       let d := { elaborator := ti.elaborator.toString
                  name := name.toString
                  tacticSpan := span'
                  text
                  reverse_s1 := true
                  goals_before, goals_after }
       return [TacticStep.node d []]
     else
       panic! "bad reverse_s1 syntax"


  | ``Lean.Parser.Tactic.inductionAlt =>
    -- induction alternative. We want the direct children
    -- of `induction` to be `seq` nodes, so we collapse these.
    return acc
  | _ => pure ()

  let mut inners := []
  for c in acc do
    inners := inners ++ [c.span_union]

  let text := replace_inner_syntax src span inners
  let text := left_trim_lines text startPosition.column

  let d := { elaborator := ti.elaborator.toString
             name := name.toString
             tacticSpan := span
             text
             goals_before, goals_after }
  return [TacticStep.node d acc]

unsafe def visitNode (ci : ContextInfo) (info : Info)
    (children : PersistentArray InfoTree)
    (acc : List TacticStep) : IO (List TacticStep) :=
  match info with
  | .ofTacticInfo ti => visitTacticInfo ci ti children acc
  | _ => pure acc

unsafe def extractToplevelStep (tree : InfoTree) : IO TacticStep := do
  let steps ← collectNodesBottomUpM (m := IO) visitNode tree
  let [step] := steps | throw <| IO.userError "got more than one toplevel step"
  return step

partial def stage2_aux (step : TacticStep) : StateM StepMap Unit := match step with
| .node data children => do
  if let [goal] := data.goals_before then
    let sm ← get
    let goalId := goal.goalId
    let span := data.tacticSpan
    -- goals after includes stuff from the children in addition to data.goals_after.
    let mut goals_after := []
    for child in children do
      for g in child.goals_before do
        goals_after := g :: goals_after
    for g in data.goals_after do
       goals_after := g :: goals_after
    let ts' := { span,
                 goal_before := goal,
                 goals_after := goals_after.reverse,
                 text := data.text,
                 reverse_s1 := data.reverse_s1
                 reverse_s2 := data.reverse_s2 }
    set (sm.insert goalId ts')
  for child in children do
    stage2_aux child
| .seq _ children => do
  for child in children do
    stage2_aux child

partial def stage2 (step : TacticStep) : IO Stage2State := do
  let ⟨_, m⟩ := StateT.run (stage2_aux step) default
  let [top_goal] := step.goals_before |
         throw <| IO.userError "got more than one toplevel step"
  return { startGoal := top_goal, steps := m }


def stage3_inner (config : Config) (step : TacticStep') : GoalAction := Id.run do
    let mut ts_rev : List TransformedGoal := []
    for g in step.goals_after do
      let im := Animate.do_match step.goal_before.state g.state
                                 (min_match_len := config.min_match_len)
                                 (nonmatchers := config.nonmatchers)
                                 (s1_reverse_order := step.reverse_s1)
                                 (s2_reverse_order := step.reverse_s2)
      ts_rev := {goal := g, indexMaps := im} :: ts_rev
    let ga : GoalAction := {
      startGoalId := step.goal_before.goalId
      startState := step.goal_before.state
      results := ts_rev.reverse
    }
    return ga

partial def stage3 (config : Config) (state2 : Stage2State) : IO Movie := do
  let mut rev_actions := []
  let mut visited := Batteries.mkRBSet String Ord.compare
  let mut colorings := #[]
  let mut currentGoals := [state2.startGoal.goalId]
  while currentGoals.length > 0 do
    let currentGoal :: rest := currentGoals | panic "impossible"
    if visited.contains currentGoal then panic s!"re-visited goal {currentGoal}"
    visited := visited.insert currentGoal
    let .some step :=
      state2.steps.get? currentGoal | panic s!"goal not found {currentGoal}"
    colorings := colorings.push ⟨currentGoal, ← HighlightSyntax.assign_colors step.goal_before.state⟩
    let mut goal_actions := [stage3_inner config step]
    currentGoals := []
    for gid in rest do
      let .some other_step :=
        state2.steps.get? gid | panic s!"goal not found {gid}"
      if other_step.span == step.span
      then
        colorings := colorings.push ⟨gid, ← HighlightSyntax.assign_colors other_step.goal_before.state⟩
        goal_actions := stage3_inner config other_step :: goal_actions
        currentGoals := currentGoals ++ (other_step.goals_after.map (·.goalId))
      else
        currentGoals := currentGoals ++ [gid]

    rev_actions := { tacticText := step.text, goalActions := goal_actions } :: rev_actions
    currentGoals := (step.goals_after.map (·.goalId)) ++ currentGoals
    pure ()
  -- TODO: verify that everything in state2 was visited.
  return { theoremName := config.const_name.toString
           actions := rev_actions.reverse
           startGoal := state2.startGoal,
           highlighting := colorings}

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
  Lean.searchPathRef.set compile_time_search_path%
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
        if config.print_stage1 then
          IO.println s!"{ToJson.toJson step}"
        let stage2state ← stage2 step
        if config.print_stage1 then
          IO.println "STAGE 2:"
          stage2state.dump
        let stage3 ← stage3 config stage2state
        IO.println <| (Lean.toJson stage3).pretty (lineWidth := 200)
      -- we're done
      return ()

  throw <| IO.userError s!"no constant of name {config.const_name} was found"

end infotrees

end Animate

unsafe def main (args : List String) : IO Unit := do
  let cfg ← Animate.parseArgs args.toArray

  Animate.processFile cfg
