import Chess.Basic

section tactics

open Lean.Meta Lean.Elab.Tactic

syntax "move " term : tactic

elab_rules : tactic | `(tactic| move $t:term) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedWin _) side) pos := goal_type
    | throwError "'move' tactic expects ForcedWin goal"
  -- TODO throw error if side does not equal pos.turn
  let t ← Lean.Elab.Term.elabTerm t none
  let cm ← whnf (← mkAppM ``ChessMove.ofString #[t])
  let .app (.app (.const ``Option.some _) _) cm := cm
    | throwError "failed to parse move"

  let pos1 ← whnf (← mkAppM ``make_move #[pos, cm])
  let .app (.app (.const ``Option.some _) _) pos1 := pos1
    | throwError "failed to make move"
  let pos1 ← whnf pos1

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let mv_stx ← Lean.Elab.Term.exprToSyntax cm
  let pos1_stx ← Lean.Elab.Term.exprToSyntax pos1
  evalTactic (← `(tactic| refine ForcedWin.Self $pos_stx $mv_stx $pos1_stx (by decide) ?_))
  evalTactic (← `(tactic| dsimp [game_start, Side.other, Position.set]))

syntax "opponent_move" : tactic

elab_rules : tactic | `(tactic| opponent_move) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedWin _) side) pos := goal_type
    | throwError "'opponent_move' tactic expects ForcedWin goal"
  -- TODO throw error if side does not equal pos.turn.other

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  evalTactic (← `(tactic| apply ForcedWin.Opponent $pos_stx))
  evalTactic (← `(tactic| rw [←List.forall_iff_forall_mem]))
  evalTactic (← `(tactic| dsimp [do_simple_move, Side.other, Position.set]))
  evalTactic (← `(tactic| try constructorm* (_ ∧ _)))
  for g in (←get).goals do
    g.setUserName .anonymous

syntax "checkmate" : tactic

elab_rules : tactic | `(tactic| checkmate) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedWin _) side) pos := goal_type
    | throwError "'checkmate' tactic expects ForcedWin goal"
  -- TODO throw error if side does not equal pos.turn.other

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  evalTactic (← `(tactic| exact ForcedWin.Checkmate $pos_stx (by decide)))

end tactics
