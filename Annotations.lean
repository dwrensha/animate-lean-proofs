import Lean

syntax (name := atomicTac) "atomic" "(" tacticSeq ")"  :  tactic

elab_rules : tactic
| `(tactic| atomic( $tac )) => do
  Lean.Elab.Tactic.evalTactic tac


syntax (name := reverseS2Tac) "reverse_s2" "(" tacticSeq ")"  :  tactic

elab_rules : tactic
| `(tactic| reverse_s2( $tac )) => do
  Lean.Elab.Tactic.evalTactic tac

syntax (name := reverseS1Tac) "reverse_s1" "(" tacticSeq ")"  :  tactic

elab_rules : tactic
| `(tactic| reverse_s1( $tac )) => do
  Lean.Elab.Tactic.evalTactic tac

syntax (name := reverseS1S2Tac) "reverse_s1_s2" "(" tacticSeq ")"  :  tactic

elab_rules : tactic
| `(tactic| reverse_s1_s2( $tac )) => do
  Lean.Elab.Tactic.evalTactic tac



--set_option trace.Elab.info true
--example : 1 = 1 := by
--  atomic ( have := True.intro; rfl )

--set_option trace.Elab.info false
