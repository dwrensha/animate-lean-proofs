import Lean
import Lean.Elab.Tactic.Induction
import Mathlib.Tactic

namespace NNG

section tactics

-- make `rw` mean `rewrite`, so that it does not autmatically close goals with `rfl`.
macro (name := rwSeq) "rw " c:Lean.Parser.Tactic.optConfig s:Lean.Parser.Tactic.rwRuleSeq l:(Lean.Parser.Tactic.location)? : tactic => do
    `(tactic| (rewrite $c $s:rwRuleSeq $(l)?))

open Lean Meta Elab Elab.Tactic

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "unknown alternative name '{altName}'"

def ElimApp.evalNames (elimInfo : ElimInfo) (alts : Array ElimApp.Alt) (withArg : Syntax)
    (numEqs := 0) (generalized : Array FVarId := #[]) (toClear : Array FVarId := #[])
    (toTag : Array (Ident × FVarId) := #[]) :
    TermElabM (Array MVarId) := do
  let mut names : List Syntax := withArg[1].getArgs |>.toList
  let mut subgoals := #[]
  for { name := altName, mvarId := g, .. } in alts do
    let numFields ← getAltNumFields elimInfo altName
    let (altVarNames, names') := names.splitAtD numFields (Unhygienic.run `(_))
    names := names'
    let (fvars, g) ← g.introN numFields <| altVarNames.map (getNameOfIdent' ·[0])
    let some (g, subst) ← Cases.unifyEqs? numEqs g {} | pure ()
    let (introduced, g) ← g.introNP generalized.size
    let subst := (generalized.zip introduced).foldl (init := subst) fun subst (a, b) =>
      subst.insert a (.fvar b)
    let g ← liftM $ toClear.foldlM (·.tryClear) g
    g.withContext do
      for (stx, fvar) in toTag do
        Term.addLocalVarInfo stx (subst.get fvar)
      for fvar in fvars, stx in altVarNames do
        (subst.get fvar).addLocalVarInfoForBinderIdent ⟨stx⟩
    subgoals := subgoals.push g
  pure subgoals

open private getElimNameInfo generalizeTargets generalizeVars from Lean.Elab.Tactic.Induction
elab (name := induction'') "induction " tgts:(Parser.Tactic.casesTarget,+)
    usingArg:((" using " ident)?)
    withArg:((" with" (ppSpace colGt binderIdent)+)?)
    genArg:((" generalizing" (ppSpace colGt ident)+)?) : tactic => do
  let (targets, toTag) ← elabCasesTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := true)
    let targets ← addImplicitTargets elimInfo targets
    evalInduction.checkTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    g.withContext do
      let genArgs ← if genArg.1.isNone then pure #[] else getFVarIds genArg.1[1].getArgs
      let forbidden ← mkGeneralizationForbiddenSet targets
      let mut s ← getFVarSetToGeneralize targets forbidden
      for v in genArgs do
        if forbidden.contains v then
          throwError "variable cannot be generalized \
            because target depends on it{indentExpr (mkFVar v)}"
        if s.contains v then
          throwError "unnecessary 'generalizing' argument, \
            variable '{mkFVar v}' is generalized automatically"
        s := s.insert v
      let (fvarIds, g) ← g.revert (← sortFVarIds s.toArray)
      g.withContext do
        let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
        let elimArgs := result.elimApp.getAppArgs
        ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! targetFVarIds
        g.assign result.elimApp
        let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
          (generalized := fvarIds) (toClear := targetFVarIds) (toTag := toTag)
        setGoals <| (subgoals ++ result.others).toList ++ gs


end tactics

section power

-- level 7
theorem mul_pow
    (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with t Ht
  · rw [pow_zero]
    rw [pow_zero]
    rw [pow_zero]
    rw [mul_one]
    rfl
  · rw [pow_succ]
    rw [pow_succ]
    rw [pow_succ]
    rw [Ht]
    simp only [mul_assoc]
    rw [mul_comm a (_ * b)]
    rw [mul_assoc]
    rw [mul_comm b a]
    rfl

-- level 9
theorem add_sq
    (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [pow_two]
  rw [pow_two]
  rw [pow_two]
  rw [add_right_comm]
  rw [mul_add]
  rw [add_mul]
  rw [add_mul]
  rw [two_mul]
  rw [add_mul]
  rw [mul_comm b a]
  rw [← add_assoc]
  rw [← add_assoc]
  rfl

end power
