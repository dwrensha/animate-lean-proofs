import Chess
import ChessWidget
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Presentation.Expr
import ProofWidgets.Component.HtmlDisplay

/-! ## Example use of string diagram widgets -/

open ProofWidgets Lean Meta Elab

#check ForcedWin

theorem Chess.morphy_mates_in_two :
    ForcedWin .white
      ╔════════════════╗
      ║░░▓▓░░▓▓♚]♝]░░♜]║
      ║♟]░░▓▓♞]▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓♛]▓▓░░▓▓║
      ║▓▓░░▓▓░░♟]░░♗]░░║
      ║░░▓▓░░▓▓♙]▓▓░░▓▓║
      ║▓▓♕]▓▓░░▓▓░░▓▓░░║
      ║♙]♙]♙]▓▓░░♙]♙]♙]║
      ║▓▓░░♔}♖]▓▓░░▓▓░░║
      ╚════════════════╝ := by
    move "Qb8"
    opponent_move
    move "Rd8"
    checkmate

#check Chess.morphy_mates_in_two

def get_pos {p : _root_.Position} (_: ForcedWin Side.white p) : _root_.Position := p


#check get_pos Chess.morphy_mates_in_two


set_option linter.hashCommand false
#widget ChessPositionWidget with { pos? := get_pos Chess.morphy_mates_in_two : ChessPositionWidgetProps }

#check ChessPositionWidget

open ProofWidgets Penrose DiagramBuilderM Lean.Server

namespace Chess


open scoped Jsx in
/-- The RPC method for displaying FEN for ForcedWin (Side → Position → Prop). -/
@[server_rpc_method]
def myrpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none  -- No goals, return none
      else
        let some g := props.goals[0]? | unreachable!
        g.ctx.val.runMetaM {} do
          g.mvarId.withContext do
            -- Get the goal's type
            let type ← g.mvarId.getType
            -- Extract the function name and arguments using `getAppFnArgs`
            let (fn, args) := type.getAppFnArgs
            if fn == ``ForcedWin && args.size == 2 then
              -- Extract the `Position` argument
              let posExpr := args[1]!  -- The second argument should be the Position
              -- Try to manually interpret `posExpr` as a `Position` somehow
              let posVal ← evalExpr _root_.Position (mkConst ``_root_.Position) posExpr

              -- Convert the interpreted position to FEN
              let fenStr := fenFromPosition posVal
              return some <span>FEN: {Html.text fenStr}</span>
            return none)
    match html with
    | none => return <span>No ForcedWin goal found or invalid type.</span>
    | some inner => return inner


end Chess

@[widget_module]
def ForcedWinWidget :  Component PanelWidgetProps  :=
    mk_rpc_widget% Chess.myrpc
syntax (name := forcedWinWidget) "#forced_win_widget " term : command
open Command
/-
@[command_elab stringDiagram, inherit_doc stringDiagram]
def elabStringDiagramCmd : CommandElab := fun
  | stx@`(#forced_win_widget $t:term) => do
    let html ← runTermElabM fun _ => do
      let e ← try mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo t)
        catch _ => Term.levelMVarToParam (← instantiateMVars (← Term.elabTerm t none))
      match ← StringDiagram.stringMorOrEqM? e with
      | .some html => return html
      | .none => throwError "could not find a morphism or equality: {e}"
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplay.javascript)
      (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."

#forced_win_widget Chess.morphy_mates_in_two
-/
theorem Chess.morphy_mates_in_two' :
    ForcedWin .white
      ╔════════════════╗
      ║░░▓▓░░▓▓♚]♝]░░♜]║
      ║♟]░░▓▓♞]▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓♛]▓▓░░▓▓║
      ║▓▓░░▓▓░░♟]░░♗]░░║
      ║░░▓▓░░▓▓♙]▓▓░░▓▓║
      ║▓▓♕]▓▓░░▓▓░░▓▓░░║
      ║♙]♙]♙]▓▓░░♙]♙]♙]║
      ║▓▓░░♔}♖]▓▓░░▓▓░░║
      ╚════════════════╝ := by
    with_panel_widgets [ForcedWinWidget]
      move "Qb8"
      opponent_move
      move "Rd8"
      checkmate

#widget ChessPositionWidget with { pos? := get_pos Chess.morphy_mates_in_two : ChessPositionWidgetProps }
