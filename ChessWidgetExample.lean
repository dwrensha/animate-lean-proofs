import Chess
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

def get_pos {p : _root_.Position} {side : Side} (_: ForcedWin side p) : _root_.Position := p

def get_side {p : _root_.Position} {side : Side} (_: ForcedWin side p) : Side := side

#check get_pos Chess.morphy_mates_in_two
#check get_side Chess.morphy_mates_in_two == Side.white

set_option linter.hashCommand false
#widget ChessPositionWidget with { position? := some <| get_pos Chess.morphy_mates_in_two : ChessPositionWidgetProps }

#check ChessPositionWidget

open ProofWidgets Penrose DiagramBuilderM Lean.Server

namespace Chess

private unsafe def evalModuleUnsafe (e : Expr) : MetaM Module :=
  evalExpr' Module ``Module e

@[implemented_by evalModuleUnsafe]
opaque evalModule (e : Expr) : MetaM Module

open scoped Jsx in
/-- The RPC method for displaying FEN for ForcedWin (Side → Position → Prop). -/

@[server_rpc_method]
def forced_win_rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
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
              -- Try to interpret `posExpr` as a `Position`
              let posVal ← unsafe (evalExpr _root_.Position (mkConst ``_root_.Position) posExpr)
              -- Create props for the ChessPositionWidget
              let widgetProps : ChessPositionWidgetProps := { position? := some posVal }
              let board_html := Html.ofComponent ChessPositionWidget widgetProps #[]
              let fen_str := fenFromPosition posVal
              let fen_html := <span>{Html.text fen_str}</span>
              let combined_html := Html.element "div" #[] #[board_html, fen_html]
              return some <| combined_html
            return none)
    match html with
    | none => return <span>No ForcedWin goal found or invalid type.</span>
    | some inner => return inner

end Chess

@[widget_module]
def ForcedWinWidget :  Component PanelWidgetProps  :=
    mk_rpc_widget% Chess.forced_win_rpc
syntax (name := forcedWinWidget) "#forced_win_widget " term : command
open Command

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

#widget ChessPositionWidget with { position? := get_pos Chess.morphy_mates_in_two : ChessPositionWidgetProps }
