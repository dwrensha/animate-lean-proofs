import Chess.Basic
import Chess.Fen
import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.Panel.Basic

/-! ## Example use of string diagram widgets -/


structure ChessPositionWidgetProps where
  position? : Option Position := none
  deriving Lean.Server.RpcEncodable

open ProofWidgets

@[widget]
def ChessPositionWidget : Component ChessPositionWidgetProps where
  javascript := "
import * as React from 'react';
// Mapping of piece names to symbols
const pieceSymbols = {
  'pawn': '♟',
  'rook': '♜',
  'knight': '♞',
  'bishop': '♝',
  'queen': '♛',
  'king': '♚'
};

// Helper function to determine the square color
function getSquareColor(row, col) {
  return (row + col) % 2 === 0 ? '#b58863' : '#f0d9b5';
}

// Chessboard component with inline styles
export default function ChessPositionWidget(props) {
  const emptyBoard = Array(8).fill(Array(8).fill(null));

  const { turn = 'nobody', squares = emptyBoard } = props.position || {};

  const chessBoardStyle = {
    display: 'flex',
    flexDirection: 'column',
  };

  const chessRowStyle = {
    display: 'flex',
  };

  const chessSquareStyle = {
    width: '40px',
    height: '40px',
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'center',
  };

  const chessPieceStyle = (color) => ({
    fontSize: '40px',
    color: color === 'white' ? '#fff' : '#000',
  });

  const rows = squares.map((row, rowIndex) => {
    const columns = row.map((square, colIndex) => {
      const squareColor = getSquareColor(rowIndex, colIndex);
      const piece = square ? pieceSymbols[square[0]] : null;
      const pieceColor = square ? square[1] : null;

      return React.createElement(
        'div',
        {
          key: `${rowIndex}-${colIndex}`,
          style: { ...chessSquareStyle, backgroundColor: squareColor },
        },
        React.createElement(
          'span',
          { style: chessPieceStyle(pieceColor) },
          piece
        )
      );
    });

    return React.createElement(
      'div',
      { key: `row-${rowIndex}`, style: chessRowStyle },
      columns
    );
  });

  return React.createElement(
    'div',
    {},
    React.createElement('h3', {}, `Turn: ${turn}`),
    React.createElement('div', { style: chessBoardStyle }, rows)
  );
}
"


open Lean Meta Elab

def get_pos {p : _root_.Position} {side : Side} (_: ForcedWin side p) : _root_.Position := p

def get_side {p : _root_.Position} {side : Side} (_: ForcedWin side p) : Side := side

open ProofWidgets Penrose DiagramBuilderM Lean.Server

namespace Chess

private unsafe def evalModuleUnsafe (e : Expr) : MetaM Module :=
  evalExpr' Module ``Module e

@[implemented_by evalModuleUnsafe]
opaque evalModule (e : Expr) : MetaM Module


/-- Extracts the position from a goal of type `ForcedWin`. -/
def extractPositionFromForcedWinGoal (g : MVarId) : MetaM (Option _root_.Position) := do
  g.withContext do
    -- Get the goal's type
    let type ← g.getType
    -- Extract the function name and arguments using `getAppFnArgs`
    let (fn, args) := type.getAppFnArgs
    -- Check if the goal is of type `ForcedWin`
    if fn == ``ForcedWin && args.size == 2 then
      -- Extract the `Position` argument
      let posExpr := args[1]!  -- The second argument should be the Position
      -- Try to interpret `posExpr` as a `Position`
      let posVal ← unsafe (evalExpr _root_.Position (mkConst ``_root_.Position) posExpr)
      return some posVal
    else
      return none

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
          -- Use the extractPositionFromForcedWinGoal function
          let posOpt ← extractPositionFromForcedWinGoal g.mvarId
          match posOpt with
          | some posVal =>
            -- Create props for the ChessPositionWidget
            let widgetProps : ChessPositionWidgetProps := { position? := some posVal }
            let board_html := Html.ofComponent ChessPositionWidget widgetProps #[]
            let fen_str := fenFromPosition posVal
            let fen_html := <span>{Html.text fen_str}</span>
            let combined_html := Html.element "div" #[] #[board_html, fen_html]
            return some <| combined_html
          | none => return none)
    match html with
    | none => return <span>No ForcedWin goal found or invalid type.</span>
    | some inner => return inner


end Chess

@[widget_module]
def ForcedWinWidget :  Component PanelWidgetProps  :=
    mk_rpc_widget% Chess.forced_win_rpc
syntax (name := forcedWinWidget) "#forced_win_widget " term : command
