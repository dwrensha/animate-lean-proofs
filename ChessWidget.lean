import Lean

open Lean Widget

@[widget_module]
def ChessPositionWidget : Lean.Widget.Module where
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

  const { turn = 'nobody', squares = emptyBoard } = props.pos || {};

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
#widget ChessPositionWidget
