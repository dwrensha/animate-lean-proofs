import Chess.Basic

/- Parsing Forsyth–Edwards Notation (FEN) -/
def parsePiece : Char → Option (Piece × Side)
| 'p' => some (Piece.pawn, Side.black)
| 'n' => some (Piece.knight, Side.black)
| 'b' => some (Piece.bishop, Side.black)
| 'r' => some (Piece.rook, Side.black)
| 'q' => some (Piece.queen, Side.black)
| 'k' => some (Piece.king, Side.black)
| 'P' => some (Piece.pawn, Side.white)
| 'N' => some (Piece.knight, Side.white)
| 'B' => some (Piece.bishop, Side.white)
| 'R' => some (Piece.rook, Side.white)
| 'Q' => some (Piece.queen, Side.white)
| 'K' => some (Piece.king, Side.white)
| _ => none

def parseFenRow (row : String) : List (Option (Piece × Side)) :=
  row.foldl (fun acc c =>
    if c.isDigit then
      let n := c.toNat - '0'.toNat
      acc ++ List.replicate n none
    else
      acc ++ [parsePiece c]
  ) []

def parseFenBoard (board : List String) : Squares :=
  board.map parseFenRow

def parseSideToMove (s : String) : Side :=
  match s with
  | "w" => Side.white
  | "b" => Side.black
  | _ => Side.white  -- Defaulting to white in case of error

def positionFromFen (fen : String) : Option Position :=
  let parts := fen.splitOn " "
  match parts with
  | boardStr :: sideToMoveStr :: _ =>
      let boardRows := boardStr.splitOn "/"
      if boardRows.length = 8 then
        let board := parseFenBoard boardRows
        let sideToMove := parseSideToMove sideToMoveStr
        -- TODO: Add parsing for
        -- castling, en passant, halfmove clock and fullmove number.
        some { squares := board, turn := sideToMove }
      else
        none
  | _ => none

def pieceToFenChar : Piece × Side → Char
| (Piece.pawn, Side.white) => 'P'
| (Piece.knight, Side.white) => 'N'
| (Piece.bishop, Side.white) => 'B'
| (Piece.rook, Side.white) => 'R'
| (Piece.queen, Side.white) => 'Q'
| (Piece.king, Side.white) => 'K'
| (Piece.pawn, Side.black) => 'p'
| (Piece.knight, Side.black) => 'n'
| (Piece.bishop, Side.black) => 'b'
| (Piece.rook, Side.black) => 'r'
| (Piece.queen, Side.black) => 'q'
| (Piece.king, Side.black) => 'k'

def fenRowFromSquares (row : List (Option (Piece × Side))) : String :=
  let rec aux (squares : List (Option (Piece × Side))) (acc : String)
      (emptyCount : Nat) : String :=
    match squares with
    | [] =>
        if emptyCount > 0 then
          acc ++ toString emptyCount
        else
          acc
    | (some piece) :: rest =>
        let acc' := if emptyCount > 0 then acc ++ toString emptyCount else acc
        let c := pieceToFenChar piece
        aux rest (acc' ++ c.toString) 0
    | none :: rest =>
        aux rest acc (emptyCount + 1)
  aux row "" 0

def fenFromPosition (pos : Position) : String :=
  let boardRows := pos.squares
  let fenRows := boardRows.map fenRowFromSquares
  let fenBoard := String.intercalate "/" fenRows
  let sideToMove := match pos.turn with
                    | Side.white => "w"
                    | Side.black => "b"
  -- TODO: handle the following fields
  let castling := "-"
  let enPassant := "-"
  let halfmoveClock := "0"
  let fullmoveNumber := "0"
  fenBoard ++ " " ++ sideToMove ++ " " ++ castling ++ " " ++ enPassant ++ " " ++ halfmoveClock ++ " " ++ fullmoveNumber

-- Example usage:
def my_pos := (positionFromFen "r3k2r/pp2bppp/2n1pn2/q1bpN3/2B5/4P3/PPP2PPP/RNBQ1RK1 w kq - 4 10").get!

#reduce my_pos

#eval fenFromPosition my_pos

#eval positionFromFen (fenFromPosition my_pos) == some my_pos
