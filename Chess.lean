import Lean
import Mathlib.Data.List.Basic
import Mathlib.Tactic.CasesM

declare_syntax_cat chess_square
declare_syntax_cat horizontal_border
declare_syntax_cat game_top_row
declare_syntax_cat game_bottom_row
declare_syntax_cat game_row

syntax "═" : horizontal_border

syntax "\n╔" horizontal_border* "╗\n" : game_top_row

syntax "╚" horizontal_border* "╝\n" : game_bottom_row

syntax "║" chess_square* "║\n" : game_row

syntax "♙]" : chess_square -- white pawn
syntax "♘]" : chess_square -- white knight
syntax "♗]" : chess_square -- white bishop
syntax "♖]" : chess_square -- white rook
syntax "♕]" : chess_square -- white queen
syntax "♔]" : chess_square -- white king
syntax "♟]" : chess_square -- black pawn
syntax "♞]" : chess_square -- black knight
syntax "♝]" : chess_square -- black bishop
syntax "♜]" : chess_square -- black bishop
syntax "♛]" : chess_square -- black queen
syntax "♚]" : chess_square -- black king

syntax "░░" : chess_square -- light square
syntax "▓▓" : chess_square -- dark square
syntax "♔}" : chess_square -- white king and it's white's move
syntax "♚}" : chess_square -- black king and it's black's move

syntax:max game_top_row game_row* game_bottom_row : term

structure Coords where
  row : Nat
  col : Nat
deriving DecidableEq, Repr, Inhabited

def Coords.range : List Coords := Id.run do
  let mut result := []
  for r in [0:8] do
    for c in [0:8] do
      result := ⟨r,c⟩ :: result
  return result.reverse

def Coords.up (c : Coords) : Option Coords :=
 if c.row > 0
 then some { c with row := c.row - 1 }
 else none

def Coords.down (c : Coords) : Option Coords :=
 if c.row + 1 < 8
 then some { c with row := c.row + 1 }
 else none

def Coords.left (c : Coords) : Option Coords :=
 if c.col > 0
 then some { c with col := c.col - 1 }
 else none

def Coords.right (c : Coords) : Option Coords :=
 if c.col + 1 < 8
 then some { c with col := c.col + 1 }
 else none

def Coords.ul (c : Coords) : Option Coords :=
 c.up.bind Coords.left

def Coords.ur (c : Coords) : Option Coords :=
 c.up.bind Coords.right

def Coords.dl (c : Coords) : Option Coords :=
 c.down.bind Coords.left

def Coords.dr (c : Coords) : Option Coords :=
 c.down.bind Coords.right

-- knight's moves
def Coords.nm1 (c : Coords) : Option Coords :=
 c.ul.bind Coords.left

def Coords.nm2 (c : Coords) : Option Coords :=
 c.ul.bind Coords.up

def Coords.nm3 (c : Coords) : Option Coords :=
 c.ur.bind Coords.up

def Coords.nm4 (c : Coords) : Option Coords :=
 c.ur.bind Coords.right

def Coords.nm5 (c : Coords) : Option Coords :=
 c.dr.bind Coords.right

def Coords.nm6 (c : Coords) : Option Coords :=
 c.dr.bind Coords.down

def Coords.nm7 (c : Coords) : Option Coords :=
 c.dl.bind Coords.down

def Coords.nm8 (c : Coords) : Option Coords :=
 c.dl.bind Coords.left

inductive Piece where
| pawn : Piece
| knight : Piece
| bishop : Piece
| rook : Piece
| queen : Piece
| king : Piece
deriving DecidableEq, Repr

inductive Side where
| white : Side
| black : Side
deriving DecidableEq, Repr, Inhabited

def Side.other : Side -> Side
| white => black
| black => white

-- row, column.
-- (0,0) is the upper left corner (a8)
abbrev Squares := Array (Array (Option (Piece × Side)))

structure Position where
  squares : Squares
  turn : Side
deriving DecidableEq, Repr, Inhabited

def Position.get (p : Position) (c : Coords) : Option (Piece × Side) :=
  p.squares[c.row]![c.col]!

def Position.sideAt (p : Position) (c : Coords) : Option Side :=
  match p.get c with
  | some (_, s) => some s
  | none => none

def Position.set (p : Position) (c : Coords) (s : Option (Piece × Side)) : Position :=
  { p with squares := p.squares.set! c.row (p.squares[c.row]!.set! c.col s) }

-- size, current row, remaining cells -> gamestate
/-def positin_from_cells_aux : Coords → Nat → List (List CellContents) → GameState
| size, _, [] => ⟨size, ⟨0,0⟩, []⟩
| size, currentRow, row::rows =>
        let prevState := game_state_from_cells_aux size (currentRow + 1) rows
        update_state_with_row currentRow row prevState
-/

-- size, remaining cells -> gamestate
--def position_from_squares : List (List (Option (Piece × Side))) → Position
--| size, cells => game_state_from_cells_aux size 0 cells


def termOfSquare : Lean.TSyntax `chess_square → Lean.MacroM (Lean.TSyntax `term)
| `(chess_square| ░░) => `(none)
| `(chess_square| ▓▓) => `(none)
| `(chess_square| ♙]) => `(some (Piece.pawn, Side.white))
| `(chess_square| ♘]) => `(some (Piece.knight, Side.white))
| `(chess_square| ♗]) => `(some (Piece.bishop, Side.white))
| `(chess_square| ♖]) => `(some (Piece.rook, Side.white))
| `(chess_square| ♕]) => `(some (Piece.queen, Side.white))
| `(chess_square| ♔]) => `(some (Piece.king, Side.white))
| `(chess_square| ♔}) => `(some (Piece.king, Side.white))
| `(chess_square| ♟]) => `(some (Piece.pawn, Side.black))
| `(chess_square| ♞]) => `(some (Piece.knight, Side.black))
| `(chess_square| ♝]) => `(some (Piece.bishop, Side.black))
| `(chess_square| ♜]) => `(some (Piece.rook, Side.black))
| `(chess_square| ♛]) => `(some (Piece.queen, Side.black))
| `(chess_square| ♚]) => `(some (Piece.king, Side.black))
| `(chess_square| ♚}) => `(some (Piece.king, Side.black))
| _ => Lean.Macro.throwError "unknown chess square"

def termOfGameRow : Lean.TSyntax `game_row → Lean.MacroM (Lean.TSyntax `term)
| `(game_row| ║$squares:chess_square*║) =>
      do if squares.size != 8
         then Lean.Macro.throwError "row has wrong size"
         let squares' ← Array.mapM termOfSquare squares
         `(#[$squares',*])
| _ => Lean.Macro.throwError "unknown game row"

def turnOfSquare : Lean.TSyntax `chess_square → Option Side
| `(chess_square| ♔}) => some (Side.white)
| `(chess_square| ♚}) => some (Side.black)
| _ => none

def turnsOfRow : Lean.TSyntax `game_row → List (Option Side)
| `(game_row| ║$squares:chess_square*║) =>
      squares.toList.map turnOfSquare
| _ => []

macro_rules
| `(╔ $tb:horizontal_border* ╗
    $rows:game_row*
    ╚ $bb:horizontal_border* ╝) =>
      do if rows.size != 8 then Lean.Macro.throwError "chess board must have 8 rows"
         if tb.size != 8 * 2 || bb.size != 8 * 2 then
           Lean.Macro.throwError "chess board must have 8 columns"
         let rows' ← Array.mapM termOfGameRow rows
         let turns := (Array.map turnsOfRow rows).toList.join
         let whiteTurn := turns.contains (.some Side.white)
         let blackTurn := turns.contains (.some Side.black)
         if whiteTurn ∧ blackTurn then
           Lean.Macro.throwError "cannot be both white's turn and black's turn"
         if whiteTurn
         then
           `(Position.mk #[$rows',*] .white)
         else
           `(Position.mk #[$rows',*] .black)

def syntaxOfSquare (turn : Side) : (Piece × Side) →
  Lean.PrettyPrinter.Delaborator.DelabM (Lean.TSyntax `chess_square)
| (Piece.pawn, Side.white) => `(chess_square| ♙])
| (Piece.knight, Side.white) => `(chess_square| ♘])
| (Piece.bishop, Side.white) => `(chess_square| ♗])
| (Piece.rook, Side.white) => `(chess_square| ♖])
| (Piece.queen, Side.white) => `(chess_square| ♕])
| (Piece.king, Side.white) =>
  match turn with
  | .white => `(chess_square| ♔})
  | .black => `(chess_square| ♔])
| (Piece.pawn, Side.black) => `(chess_square| ♟])
| (Piece.knight, Side.black) => `(chess_square| ♞])
| (Piece.bishop, Side.black) => `(chess_square| ♝])
| (Piece.rook, Side.black) => `(chess_square| ♜])
| (Piece.queen, Side.black) => `(chess_square| ♛])
| (Piece.king, Side.black) =>
  match turn with
  | .white => `(chess_square| ♚])
  | .black => `(chess_square| ♚})

def extractSquare : Lean.Expr → Lean.MetaM (Option (Piece × Side))
| exp => do
    let exp' ← Lean.Meta.whnf exp
    match exp'.getAppFn.constName!.toString with
    | "Option.none" => return none
    | "Option.some" =>
      let v := exp'.getAppArgs[1]!
      --let s := v.getAppFn.constName!.toString
      let args := v.getAppArgs
      match args[2]!.constName!, args[3]!.constName! with
      | `Piece.pawn, `Side.white => return some (Piece.pawn, Side.white)
      | `Piece.knight, `Side.white => return some (Piece.knight, Side.white)
      | `Piece.bishop, `Side.white => return some (Piece.bishop, Side.white)
      | `Piece.rook, `Side.white => return some (Piece.rook, Side.white)
      | `Piece.queen, `Side.white => return some (Piece.queen, Side.white)
      | `Piece.king, `Side.white => return some (Piece.king, Side.white)
      | `Piece.pawn, `Side.black => return some (Piece.pawn, Side.black)
      | `Piece.knight, `Side.black => return some (Piece.knight, Side.black)
      | `Piece.bishop, `Side.black => return some (Piece.bishop, Side.black)
      | `Piece.rook, `Side.black => return some (Piece.rook, Side.black)
      | `Piece.queen, `Side.black => return some (Piece.queen, Side.black)
      | `Piece.king, `Side.black => return some (Piece.king, Side.black)
      | _, _ => pure ()
      return none
    | other =>
      dbg_trace "unexpected const {other}"
      return none

partial def extractRowAux : Lean.Expr → Lean.MetaM (List (Option (Piece × Side)))
| exp => do
  let exp' ← Lean.Meta.whnf exp
  let f := Lean.Expr.getAppFn exp'
  match f.constName!.toString with
  | "List.cons" =>
      let consArgs := Lean.Expr.getAppArgs exp'
      let rest ← extractRowAux consArgs[2]!
      let square ← extractSquare consArgs[1]!
      return square :: rest
  | "List.nil" =>
      return []
  | other =>
       dbg_trace "unrecognized constant: {other}"
       return []

partial def extractRow : Lean.Expr → Lean.MetaM (Array (Option (Piece × Side)))
| exp => do
    if exp.getAppFn.constName!.toString ≠ "Array.mk" then
      dbg_trace exp.getAppFn.constName!.toString
      throwError "nope"
    let exp' := exp.getAppArgs[1]!
    let l ← extractRowAux exp'
    return l.toArray

partial def extractRowList : Lean.Expr → Lean.MetaM (List (Array (Option (Piece × Side))))
| exp => do
  let exp':Lean.Expr ← (Lean.Meta.whnf exp)
  let f := Lean.Expr.getAppFn exp'
  match f.constName!.toString with
  | "List.cons" =>
       let consArgs := Lean.Expr.getAppArgs exp'
       let rest ← extractRowList consArgs[2]!
       let row ← extractRow consArgs[1]!
       return row :: rest
  | "List.nil" =>
       return []
  | other =>
       dbg_trace "unrecognized constant: {other}"
       return []

partial def extractPosition : Lean.Expr → Lean.MetaM Position
| exp => do
    let exp': Lean.Expr ← Lean.Meta.reduce exp
    let positionArgs := Lean.Expr.getAppArgs exp'
    let squaresList := positionArgs[0]!.getAppArgs[1]!
    let rows ← extractRowList squaresList
    let side ← match positionArgs[1]!.constName! with
                | `Side.white => pure Side.white
                | `Side.black => pure Side.black
                | _ => throwError "unrecognized side"
    return Position.mk rows.toArray side

def delabGameRow : Array (Lean.TSyntax `chess_square) →
    Lean.PrettyPrinter.Delaborator.DelabM (Lean.TSyntax `game_row)
| a => `(game_row| ║ $a:chess_square* ║)

def delabPosition : Lean.Expr → Lean.PrettyPrinter.Delaborator.Delab
| e =>
  do guard $ e.getAppNumArgs == 2
     let pos ← extractPosition e
     let topBar := Array.mkArray (8 * 2) $ ← `(horizontal_border| ═)
     let lightSquare ← `(chess_square| ░░)
     let darkSquare ← `(chess_square| ▓▓)

     let mut a : Array (Array (Lean.TSyntax `chess_square)) :=
        Array.ofFn (n := 8) (fun row ↦ Array.ofFn (n := 8)
        (fun col ↦ if (col.val + row.val) % 2 = 0 then darkSquare else lightSquare))

     for coords in Coords.range do
       if let some s := pos.get coords then
         let v ← syntaxOfSquare pos.turn s
         a := a.set! coords.row (a[coords.row]!.set! coords.col v)
       pure ()

     let aa ← Array.mapM delabGameRow a

     `(╔$topBar:horizontal_border*╗
       $aa:game_row*
       ╚$topBar:horizontal_border*╝)

@[delab app.Position.mk] def delabPositionMk : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  let e' ← Lean.Meta.reduce e
  delabPosition e'

def game_start :=
  ╔════════════════╗
  ║♜]♞]♝]♛]♚]♝]♞]♜]║
  ║♟]♟]♟]♟]♟]♟]♟]♟]║
  ║░░▓▓░░▓▓░░▓▓░░▓▓║
  ║▓▓░░▓▓░░▓▓░░▓▓░░║
  ║░░▓▓░░▓▓░░▓▓░░▓▓║
  ║▓▓░░▓▓░░▓▓░░▓▓░░║
  ║♙]♙]♙]♙]♙]♙]♙]♙]║
  ║♖]♘]♗]♕]♔}♗]♘]♖]║
  ╚════════════════╝

#print game_start

def pos2 :=  ╔════════════════╗
             ║♜]♞]♝]♛]♚}♝]♞]♜]║
             ║♟]♟]♟]♟]♟]♟]♟]♟]║
             ║░░▓▓░░▓▓░░▓▓░░▓▓║
             ║▓▓░░▓▓░░▓▓░░▓▓░░║
             ║░░▓▓░░▓▓♙]▓▓░░▓▓║
             ║▓▓░░▓▓░░▓▓░░▓▓░░║
             ║♙]♙]♙]♙]░░♙]♙]♙]║
             ║♖]♘]♗]♕]♔]♗]♘]♖]║
             ╚════════════════╝

--#print pos2

-----------------------------------
-- end (d)elab, start analysis

-----------------------------------------------

def row_to_rank (row : Nat) : Char := Char.ofNat ((8 - row) + (Char.toNat '0'))
def col_to_file (col : Nat) : Char := Char.ofNat (col + (Char.toNat 'a'))

def is_rank (rank : Char) : Bool := '1'.toNat ≤ rank.toNat ∧ rank.toNat ≤ '8'.toNat
def is_file (rank : Char) : Bool := 'a'.toNat ≤ rank.toNat ∧ rank.toNat ≤ 'h'.toNat
def rank_to_row (rank : Char) : Nat := 8 - (rank.toNat - '0'.toNat)
def file_to_col (rank : Char) : Nat := rank.toNat - 'a'.toNat

def is_piece : Char → Bool
| 'K' => true
| 'Q' => true
| 'R' => true
| 'B' => true
| 'N' => true
| _ => false

def char_to_piece : Char → Piece
| 'K' => .king
| 'Q' => .queen
| 'R' => .rook
| 'B' => .bishop
| 'N' => .knight
| _ => .pawn

def piece_to_char : Piece → Option Char
| .king => some 'K'
| .queen => some 'Q'
| .rook => some 'R'
| .bishop => some 'B'
| .knight => some 'N'
| .pawn => none

structure OrdinaryChessMove where
  piece : Piece
  dst : Coords -- destination coords
  capture : Bool
  promote : Option Piece
  disambiguate_col : Option Nat
  disambiguate_row : Option Nat
deriving DecidableEq, Repr

inductive ChessMove where
| CastleShort : ChessMove
| CastleLong : ChessMove
| Ordinary : OrdinaryChessMove → ChessMove
deriving DecidableEq, Repr, Inhabited

instance : ToString ChessMove where
toString : ChessMove → String
| .CastleShort => "O-O"
| .CastleLong => "O-O-O"
| .Ordinary { piece, dst, capture,
              disambiguate_row, disambiguate_col, promote } => Id.run do
  let mut result := []
  if let some p := promote then
    if let some c := piece_to_char p
    then result := '=' :: c :: result

  result := col_to_file dst.col :: row_to_rank dst.row :: result

  if capture then
    result := '×' :: result

  if let some r := disambiguate_row then
    result := row_to_rank r :: result
  if let some c := disambiguate_col then
    result := col_to_file c :: result

  if let some c := piece_to_char piece
  then result := c :: result
  return String.mk result

def ChessMove.ofString : String → Option ChessMove
| "O-O" => some .CastleShort
| "O-O-O" => some .CastleLong
| s => Id.run do
  let mut piece := Piece.pawn
  let mut rest := s.toList
  match rest with
  | [] => return none | [_] => return none
  | p :: cs =>
    if is_piece p
    then
        piece := char_to_piece p
        rest := cs
    else
        piece := .pawn

  -- parsing the rest is easiest in reverse
  let mut rrest := rest.reverse
  let mut promote := none
  match rrest with
  | p :: '=' :: cs =>
    if is_piece p
    then promote := some (char_to_piece p)
         rrest := cs
    else return none
  | _ => pure ()

  let crow :: cfile :: cs := rrest | return none
  if ¬is_file cfile then return none
  if ¬is_rank crow then return none
  let dst := { row := rank_to_row crow, col := file_to_col cfile}
  rrest := cs

  let mut capture := false
  match rrest with
  | '×' :: cs =>
        capture := true
        rrest := cs
  | _ => pure ()

  let mut disambiguate_row : Option Nat := none
  let mut disambiguate_col : Option Nat := none
  match rrest with
  | c :: cs =>
    if is_file c
    then disambiguate_col := some (file_to_col c)
         if ¬cs.isEmpty then return none
    else
      if is_rank c
      then disambiguate_row := some (rank_to_row c)
           match cs with
           | [] => pure ()
           | [c] =>
             if is_file c
             then disambiguate_col := some (file_to_col c)
             else return none
           | _ => return none
    rrest := cs
  | [] => pure ()

  return some (.Ordinary {piece, dst, capture,
                          disambiguate_row, disambiguate_col, promote})

#eval (ChessMove.ofString "Qa6×d3").map ToString.toString
--#eval (ChessMove.ofString "e×f5")

----

def look_for_move_src (pos : Position) (side : Side) (dst : Coords)
    (step : Coords → Option Coords) (allowed_piece : Piece)
    : Nat → Option (Coords × Piece)
| 0 => none
| .succ n =>
  let msrc := step dst
  match msrc with
  | none => none
  | some src =>
    match pos.get src with
    | none => look_for_move_src pos side src step allowed_piece n
    | some (piece, side1) =>
      if side = side1 ∧ (piece = allowed_piece ∨ piece = .queen) then
       some (src, piece)
      else
       none

/-- returns true is dst is threatened by a piece of side `side`
-/
def square_is_threatened (pos : Position) (side : Side) (dst : Coords)
    : Bool := Id.run do
  if pos.sideAt dst = some side then
    -- the destination is already occupied by a piece from the same side
    return false

  let contents := pos.get dst

  -- pawn moves
  match side with
  | .white =>
    if contents.isNone then pure ()
    else -- dst has a piece of color side.other
      if let some src := dst.dr then
        if pos.get src = some (.pawn, .white) then return true
      if let some src := dst.dl then
        if pos.get src = some (.pawn, .white) then return true
    -- TODO en passant?
  | .black =>
    if contents.isNone then pure ()
    else -- dst has a piece of color side.other
      if let some src := dst.ur then
        if pos.get src = some (.pawn, .black) then
          return true
      if let some src := dst.ul then
        if pos.get src = some (.pawn, .black) then
          return true

  -- knight moves
  for src in [dst.nm1, dst.nm2, dst.nm3, dst.nm4,
              dst.nm5, dst.nm6, dst.nm7, dst.nm8].filterMap id do
    if pos.get src = some (.knight, side) then
      return true

  -- rook, bishop, and queen moves
  if let some _ := look_for_move_src pos side dst Coords.up .rook 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.down .rook 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.left .rook 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.right .rook 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.ul .bishop 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.ur .bishop 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.dr .bishop 7 then
    return true

  if let some _ := look_for_move_src pos side dst Coords.dl .bishop 7 then
    return true

  -- king moves
  for src in [dst.up, dst.ur, dst.right, dst.dr,
              dst.down, dst.dl, dst.left, dst.ul].filterMap id do
    if pos.get src = some (.king, side) then
      return true

  return false

def find_king (pos : Position) (side : Side) : List Coords → Coords
| [] => ⟨0,0⟩
| coords :: rest =>
  if pos.get coords = some (.king, side)
  then coords
  else find_king pos side rest

def king_is_in_check (pos : Position) (side : Side) : Bool :=
  let king_coords : Coords := find_king pos side Coords.range
  square_is_threatened pos side.other king_coords

@[reducible]
def do_simple_move (pos : Position) (src : Coords) (dst : Coords) : Position :=
  let pos1 := { pos with turn := pos.turn.other }
  let tmp := pos1.get src
  (pos1.set src none).set dst tmp

@[reducible]
def do_promote_move (pos : Position) (src : Coords) (dst : Coords)
    (piece: Piece) : Position :=
  let pos1 := { pos with turn := pos.turn.other }
  (pos1.set src none).set dst (some (piece, pos.turn))

def simple_pawn_move (dst : Coords) : ChessMove :=
  .Ordinary { piece := .pawn, dst, capture := false, promote := none,
              disambiguate_col := none, disambiguate_row := none }

def promote_pawn_moves (pos : Position) (src dst : Coords)
    : List (ChessMove × Position) :=
  [Piece.knight, Piece.bishop, Piece.rook, Piece.queen].map
  fun p ↦
   let capture := (pos.get dst).isSome
   let disambiguate_col := if capture then some src.col else none
   let pos1 := { pos with turn := pos.turn.other }
   let pos2 := (pos1.set src none).set dst (some (p, pos.turn))
   (.Ordinary { piece := .pawn, dst, capture, promote := some p,
                disambiguate_col, disambiguate_row := none },
    pos2)

def king_move (dst : Coords) (capture : Bool) : ChessMove :=
  .Ordinary { piece := .king, dst, capture, promote := none,
              disambiguate_col := none, disambiguate_row := none }

def capture_pawn_move (src dst : Coords) : ChessMove :=
  .Ordinary { piece := .pawn, dst, capture := true, promote := none,
              disambiguate_col := some src.col, disambiguate_row := none }

def unambig_piece_move (src dst : Coords) (piece : Piece) (capture : Bool) : ChessMove :=
  .Ordinary { piece, dst, capture, promote := none,
              disambiguate_col := some src.col, disambiguate_row := some src.row }

def white_pawn_moves_from_src (pos : Position) (src : Coords)
    : List (ChessMove × Position) := Id.run do
  let mut result := []
  if let some dst := src.up then
    if let none := pos.get dst then
      if dst.row = 0
      then result := (promote_pawn_moves pos src dst).append result
      else
        result := (simple_pawn_move dst, do_simple_move pos src dst) :: result
        if src.row = 6 then
          if let some dst := dst.up then
            if let none := pos.get dst then
              result := (simple_pawn_move dst, do_simple_move pos src dst) :: result
  for dst in [src.ul, src.ur].filterMap id do
     -- TODO en passant
     if let some (_, side) := pos.get dst then
       if side ≠ pos.turn then
         if dst.row = 0
         then result := (promote_pawn_moves pos src dst).append result
         else
           result := (capture_pawn_move src dst, do_simple_move pos src dst) :: result
  return result

def black_pawn_moves_from_src (pos : Position) (src : Coords)
    : List (ChessMove × Position) := Id.run do
  let mut result := []
  if let some dst := src.down then
    if let none := pos.get dst then
      if dst.row = 7
      then result := (promote_pawn_moves pos src dst).append result
      else
        result := (simple_pawn_move dst, do_simple_move pos src dst) :: result
        if src.row = 1 then
          if let some dst := dst.down then
            if let none := pos.get dst then
              result := (simple_pawn_move dst, do_simple_move pos src dst) :: result
  for dst in [src.dl, src.dr].filterMap id do
     -- TODO en passant
     if let some (_, side) := pos.get dst then
       if side ≠ pos.turn then
         if dst.row = 7
         then result := (promote_pawn_moves pos src dst).append result
         else
           result := (capture_pawn_move src dst, do_simple_move pos src dst) :: result
  return result

def look_for_moves_dst (pos : Position) (piece : Piece) (src cur : Coords)
    (step : Coords → Option Coords) (acc : List (ChessMove × Position))
    : Nat → List (ChessMove × Position)
| 0 => acc
| .succ n =>
  let mdst := step cur
  match mdst with
  | none => acc
  | some dst =>
    match pos.get dst with
    | none => look_for_moves_dst pos piece src dst step
              ((unambig_piece_move src dst piece false,
                do_simple_move pos src dst)::acc) n
    | some (_, side) =>
      if pos.turn.other = side then
       (unambig_piece_move src dst piece true,
        do_simple_move pos src dst)::acc
      else
       acc

-- returns the valid moves that start from src.
-- Fully disambiguates R,B,N,Q moves. A later step must
-- remove the disambiguation to the extent possible.
def valid_moves_from_src (pos : Position) (src : Coords)
    : List (ChessMove × Position) := Id.run do
  let some (piece, side) := pos.get src | return []
  if side ≠ pos.turn then return []
  let mut result := []
  match (piece, side) with
  | (.pawn, .white) => result := white_pawn_moves_from_src pos src
  | (.pawn, .black) => result := black_pawn_moves_from_src pos src
  | (.knight, _) =>
    for dst in [src.nm1, src.nm2, src.nm3, src.nm4,
                src.nm5, src.nm6, src.nm7, src.nm8].filterMap id do
      match pos.get dst with
      | some (_, side1) =>
        if side1 = side.other then
          result := (unambig_piece_move src dst .knight true,
                     do_simple_move pos src dst) :: result
      | none =>
          result := (unambig_piece_move src dst .knight false,
                     do_simple_move pos src dst) :: result
  | (.bishop, _) =>
    result := result.append (look_for_moves_dst pos .bishop src src Coords.ul [] 7)
    result := result.append (look_for_moves_dst pos .bishop src src Coords.ur [] 7)
    result := result.append (look_for_moves_dst pos .bishop src src Coords.dr [] 7)
    result := result.append (look_for_moves_dst pos .bishop src src Coords.dl [] 7)

  | (.rook, _) =>
    result := result.append (look_for_moves_dst pos .rook src src Coords.up [] 7)
    result := result.append (look_for_moves_dst pos .rook src src Coords.left [] 7)
    result := result.append (look_for_moves_dst pos .rook src src Coords.down [] 7)
    result := result.append (look_for_moves_dst pos .rook src src Coords.right [] 7)

  | (.queen, _) =>
    result := result.append (look_for_moves_dst pos .queen src src Coords.up [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.left [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.down [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.right [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.ul [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.ur [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.dr [] 7)
    result := result.append (look_for_moves_dst pos .queen src src Coords.dl [] 7)

  | (.king, _) =>
    for dst in [src.up, src.right, src.down, src.left,
                src.ul, src.ur, src.dr, src.dl].filterMap id do
      match pos.get dst with
      | some (_, side1) =>
        if side1 = side.other then
          result := (king_move dst true, do_simple_move pos src dst) :: result
      | none =>
          result := (king_move dst false, do_simple_move pos src dst) :: result


  let result' := result.filter (fun (_,p) ↦ ¬king_is_in_check p side)
  return result'

/--
Take a bunch of moves which have Q,R,N,B moves fully disambiguated,
and remove redundant disambiuation. TODO: actually implement this properly.
Currently this just fully ambiguates, which can cause collisions.
-/
def ambiguate (moves : List (ChessMove × Position))
    : List (ChessMove × Position) := Id.run do
  let mut result := []
  for (m,p) in moves do
    match m with
    | .CastleShort | .CastleLong
    | .Ordinary { piece := .pawn, .. }
    | .Ordinary { piece := .king, .. } =>
        result := (m,p) :: result
    | .Ordinary { piece, dst, capture, promote,
                  disambiguate_col := _, disambiguate_row := _} =>
        let disambiguate_col := none
        let disambiguate_row := none
        result := (.Ordinary { piece, dst, capture, promote,
                               disambiguate_col, disambiguate_row},
                   p) :: result
  return result

def valid_moves (pos : Position) : List (ChessMove × Position) := Id.run do
  let mut moves := []
  for src in Coords.range do
    moves := (valid_moves_from_src pos src).append moves

  return ambiguate moves

#reduce valid_moves game_start
--#reduce valid_moves pos2

-- returns true if p.turn is in check and has no moves
@[reducible]
def IsCheckmate (pos : Position) : Prop :=
  if king_is_in_check pos pos.turn
  then valid_moves pos = []
  else False

/--
 `ForcedWin side pos` means than `side` has a forced win
 at position `pos`.
-/
inductive ForcedWin : Side → Position → Prop where
| Checkmate (p : Position) : IsCheckmate p → ForcedWin p.turn.other p
| Self (p : Position) (m : ChessMove) (p1 : Position) :
   (m, p1) ∈ valid_moves p → ForcedWin p.turn p1 → ForcedWin p.turn p
| Opponent (p : Position) :
   (∀ vm ∈ valid_moves p, ForcedWin p.turn.other vm.snd) → ForcedWin p.turn.other p
   -- FIXME: This is wrong because it considers a stalemate to be a win for the side
   --        who doesn't have the move.
--------------

def make_move (pos : Position) (cm : ChessMove) : Option Position :=
  let mvs := valid_moves pos
  (mvs.find? (·.fst = cm)).map (·.snd)

---

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
-----

/-
theorem black_wins_back_rank :
    ForcedWin .black
      ╔════════════════╗
      ║░░▓▓░░▓▓♜]▓▓♚}▓▓║
      ║♟]░░▓▓░░▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║♙]♙]♙]▓▓░░♙]♙]♙]║
      ║▓▓░░▓▓░░▓▓░░♔]░░║
      ╚════════════════╝ := by
  move "Re1"
  checkmate
-/


/-
theorem white_wins_promotion_back_rank :
    ForcedWin .white
      ╔════════════════╗
      ║░░▓▓░░▓▓░░▓▓♚]▓▓║
      ║♟]░░♙]░░▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║♙]♙]░░▓▓░░♙]♙]♙]║
      ║▓▓░░▓▓░░▓▓░░♔}░░║
      ╚════════════════╝ := by
  move "c8=R"
  checkmate
-/

/-
theorem black_wins_promotion :
    ForcedWin .black
      ╔════════════════╗
      ║░░▓▓░░▓▓░░▓▓♚}▓▓║
      ║♟]░░▓▓░░▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓♙]♙]♗]║
      ║♙]♙]░░▓▓♟]♙]♔]♙]║
      ║▓▓░░▓▓░░▓▓♘]♖]♖]║
      ╚════════════════╝ := by
  move "e1=N"
  checkmate
-/

/-
/-
Timman-Short 1990
(from https://en.wikipedia.org/wiki/Smothered_mate)
-/
set_option maxHeartbeats 3000000 in
theorem smothered_mate :
    ForcedWin .white
      ╔════════════════╗
      ║▓▓░░▓▓░░♜]░░▓▓♚]║
      ║♟]▓▓♟]♖]♙]▓▓♟]♟]║
      ║▓▓░░♟]░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░♟]♘]▓▓║
      ║▓▓░░♕]░░▓▓░░♞]░░║
      ║♛]▓▓░░▓▓░░▓▓♙]▓▓║
      ║♙]░░▓▓░░♙]♙]▓▓♙]║
      ║░░▓▓░░▓▓░░▓▓♔}▓▓║
      ╚════════════════╝ := by
  move "Nf7"
  opponent_move
  move "Nh6"
  opponent_move
  move "Qg8"
  opponent_move
  move "Nf7"
  checkmate
-/

/-
set_option maxHeartbeats 3000000 in
theorem emms115 :
    ForcedWin .white
      ╔════════════════╗
      ║♚]▓▓░░▓▓░░▓▓░░♜]║
      ║♟]♝]♗]♘]▓▓░░♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║♙]░░♞]░░▓▓░░▓▓░░║
      ║░░♝]♙]▓▓░░▓▓░░▓▓║
      ║▓▓♙]▓▓░░▓▓░░♙]░░║
      ║░░▓▓░░♜]░░♙]♗]♙]║
      ║♖]░░▓▓░░▓▓♖]♔}░░║
      ╚════════════════╝ := by
  move "Nb6"
  opponent_move
  move "a×b6"
  opponent_move
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
-/

/-
set_option maxHeartbeats 3000000 in
theorem emms_140 :
    ForcedWin .white
      ╔════════════════╗
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓♚]▓▓░░▓▓░░║
      ║░░♜]♟]▓▓♖]▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░♟]░░║
      ║♙]♟]░░▓▓░░♜]░░▓▓║
      ║♞]♗]▓▓░░▓▓♖]♔}░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ╚════════════════╝ := by
  move "Rd3"
  opponent_move
  · sorry
  · sorry
  · sorry
  --move "Re8"
-/

/-
set_option maxHeartbeats 3000000 in
theorem emms_144 :
    ForcedWin .white
      ╔════════════════╗
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░♕]♟]║
      ║░░♟]♛]▓▓░░▓▓♝]▓▓║
      ║▓▓░░▓▓♟]▓▓♟]♚]░░║
      ║░░▓▓░░♙]░░▓▓░░▓▓║
      ║▓▓░░▓▓░░♘]░░♙]░░║
      ║♙]♙]░░▓▓░░♙]░░♔}║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ╚════════════════╝ := by
  move "f4"
  opponent_move
  move "g4"
  opponent_move
  · move "Qe5"
    opponent_move
    · move "Q×f5"
      opponent_move <;> (move "Qg5"; checkmate)
    · move "N×g4"
      checkmate
    · move "Qg5"
      checkmate
  · move "Qh6"
    opponent_move
    move "Q×h5"
    checkmate
-/

/-
set_option maxHeartbeats 3000000 in
theorem emms_145 :
    ForcedWin .black
      ╔════════════════╗
      ║░░▓▓░░▓▓░░♝]♜]♚}║
      ║▓▓░░▓▓░░▓▓♟]♜]♟]║
      ║♗]▓▓░░▓▓♟]▓▓░░▓▓║
      ║♘]░░♟]░░▓▓░░▓▓░░║
      ║♙]▓▓░░▓▓♙]▓▓░░▓▓║
      ║▓▓░░♘]░░▓▓♞]▓▓♛]║
      ║░░▓▓♖]▓▓♕]▓▓♙]▓▓║
      ║▓▓░░▓▓♖]▓▓♔]▓▓░░║
      ╚════════════════╝ := by
  move "Qh1"
  opponent_move
  move "R×g2"
  opponent_move
  · move "Qh3"
    opponent_move
    move "Qg3"
    checkmate
  · move "Qh6"
    opponent_move
    · -- need to disambiguate which rook
      sorry
    · move "Ne5"
      checkmate
-/

/-
set_option maxHeartbeats 3000000 in
theorem emms_151 :
    ForcedWin .black
      ╔════════════════╗
      ║░░▓▓░░♜]░░▓▓░░♚}║
      ║♖]♖]▓▓░░▓▓░░♟]░░║
      ║░░▓▓░░▓▓░░♟]░░▓▓║
      ║▓▓░░▓▓░░♟]░░▓▓░░║
      ║░░▓▓♗]▓▓░░▓▓♝]♟]║
      ║▓▓♙]▓▓░░▓▓♜]▓▓░░║
      ║░░▓▓░░▓▓♘]▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░♔]░░║
      ╚════════════════╝ := by
  move "Rd1"
  opponent_move
  rotate_left
  · move "Rf2"
    checkmate
  · move "h3"
    opponent_move
    move "Rf2"
    opponent_move
    move "Rg2"
    opponent_move
    move "g5"
    checkmate
-/

/-
theorem morphy_mates_in_two :
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
-/

/-
theorem generic_game : ForcedWin .white game_start := by
  move "e4"
  opponent_move
  · move "d4"
    sorry
  · move "Ke2"
    sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
-/
