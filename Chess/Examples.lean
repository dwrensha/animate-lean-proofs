import Chess.Basic
import Chess.Tactics
import Chess.Widgets


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

set_option linter.hashCommand false
#widget ChessPositionWidget with { position? := some <| get_pos black_wins_promotion : ChessPositionWidgetProps }

/-
Timman-Short 1990
(from https://en.wikipedia.org/wiki/Smothered_mate)
-/
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
  with_panel_widgets [ForcedWinWidget]
    move "Nf7"
    opponent_move
    move "Nh6"
    opponent_move
    move "Qg8"
    opponent_move
    move "Nf7"
    checkmate



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
