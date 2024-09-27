#!/usr/bin/env python3

import os
import sys
import subprocess
import venv

# Define the path to the script directory and virtual environment directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
VENV_DIR = os.path.join(SCRIPT_DIR, 'venv')

def create_virtualenv(venv_path):
    """Creates a virtual environment if it doesn't exist."""
    if not os.path.isdir(venv_path):
        venv.create(venv_path, with_pip=True)

def install_package(venv_path, package):
    """Installs a package in the virtual environment using pip."""
    pip_executable = os.path.join(venv_path, 'bin', 'pip')
    # Check if the package is already installed
    try:
        subprocess.check_call([pip_executable, 'show', package], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        # Package is not installed; install it silently
        subprocess.check_call([pip_executable, 'install', package], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def is_running_in_venv():
    """Checks if the script is already running inside the virtual environment."""
    venv_python = os.path.join(VENV_DIR, 'bin', 'python3')
    return os.path.realpath(sys.executable) == os.path.realpath(venv_python)

def activate_and_run():
    """Runs the chess move logic."""
    # Install python-chess if not installed
    install_package(VENV_DIR, 'python-chess')

    # Now, import chess and the engine after ensuring installation
    import chess
    import chess.engine

    if len(sys.argv) != 2:
        print("Usage: get_next_move.py '<FEN>'")
        sys.exit(1)

    fen = sys.argv[1]
    board = chess.Board(fen)

    # Initialize the engine (specify the path if necessary)
    engine = chess.engine.SimpleEngine.popen_uci('stockfish')

    try:
        # Set a thinking time limit (e.g., 0.1 seconds)
        # TODO: make this an additional option here!
        result = engine.play(board, chess.engine.Limit(time=.1))
        move = result.move
        # Output the move in Standard Algebraic Notation (e.g., "Nf3")
        # Strip the '+', because we don't need it
        print(board.san(move).replace('+', '').replace('#', ''))
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    finally:
        engine.quit()

def run_in_virtualenv():
    """Re-executes the script using the virtual environment's Python."""
    venv_python = os.path.join(VENV_DIR, 'bin', 'python3')

    # If the current interpreter is not the virtual environment's python, re-execute the script
    if not is_running_in_venv():
        print("Re-executing the script within the virtual environment...")
        os.execv(venv_python, [venv_python] + sys.argv)

if __name__ == "__main__":
    # Ensure the virtual environment is created
    create_virtualenv(VENV_DIR)

    # Check if we are running inside the virtual environment
    if not is_running_in_venv():
        run_in_virtualenv()
    else:
        activate_and_run()