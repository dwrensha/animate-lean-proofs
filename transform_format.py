import json
import argparse
import subprocess
import tempfile
import sys
import os


def parse_state(state_str):
    """Parse state string into hypotheses and goal"""
    lines = state_str.strip().split('\n')
    hypotheses = []
    goal = ""
    
    for i, line in enumerate(lines):
        if line.startswith('⊢'):
            goal = line[1:].strip()
        elif ': ' in line and not line.startswith('case'):
            # This is a hypothesis
            hypotheses.append(line.strip())
    
    return {"hypotheses": hypotheses, "goal": goal}


def convert_to_tree(movie_json):
    """Convert Animate.lean flat format to tree structure"""
    # Build goalId -> action mapping
    goal_to_action = {}
    for action in movie_json["actions"]:
        for ga in action["goalActions"]:
            goal_to_action[ga["startGoalId"]] = {
                "tactic": action["tacticText"],
                "state": ga["startState"],
                "results": ga["results"]
            }
    
    def build_tree(goal_id):
        if goal_id not in goal_to_action:
            return None
        
        info = goal_to_action[goal_id]
        parsed = parse_state(info["state"])
        
        children = []
        for result in info["results"]:
            child = build_tree(result["goal"]["goalId"])
            if child:
                children.append(child)
        
        return {
            "proof_state": parsed,
            "next_tactic": info["tactic"],
            "children": children
        }
    
    start_id = movie_json["startGoal"]["goalId"]
    return build_tree(start_id)


def run_animate(lean_file: str, theorem_name: str) -> dict:
    """Run lake exe Animate and return the parsed JSON"""
    # Get the script directory as the working directory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    cmd = ["lake", "exe", "Animate", lean_file, theorem_name]
    
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            cwd=script_dir,
            check=True
        )
        return json.loads(result.stdout)
    except subprocess.CalledProcessError as e:
        print(f"Error running Animate: {e}", file=sys.stderr)
        print(f"stderr: {e.stderr}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error parsing JSON output: {e}", file=sys.stderr)
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(
        description="Transform Lean proof to tree-structured JSON format",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Example usage:
  python transform_format.py --original_lean_file Input/NNG.lean --target_theorem NNG.mul_pow --output_file output.json
  python transform_format.py -i Input/test_file.lean -t test -o result.json
        """
    )
    
    parser.add_argument(
        "--original_lean_file", "-i",
        required=True,
        help="Path to the Lean file containing the theorem"
    )
    parser.add_argument(
        "--target_theorem", "-t",
        required=True,
        help="Name of the theorem to extract (e.g., 'NNG.mul_pow')"
    )
    parser.add_argument(
        "--output_file", "-o",
        required=True,
        help="Path to the output JSON file"
    )
    parser.add_argument(
        "--keep_intermediate", "-k",
        action="store_true",
        help="Keep the intermediate Animate JSON output (saved as <output_file>.intermediate.json)"
    )
    
    args = parser.parse_args()
    
    # Run Animate to get the original JSON
    print(f"Running Animate on {args.original_lean_file} for theorem {args.target_theorem}...", file=sys.stderr)
    movie_json = run_animate(args.original_lean_file, args.target_theorem)
    
    # Optional: save intermediate result
    if args.keep_intermediate:
        intermediate_file = args.output_file + ".intermediate.json"
        with open(intermediate_file, "w", encoding="utf-8") as f:
            json.dump(movie_json, f, indent=2, ensure_ascii=False)
        print(f"Intermediate JSON saved to {intermediate_file}", file=sys.stderr)
    
    # Convert to tree format
    tree = convert_to_tree(movie_json)
    
    # Write to output file
    with open(args.output_file, "w", encoding="utf-8") as f:
        json.dump(tree, f, indent=2, ensure_ascii=False)
    
    print(f"Transformed JSON saved to {args.output_file}", file=sys.stderr)


if __name__ == "__main__":
    main()