"""
CS292C Homework 2 — Problem 5 (Bonus): Verified Skill Composition (10 points)
===============================================================================
Verify that two sequentially composed agent skills maintain a filesystem
invariant, then show how a composition bug breaks the invariant.

AI Attribution: Used Claude Code to set up the Z3 array encoding for the filesystem
model and the ForAll quantifiers for the frame conditions. The skeleton already had
most of the structure, I just needed to uncomment and wire up the solver checks.
The [EXPLAIN] for part (c) is from my own experience using Claude Code.
"""

from z3 import *


# ============================================================================
# Filesystem Model
#
# We model the filesystem as a Z3 array: Array(Int, Int)
#   - Index = file path ID (integer)
#   - Value = content hash (integer)
#
# Two paths are special:
#   INPUT_FILE = 0   (the file Skill A reads)
#   OUTPUT_FILE = 1  (the file Skill B writes to)
# ============================================================================

INPUT_FILE = 0
OUTPUT_FILE = 1


# ============================================================================
# Part (a): Verify correct composition — 4 pts
# ============================================================================

def verify_correct_composition():
    print("=== Part (a): Correct Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    # Skill A postcondition: filesystem unchanged
    skill_A_post = fs_after_A == fs_initial

    # Skill B postcondition: only OUTPUT_FILE changes
    skill_B_post = And(
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Composed postcondition to verify
    composed_post = And(
        # Input file preserved
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        # Output written
        Select(fs_final, OUTPUT_FILE) == result_content,
        # Nothing else changed
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Check that (skill_A_post ∧ skill_B_post) → composed_post is valid.
    # Negate and check UNSAT.
    s = Solver()
    s.add(skill_A_post)
    s.add(skill_B_post)
    s.add(Not(composed_post))

    result = s.check()
    if result == unsat:
        print("  ✓ Composed postcondition VERIFIED (UNSAT — no counterexample)")
    else:
        print(f"  ✗ Composition FAILED: {s.model()}")
    print()


# ============================================================================
# Part (b): Buggy composition — 3 pts
# ============================================================================

def verify_buggy_composition():
    print("=== Part (b): Buggy Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    skill_A_post = fs_after_A == fs_initial

    # BUGGY Skill B: writes to INPUT_FILE instead of OUTPUT_FILE
    buggy_B_post = And(
        Select(fs_final, INPUT_FILE) == result_content,  # ← BUG
        ForAll([p], Implies(p != INPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Same composed postcondition as before
    composed_post = And(
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Check: the composed postcondition should FAIL.
    s = Solver()
    s.add(skill_A_post)
    s.add(buggy_B_post)
    s.add(Not(composed_post))

    result = s.check()
    if result == sat:
        m = s.model()
        print("  ✗ Composed postcondition FAILS (SAT — counterexample found)")
        print(f"    Model: {m}")
        print()
        # Show what went wrong
        print("  Explanation:")
        print("    Skill B wrote result_content to INPUT_FILE (path 0) instead of OUTPUT_FILE (path 1).")
        print("    The composed postcondition requires INPUT_FILE to be unchanged,")
        print("    but Skill B overwrote it. The input file is now corrupted.")
    else:
        print("  ✓ No counterexample found (unexpected!)")
    print()


# ============================================================================
# Part (c): Real-world connection — 3 pts
#
# [EXPLAIN] ive seen this happen with claude code — one tool reads a config
# file to figure out the project layout, then another tool reformats or edits
# that same file. the first tool's assumptions about the file contents are now
# wrong but it doesnt know. basically the second tool violated the "frame"
# (what it promised not to touch). a monitor would need to track which files
# each skill read and block later skills from writing to those paths.
# ============================================================================


# ============================================================================
if __name__ == "__main__":
    verify_correct_composition()
    verify_buggy_composition()
