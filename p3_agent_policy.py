"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1-R5.
    Using default-deny: allowed = (some permit rule matches) AND (no deny rule fires).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # Permit conditions (when access is granted):
    # R1: Viewers may only file_read non-sensitive resources
    # R2: Developers may file_read anything, file_write if owner or in sandbox
    # R3: Admins may use any tool on any resource
    permit = Or(
        # R3: Admin — any tool, any resource
        role(u) == ADMIN,
        # R2: Developer — file_read anything, or file_write with ownership/sandbox
        And(role(u) == DEVELOPER, Or(
            t == FILE_READ,
            And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r)))
        )),
        # R1: Viewer — file_read non-sensitive only
        And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r)))
    )

    # Deny conditions (override permits):
    # R4: Nobody may shell_exec on sensitive resources
    # R5: network_fetch only on sandbox resources
    deny = Or(
        And(t == SHELL_EXEC, is_sensitive(r)),     # R4
        And(t == NETWORK_FETCH, Not(in_sandbox(r)))  # R5
    )

    # Biconditional: allowed iff permitted and not denied
    constraints.append(ForAll([u, t, r],
        allowed(u, t, r) == And(permit, Not(deny))
    ))

    # Constrain roles to valid values
    constraints.append(ForAll([u], Or(
        role(u) == ADMIN, role(u) == DEVELOPER, role(u) == VIEWER
    )))

    # Constrain tools to valid values
    constraints.append(ForAll([u, t, r], Implies(
        allowed(u, t, r),
        And(t >= 0, t <= 3)
    )))

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    # [EXPLAIN] SAT — R2 says devs can write if they own it OR its in sandbox.
    # since its in the sandbox, ownership doesnt matter. R4 only blocks shell_exec not writes.
    query("Q1: Developer writes sensitive, non-owned, sandbox file?",
          policy,
          [role(u) == DEVELOPER,
           is_sensitive(r) == True,
           owner(r) != u,
           in_sandbox(r) == True,
           allowed(u, FILE_WRITE, r) == True])

    # Q2: Can an admin network_fetch outside the sandbox?
    # [EXPLAIN] UNSAT — R5 says net_fetch only works in sandbox, period. even admins
    # can't do it because the deny rule overrides R3.
    query("Q2: Admin network_fetch outside sandbox?",
          policy,
          [role(u) == ADMIN,
           in_sandbox(r) == False,
           allowed(u, NETWORK_FETCH, r) == True])

    # Q3: Any role that can shell_exec on a sensitive resource?
    # [EXPLAIN] UNSAT — R4 says nobody can shell_exec on sensitive stuff, no exceptions.
    query("Q3: Any role shell_exec on sensitive resource?",
          policy,
          [is_sensitive(r) == True,
           allowed(u, SHELL_EXEC, r) == True])

    # Q4: Remove R4 — what becomes possible?
    # Build modified policy WITHOUT the shell_exec deny
    u2 = Const('u2', User)
    r2 = Const('r2', Resource)
    t2 = Int('t2')

    permit_no_r4 = Or(
        role(u2) == ADMIN,
        And(role(u2) == DEVELOPER, Or(
            t2 == FILE_READ,
            And(t2 == FILE_WRITE, Or(owner(r2) == u2, in_sandbox(r2)))
        )),
        And(role(u2) == VIEWER, t2 == FILE_READ, Not(is_sensitive(r2)))
    )
    # Only R5 in deny now (R4 removed)
    deny_no_r4 = And(t2 == NETWORK_FETCH, Not(in_sandbox(r2)))

    allowed_no_r4 = Function('allowed_no_r4', User, IntSort(), Resource, BoolSort())
    policy_no_r4 = [
        ForAll([u2, t2, r2],
            allowed_no_r4(u2, t2, r2) == And(permit_no_r4, Not(deny_no_r4))),
        ForAll([u2], Or(role(u2) == ADMIN, role(u2) == DEVELOPER, role(u2) == VIEWER))
    ]

    # [EXPLAIN] without R4 theres nothing stopping admins from running shell_exec on
    # sensitive resources — R3 just lets them do everything.
    query("Q4: Without R4, admin shell_exec on sensitive resource?",
          policy_no_r4,
          [role(u2) == ADMIN,
           is_sensitive(r2) == True,
           allowed_no_r4(u2, SHELL_EXEC, r2) == True])


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
# ============================================================================

def part_c():
    """
    Model a 2-step escalation. R6: devs can shell_exec non-sensitive sandbox resources.
    Attack: step 1 shell_exec changes r2's sensitivity flag, step 2 shell_exec on r2.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    u = Const('u', User)
    r1 = Const('r1', Resource)
    r2 = Const('r2', Resource)

    # Two time steps: sensitivity can change between them
    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after = Function('is_sensitive_after', Resource, BoolSort())

    # R6 for developers: shell_exec on non-sensitive sandbox resources
    # We check allowed_at for each step using the sensitivity at that time

    s = Solver()

    # The developer
    s.add(role(u) == DEVELOPER)

    # r1 and r2 are distinct resources
    s.add(r1 != r2)

    # r2 was originally sensitive
    s.add(is_sensitive_before(r2) == True)

    # Step 1: developer shell_exec on r1
    # r1 is non-sensitive and in sandbox — allowed by R6
    s.add(is_sensitive_before(r1) == False)
    s.add(in_sandbox(r1) == True)

    # Side effect of step 1: r2 becomes non-sensitive
    # (e.g., shell_exec modified a config file that controls sensitivity)
    s.add(is_sensitive_after(r2) == False)
    # r1's sensitivity doesn't change
    s.add(is_sensitive_after(r1) == is_sensitive_before(r1))

    # Step 2: developer shell_exec on r2
    # Using the AFTER sensitivity, r2 is now non-sensitive and in sandbox
    s.add(in_sandbox(r2) == True)

    # R4 check at step 2 using AFTER sensitivity: shell_exec blocked only if sensitive
    # Since is_sensitive_after(r2) == False, R4 does NOT block it
    # R6 allows developer shell_exec on non-sensitive sandbox resources
    step2_r4_blocks = And(is_sensitive_after(r2))  # R4 would block if sensitive
    step2_r6_allows = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_after(r2)),
        in_sandbox(r2)
    )

    # The attack succeeds: step 2 is allowed despite r2 being originally sensitive
    s.add(step2_r6_allows)
    s.add(Not(step2_r4_blocks))  # R4 doesn't block (sensitivity was changed)

    result = s.check()
    print(f"  Escalation possible: {result}")
    if result == sat:
        print(f"  Model: {s.model()}")
        print()
        print("  Attack trace:")
        print("    Step 1: developer shell_exec on r1 (non-sensitive, sandbox) → ALLOWED by R6")
        print("           Side effect: r2's sensitivity changed from True to False")
        print("    Step 2: developer shell_exec on r2 (now non-sensitive, sandbox) → ALLOWED by R6")
        print("           R4 bypassed because r2 is no longer marked sensitive!")
    print()

    # Fix: Add a constraint that sensitivity flags are IMMUTABLE — shell_exec cannot
    # change them. Alternatively, check against the ORIGINAL sensitivity.
    print("  Proposed fix: Check shell_exec against ORIGINAL sensitivity, not current.")
    print("  Implementation: Add constraint that sensitivity is monotonic (once sensitive, always sensitive).")

    s_fix = Solver()
    s_fix.add(role(u) == DEVELOPER)
    s_fix.add(r1 != r2)
    s_fix.add(is_sensitive_before(r2) == True)
    s_fix.add(is_sensitive_before(r1) == False)
    s_fix.add(in_sandbox(r1) == True)
    s_fix.add(in_sandbox(r2) == True)

    # FIX: Sensitivity is monotonic — once sensitive, always sensitive
    r_any = Const('r_any', Resource)
    s_fix.add(ForAll([r_any], Implies(
        is_sensitive_before(r_any),
        is_sensitive_after(r_any)
    )))

    # Now check if step 2 can still bypass R4
    s_fix.add(is_sensitive_after(r2) == False)  # attacker tries to make r2 non-sensitive

    fix_result = s_fix.check()
    print(f"\n  After fix — escalation possible: {fix_result}")
    if fix_result == unsat:
        print("  ESCALATION BLOCKED")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
