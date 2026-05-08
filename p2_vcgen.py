"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.

AI Attribution: Used Claude Code to implement wp() and verify(). I worked out the
wp rules from lecture notes first, then had Claude help with the Z3 substitute() calls
and getting the side VC generation right for while loops. Found the loop invariants
by tracing on paper (noted in [EXPLAIN] comments), then Claude helped encode them as ASTs.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return z3.Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return z3.And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return z3.Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []

def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """Compute wp(stmt, Q). For while loops, adds side VCs to the global list."""
    global side_vcs

    match stmt:
        case Assign(var, expr):
            # wp(x := E, Q) = Q[x ↦ E]
            return z3_substitute_var(Q, var, aexp_to_z3(expr))

        case Seq(s1, s2):
            # wp(S1; S2, Q) = wp(S1, wp(S2, Q))
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            # wp(if b then S1 else S2, Q) = (b → wp(S1, Q)) ∧ (¬b → wp(S2, Q))
            b = bexp_to_z3(cond)
            return z3.And(
                z3.Implies(b, wp(s1, Q)),
                z3.Implies(z3.Not(b), wp(s2, Q))
            )

        case While(cond, inv, body):
            # wp(while b inv I do S, Q) = I
            # Side VC 1 (preservation): I ∧ b → wp(S, I)
            # Side VC 2 (postcondition): I ∧ ¬b → Q
            I = bexp_to_z3(inv)
            b = bexp_to_z3(cond)
            wp_body_I = wp(body, I)
            side_vcs.append(("preservation", z3.Implies(z3.And(I, b), wp_body_I)))
            side_vcs.append(("postcondition", z3.Implies(z3.And(I, z3.Not(b)), Q)))
            return I

        case Assert(cond):
            # wp(assert P, Q) = P ∧ Q
            return z3.And(bexp_to_z3(cond), Q)

        case Assume(cond):
            # wp(assume P, Q) = P → Q
            return z3.Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """Verify {pre} stmt {post}. Computes wp, checks pre->wp and all side VCs."""
    global side_vcs
    side_vcs = []

    pre_z3 = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    # Compute weakest precondition
    wp_result = wp(stmt, post_z3)

    # Check main VC: pre → wp is valid (negate and check UNSAT)
    print(f"=== {label} ===")

    s = Solver()
    s.add(z3.Not(z3.Implies(pre_z3, wp_result)))
    main_result = s.check()
    main_valid = (main_result == unsat)
    print(f"  Main VC (pre → wp): {'Valid' if main_valid else 'INVALID'}")
    if not main_valid:
        print(f"    Counterexample: {s.model()}")

    # Check each side VC
    all_valid = main_valid
    for vc_name, vc_formula in side_vcs:
        s2 = Solver()
        s2.add(z3.Not(vc_formula))
        vc_result = s2.check()
        vc_valid = (vc_result == unsat)
        print(f"  Side VC ({vc_name}): {'Valid' if vc_valid else 'INVALID'}")
        if not vc_valid:
            print(f"    Counterexample: {s2.model()}")
            all_valid = False

    if all_valid:
        print(f"  ✓ {label}: Verified")
    else:
        print(f"  ✗ {label}: FAILED")
    print()


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{x == a ∧ y == b}  t:=x; x:=y; y:=t  {x == b ∧ y == a}"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{true}  if x<0 then r:=0-x else r:=x  {r >= 0 ∧ (r==x ∨ r==0-x)}"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
#
# For each program below, replace the `???` invariant with a correct one.
# [EXPLAIN] in a comment how you found each invariant and why it works.
# ============================================================================

def test_mult():
    """
    Program C1 — Multiplication by addition:
      {a >= 0}
      i := 0; r := 0;
      while i < a  invariant ???  do
        r := r + b;  i := i + 1;
      {r == a * b}
    """
    pre = Compare('>=', Var('a'), IntConst(0))

    # [EXPLAIN] ran the loop a few times: i goes 0,1,2,... and r goes 0,b,2b,...
    # so r = i*b at every step. need i<=a as a bound so when the loop exits
    # (i>=a), we can pin i=a exactly and get r=a*b.
    # checked preservation: after body, r'=r+b=(i+1)*b and i'=i+1<=a (since i<a).
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('*', Var('i'), Var('b'))),
        ImpAnd(
            Compare('>=', Var('i'), IntConst(0)),
            Compare('<=', Var('i'), Var('a'))
        )
    )

    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")


def test_add():
    """
    Program C2 — Addition by loop:
      {n >= 0 ∧ m >= 0}
      i := 0; r := n;
      while i < m  invariant ???  do
        r := r + 1;  i := i + 1;
      {r == n + m}
    """
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))

    # [EXPLAIN] traced it: i=0,r=n then i=1,r=n+1 then i=2,r=n+2... so r=n+i.
    # added i<=m as bound — at exit i>=m and i<=m gives i=m so r=n+m.
    # preservation works bc r+1 = n+(i+1) and i+1<=m when i<m.
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('+', Var('n'), Var('i'))),
        ImpAnd(
            Compare('>=', Var('i'), IntConst(0)),
            Compare('<=', Var('i'), Var('m'))
        )
    )

    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


def test_sum():
    """
    Program C3 — Sum of 1..n:
      {n >= 1}
      i := 1; s := 0;
      while i <= n  invariant ???  do
        s := s + i;  i := i + 1;
      {2 * s == n * (n + 1)}
    """
    pre = Compare('>=', Var('n'), IntConst(1))

    # [EXPLAIN] this one took a bit. traced: i=1,s=0 → i=2,s=1 → i=3,s=3 → i=4,s=6
    # noticed 2*s = 0,2,6,12 = 0*1, 1*2, 2*3, 3*4 = (i-1)*i. that's the relationship.
    # bound is i<=n+1 because loop condition is i<=n, so it exits at i=n+1.
    # then 2*s = n*(n+1) which is the postcondition.
    # preservation: 2*(s+i) = (i-1)*i + 2*i = i^2+i = i*(i+1) = ((i+1)-1)*(i+1). checks out.
    inv = ImpAnd(
        Compare('==',
                BinOp('*', IntConst(2), Var('s')),
                BinOp('*', BinOp('-', Var('i'), IntConst(1)), Var('i'))),
        ImpAnd(
            Compare('>=', Var('i'), IntConst(1)),
            Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1)))
        )
    )

    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
#
# The invariant below is WRONG (too weak). Your VCG should report failure.
# 1. Run it — which side VC fails?
# 2. [EXPLAIN] Give a concrete state where the invariant holds but the
#    postcondition does not.
# 3. Fix the invariant and re-verify.
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      {x >= 0 ∧ y > 0}
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK!
        r := r - y;  q := q + 1;
      {q * y + r == x ∧ 0 <= r ∧ r < y}

    The invariant q * y + r == x is correct but INCOMPLETE.
    It is missing a crucial conjunct. Find it.
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    # BUGGY invariant — intentionally too weak
    inv_buggy = Compare('==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'))

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_buggy, body)))
    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt, post, "Buggy Division (should FAIL)")

    # [EXPLAIN] the postcondition VC fails. the invariant q*y+r=x is preserved fine
    # (body just shuffles y between q and r) but at exit we need r>=0 and the
    # invariant doesn't say anything about r's sign.
    # counterexample: q=1, y=10, r=-5, x=5. invariant holds (10-5=5) and r<y
    # so loop exits, but r=-5 < 0 violates the postcondition.

    # FIXED invariant: add r >= 0
    inv_fixed = ImpAnd(
        Compare('==',
            BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
            Var('x')),
        Compare('>=', Var('r'), IntConst(0))
    )

    stmt_fixed = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_fixed, body)))

    verify(pre, stmt_fixed, post, "FIXED Division")


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
#
# Build the following program as an IMP AST:
#   x := x + 1;
#   if x > 0 then y := x * 2 else y := 0 - x;
# Postcondition: {y > 0}
#
# 1. Call wp() to get the weakest precondition. Print the Z3 formula.
# 2. Use Z3 to check whether each of the following is a valid precondition:
#    - {x >= 0}
#    - {x >= -1}
#    - {x == -1}
#    For each, print whether it's valid and add a comment explaining why.
# ============================================================================

def test_wp_derivation():
    """
    Part (a): Use your VCG to compute wp, then check candidate preconditions.
    """
    global side_vcs
    side_vcs = []

    print("=== Part (a): WP Derivation ===")

    # Build the IMP AST
    stmt = Seq(
        Assign('x', BinOp('+', Var('x'), IntConst(1))),
        If(Compare('>', Var('x'), IntConst(0)),
           Assign('y', BinOp('*', Var('x'), IntConst(2))),
           Assign('y', BinOp('-', IntConst(0), Var('x'))))
    )
    post = Compare('>', Var('y'), IntConst(0))

    # Compute wp
    wp_result = wp(stmt, bexp_to_z3(post))
    print(f"  wp = {wp_result}")
    print(f"  wp (simplified) = {simplify(wp_result)}")
    print()

    # Check candidate preconditions
    candidates = [
        ("x >= 0",  z3_var('x') >= 0),
        ("x >= -1", z3_var('x') >= -1),
        ("x == -1", z3_var('x') == -1),
    ]
    for name, pre_cand in candidates:
        s = Solver()
        s.add(Not(Implies(pre_cand, wp_result)))
        result = s.check()
        valid = (result == unsat)
        print(f"  {name}: {'VALID' if valid else 'INVALID'}")
        if not valid:
            print(f"    Counterexample: {s.model()}")

    # [EXPLAIN]
    # x>=0: VALID — after x:=x+1 we get x>=1, so x>0 and we go to then-branch,
    #   y=x*2 which is at least 2, so y>0 always holds.
    # x>=-1: INVALID — try x=-1: after increment x=0, which is NOT >0, so we go
    #   to else-branch and y=0-0=0. but postcondition needs y>0. fails.
    # x==-1: INVALID — same thing, x=-1 is the counterexample.
    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
