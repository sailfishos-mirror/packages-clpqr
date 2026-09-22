# CLP(Q,R) — design and implementation notes

This document describes the design of the SWI-Prolog `library(clpq)` and
`library(clpr)` solvers as they are implemented in this package.  It was
written by reading the sources together with the literature the code is
derived from, and by probing the running system.  Its purpose is to make the
package maintainable again: the libraries have had no maintainer for a long
time and were, until the test suite that accompanies this document, almost
completely untested.

* [1. Provenance and literature](#1-provenance-and-literature)
* [2. User-visible interface](#2-user-visible-interface)
* [3. Module map](#3-module-map)
* [4. Data representation](#4-data-representation)
* [5. Constraint processing pipeline](#5-constraint-processing-pipeline)
* [6. The linear equality solver](#6-the-linear-equality-solver)
* [7. The inequality solver](#7-the-inequality-solver)
* [8. Disequations](#8-disequations)
* [9. Non-linear constraints](#9-non-linear-constraints)
* [10. Optimisation](#10-optimisation)
* [11. Branch and bound](#11-branch-and-bound)
* [12. Projection and answer presentation](#12-projection-and-answer-presentation)
* [13. CLP(Q) versus CLP(R)](#13-clpq-versus-clpr)
* [14. Known problems](#14-known-problems)
* [15. Testing](#15-testing)


## 1. Provenance and literature

The code is a port of Christian Holzbaur's SICStus `clp(q,r)`, made by Leslie
De Koninck at K.U. Leuven as part of his master's thesis (supervised by Bart
Demoen, daily advisor Tom Schrijvers).  The primary reference for the intended
*behaviour* is

> Holzbaur, C.  *OFAI clp(q,r) Manual, Edition 1.3.3.*  Austrian Research
> Institute for Artificial Intelligence, Vienna, TR-95-09, 1995.
> <https://ofai.at/papers/oefai-tr-95-09.pdf>

That manual describes the implementation as three components, and the code
still has exactly that shape:

1. "A polynomial normal form expression simplification mechanism" — `nf_q.pl`
   / `nf_r.pl`.
2. "A solver for linear equations" — `bv_q.pl` / `bv_r.pl`, after

   > Holzbaur, C.  *A Specialized, Incremental Solved Form Algorithm for
   > Systems of Linear Inequalities.*  1992.

3. "A simplex algorithm to decide linear inequalities" — `ineq_q.pl` /
   `ineq_r.pl` plus the pivoting machinery in `bv_*.pl`, after Holzbaur 1994.

The background for the rest:

* Jaffar, J., Michaylov, S., Stuckey, P.J., Yap, R.H.C.  *The CLP(R) Language
  and System.*  ACM TOPLAS 14(3), 1992.  Source of the *isolation axioms*
  used to wake delayed non-linear constraints, and of the "Monash" example
  suite and `#(Const)` symbolic constants that `nf_r.pl` still supports.
* The bounded-variable simplex (each variable carries its own lower/upper
  bound instead of being represented by a slack row) is the textbook
  *bounded-variable* form, e.g. Chvátal, *Linear Programming*, 1983.
* Answer projection uses Fourier–Motzkin elimination with redundancy removal;
  see Imbert, J-L.  *Fourier's Elimination: Which to Choose?*, PPCP 1993, and
  Lassez, J-L., Lassez, C.  *Quantifier Elimination for Conjunctions of Linear
  Constraints via a Convex Hull Algorithm*, 1992.  The manual states plainly:
  "The current clp(Q,R) version uses a Fourier-Motzkin algorithm for the
  projection of linear inequalities."
* De Koninck, L., Schrijvers, T., Demoen, B.  *INCLP(R) — Interval-based
  nonlinear constraint solving over the reals*, 2006, is the follow-up work
  that handles what this solver deliberately does not.

Two design decisions from the manual are worth repeating because they explain
a lot of the code:

* **Only linear constraints are solved.**  "The clp(Q,R) system is restricted
  to deal with linear constraints because the decision algorithms for general
  nonlinear constraints are prohibitively expensive to run."  Non-linear
  constraints are *collected faithfully* and retried whenever they might have
  become linear.
* **Q and R are the same algorithm over a different number field.**  CLP(Q)
  computes with unbounded rationals and is exact; CLP(R) computes with IEEE
  doubles and replaces every exact comparison with a comparison against a
  fixed epsilon of `1.0e-10`.


## 2. User-visible interface

Both libraries export the same predicates, except that `bb_inf/4` exists only
in CLP(Q) and `bb_inf/5` only in CLP(R).

| Predicate | Meaning |
| --- | --- |
| `{}/1` | Add constraints to the store |
| `entailed/1` | Constraint follows from the store |
| `inf/2`, `inf/4` | Infimum of an expression (`/4` also returns a vertex) |
| `sup/2`, `sup/4` | Supremum of an expression |
| `minimize/1`, `maximize/1` | Optimise *and* bind the expression to the optimum |
| `bb_inf/3`, `bb_inf/4` (Q), `bb_inf/5` (R) | Mixed integer infimum |
| `dump/3` | Project the store onto a list of variables |
| `ordering/1` | Influence the shape of the projected answer |
| `clp_type/2` | Which solver owns a variable |

`library(clpq)` and `library(clpr)` export the same predicate names, so a
single module can only import one of them; use module qualification
(`clpq:{...}`) to mix them in one file.  Mixing CLP(Q) and CLP(R) constraints
on the *same variable* raises a `permission_error`.

### Constraint syntax

```
Constraints ::= Constraint | Constraint , Constraints | Constraint ; Constraints
Constraint  ::= Expr < Expr | Expr > Expr | Expr =< Expr | <=(Expr,Expr)
              | Expr >= Expr | Expr =\= Expr | Expr =:= Expr | Expr = Expr
Expr        ::= Var | Number | +Expr | -Expr | Expr+Expr | Expr-Expr
              | Expr*Expr | Expr/Expr | abs(Expr) | sin(Expr) | cos(Expr)
              | tan(Expr) | exp(Expr,Expr) | pow(Expr,Expr) | Expr^Expr
              | min(Expr,Expr) | max(Expr,Expr)
              | #(Const)                                   % CLP(R) only
```

Note what is *not* accepted, because it is a frequent source of surprise:

* `**` is not an operator of the language — only `^`, `pow/2` and `exp/2`.
* `rdiv/2` is not accepted by CLP(Q); write `1/3`, which CLP(Q) evaluates
  exactly to `1r3`.
* Anything else raises `type_error(clpq_expression, T)` resp.
  `type_error(clpr_expression, T)`.
* `sqrt/1`, `log/1`, `exp/1` (unary) are not part of the language.

Plain unification is equivalent to an equality constraint: `X = Y`,
`{X = Y}` and `{X =:= Y}` all post the same constraint, because the solver
installs an `attr_unify_hook/2`.

### Semantics of the less obvious predicates

`entailed(C)` is implemented as `negate(C, Cn), \+ {Cn}`: the constraint is
entailed exactly when adding its negation makes the store unsatisfiable.  It
therefore never changes the store.

`inf/2` and `sup/2` do not change the store either — the extremal vertex is
reached by pivoting, the value is captured in a global variable and the pivots
are then undone by backtracking.  `minimize/1`/`maximize/1` exist separately
(rather than as `inf(E,E)`) precisely because they *do* want to stay at the
optimal vertex; see the long comment above `minimize/1` in `bv_q.pl`.

`dump(+Target, +NewVars, -Constraints)` projects the store onto `Target`,
which must be a list of *unbound* variables, and renames them to `NewVars`.
The store is not modified: `dump/3` runs the destructive projection inside a
failure-driven loop and recovers the result with `nb_setarg/3`.


## 3. Module map

```
clpq.pl / clpr.pl        user entry point, toplevel residual printing
├── clpq/nf_q.pl         {}/1, entailed/1, polynomial normal form
├── clpq/store_q.pl      sparse linear-form arithmetic
├── clpq/bv_q.pl         equality solver, simplex pivoting, optimisation, dump
├── clpq/ineq_q.pl       inequality solver (bound updates)
├── clpq/fourmotz_q.pl   Fourier–Motzkin elimination (projection)
├── clpq/bb_q.pl         branch and bound (bb_inf/3,4)
├── clpq/itf_q.pl        attr_unify_hook back end (type/bound checks)
└── clpqr/…              solver-independent parts, shared by Q and R
    ├── itf.pl           clpqr_itf attribute + attr_unify_hook/2
    ├── class.pl         clpqr_class attribute (connected component)
    ├── geler.pl         clpqr_geler attribute (delayed non-linear goals)
    ├── ordering.pl      ordering/1, priority graph, topological sort
    ├── project.pl       project_attributes/2 driver
    ├── redund.pl        redundant-bound elimination
    ├── dump.pl          dump/3, attribute_goals//1
    └── highlight.pl     library(prolog_colour) support
```

`clpr/` mirrors `clpq/` file for file.  The two trees are *not* generated from
a common source; they are independent copies that have drifted apart (see
[§13](#13-clpq-versus-clpr)).

The shared `clpqr/` modules dispatch on the solver by inspecting the first
argument of the `clpqr_itf` attribute and calling the right module explicitly:

```prolog
fm_elim(clpq,Avs,Tvs,Pivots) :- fourmotz_q:fm_elim(Avs,Tvs,Pivots).
fm_elim(clpr,Avs,Tvs,Pivots) :- fourmotz_r:fm_elim(Avs,Tvs,Pivots).
```

This is why `clpqr/*.pl` can be loaded once while both solvers are active.


## 4. Data representation

### 4.1 Polynomial normal form (`nf`)

`nf/2` in `nf_*.pl` turns a user expression into an ordered sum of monomials:

```
Nf   ::= list of v(K, Powers)          % implicit sum, ordered by Powers
Powers ::= list of Base^Exp            % implicit product, ordered by Base
```

* `v(K,[])` is the scalar `K`; the empty list `[]` is the number 0.
* A variable `X` normalises to `[v(1,[X^1])]`.
* `Powers` is kept sorted on the standard order of `Base`, exponents of equal
  bases are added (`pmerge/3`), and a zero exponent removes the factor.
* Monomials with equal `Powers` are added (`nf_add/3`), and a zero coefficient
  removes the monomial.  The ordering `[] < [X^1] < …` makes the scalar, if
  present, the first element, which `split/3` exploits.
* A `Base` need not be a variable: `sin(Nf)`, `exp(Nf,Nf)`, `min(Nf,Nf)`,
  `abs(Nf)` and the "undigested" quotient `A/B` all appear as bases.  This is
  what makes the representation closed under the non-linear functions.

Integer powers of sums are expanded with the binomial theorem (`binom/3`),
which the header comment notes is roughly 4× faster than iterated
multiplication for `(1+X+Y+Z)^15`.

`linear/1` recognises a normal form in which every monomial is `v(_,[])` or
`v(_,[X^1])` with `X` a variable.  Only such normal forms reach the linear
solver.

### 4.2 Linear form (`lin`)

Once a normal form is known to be linear it is *dereferenced* into the solver's
working representation by `deref/2`:

```
Lin ::= [ I, R | Hom ]
Hom ::= list of l(X*K, Ord)            % ordered on Ord
```

* `I` is the inhomogeneous part (a constant).
* `R` is the *rhs* accumulator: the sum over `Hom` of `K` times the currently
  *active bound* of `X`.  `R+I` is therefore the current value of the variable
  this row defines.  Keeping `R` incrementally is what makes bound checking
  O(1) instead of O(row length) — see `rcb/3`.
* `Ord` is the variable's ordering key (§4.4).  `Hom` is sorted on it, so all
  the vector operations in `store_*.pl` (`add_linear_ff/5`, `add_linear_f1/4`,
  `add_linear_11/3`, `nf_substitute/4`, `delete_factor/4`) are linear merges.

A variable `X` that has never been seen gets the row `[0,0,l(X*1,Ord)]`, i.e.
`X = X`; it is *independent*.  A variable whose row has more than one term is
*dependent* (basic).

### 4.3 Attributes

Three attributes are used.  All three live in modules named after the
attribute, which is how `attr_unify_hook/2` and `attribute_goals//1` are
found.

**`clpqr_itf`** — the main per-variable record, an 11-argument term:

| # | Contents | Notes |
| --- | --- | --- |
| 1 | `clpq` or `clpr` | never changes; used for solver dispatch |
| 2 | `type(T)` or `n` | bound state, see §7.1 |
| 3 | `strictness(S)` or `n` | 2 bits, see §7.1 |
| 4 | `lin(Lin)` or `n` | the row for this variable |
| 5 | `order(Ord)` or `n` | ordering key |
| 6 | `class(C)` or `n` | connected component |
| 7 | — | **unused**; never read, never written |
| 8 | `nonzero` or `n` | variable is constrained `=\= 0` |
| 9 | `target` or `n` | projection: variable must survive |
| 10 | `keep_indep` or `n` | projection: do not eliminate |
| 11 | `keep` or `n` | projection: pivot partner, do not drop |

Arguments 2–6 are set to `n` together (`drop_lin_atts/1`, `drop_dep_one/1`)
when a variable becomes irrelevant to the linear store.  Arguments 9–11 are
only meaningful during projection.

**`clpqr_class`** — `class(CLP, All, AllT, Basis, Prio)` on a fresh variable
that acts as the identity of a connected component ("class") of the linear
store:

* `All`/`AllT` is an open (difference) list of every variable in the class.
* `Basis` is the list of dependent variables that currently have a bound
  (the simplex basis).
* `Prio` is the user's ordering graph for this class (§12.3).

Merging two classes is done by *unifying the class variables*: the
`attr_unify_hook/2` in `class.pl` appends the two variable lists by binding
the open tail of one to the head of the other, concatenates the bases and
combines the priority graphs.  This makes union-find essentially free.

**`clpqr_geler`** — `g(CLP, goals(Conj), Flag)` holding the delayed non-linear
goals that mention this variable (§9).

### 4.4 Variable ordering

Every variable in the linear store carries an `order(Ord)` key, and rows are
sorted on it.  The trick is that `Ord` is normally an *unbound fresh
variable*: `compare/3` on two unbound variables is stable within a session and
reflects creation order, so ordering is free and total.  `ordering/1` and
projection can bind these variables to small integers to force a particular
arrangement, and integers sort before variables, so explicitly ordered
variables come first.

`renormalize/2` in `store_*.pl` rebuilds a row after orders have been bound
or variables have been unified, because the sort invariant can be broken by
both.


## 5. Constraint processing pipeline

`{C}` (in `nf_*.pl`) is a small dispatcher:

| Input | Action |
| --- | --- |
| `var` | `instantiation_error` |
| `(A,B)` | `{A}, {B}` |
| `(A;B)` | `{A} ; {B}` — needed by `entailed/1` |
| `L < R` | `nf(L-R,Nf), submit_lt(Nf)` |
| `L > R` | `nf(R-L,Nf), submit_lt(Nf)` |
| `L =< R`, `<=(L,R)` | `nf(L-R,Nf), submit_le(Nf)` |
| `L >= R` | `nf(R-L,Nf), submit_le(Nf)` |
| `L =:= R`, `L = R` | `nf(L-R,Nf), submit_eq(Nf)` |
| `L =\= R` | `nf(L-R,Nf), submit_ne(Nf)` |
| other | `type_error(clpq_constraint, C)` |

Every constraint is thus normalised to a comparison of a polynomial with 0.
The `submit_*` predicates then perform a case analysis on the *shape* of the
normal form, in increasing order of cost.  `submit_eq/1` is representative:

```
[]                     trivially true
[v(K,[])]              K =:= 0, i.e. fail
[v(_,[X^P])], P>0      X = 0
[v(_,[NL^1])]          NL invertible  =>  X = inv(NL)(0)
[v(I,[]),v(K,[X^P])]   P = 1: X = -I/K;  P = -1: X = -K/I
[v(I,[]),v(K,[NL^P])]  NL invertible  =>  recurse
linear                 log_deref/4 then solve/1
otherwise              geler/3 (delay)
```

`log_deref/4` converts a normal form to a linear form by divide and conquer
(halving the list) rather than left to right, so that merging `n` rows costs
`O(n log n)` merges rather than `n` merges against a growing accumulator.
The same logarithmic pattern recurs in `renormalize_log/4`, `nf_mul_log/6`,
`nf_mul_factor_log/5` and `repair_log/4`.


## 6. The linear equality solver

`solve/1` in `bv_*.pl` solves `Lin = 0`.  It implements the incremental
solved-form algorithm of Holzbaur 1992: the store is kept in *reduced row
echelon form*, i.e. every dependent variable is defined by a row over
independent variables only.

Given a row to add, `sd/7` scans its homogeneous part and simultaneously

* collects the set of distinct classes the row touches (`ord_add_element/3`),
* collects the variables that have no class yet, and
* selects the variable to solve for, by *preference category*:

| Category | Variable | Why |
| --- | --- | --- |
| 1 | no class, no bounds | cheapest: nothing to repair |
| 2 | has class, no bounds | needs back-substitution in its class |
| 3 | no class, bounded | new basis entry, basis must be reconsidered |
| 4 | has class, bounded | both of the above |

`isolate/3` rewrites `Lin = 0` into `Selected = Lin1` and the four categories
then differ in how much work follows:

* **1** — just store `Lin1` as the row of `Selected` and attach the new
  variables to a fresh class.
* **2** — back-substitute `Selected` in every row of its class.  If the row
  touched exactly one class (`ClassesUniq = [_]`) the rank increases, and
  `bs_collect_bindings/5` can additionally harvest *implied values*: any row
  that collapses to `X = Inhom` yields a binding.
* **3**/**4** — as above, plus `deactivate_bound/2`, `basis_add/2`,
  `undet_active/1` and finally `rcbl/3` to re-establish feasibility of the
  whole basis.

Bindings are collected and applied at the very end (`export_binding/1`) rather
than during back-substitution, because binding a variable in the middle of the
traversal would trigger `attr_unify_hook/2` re-entrantly.

`solve_x/2` and `solve_ord_x/3` are variants that solve for a *given*
variable; they are used by the unification hook, which must eliminate the
variable that is about to be bound.


## 7. The inequality solver

### 7.1 Bounds and strictness

A variable's bound state is the `type(T)` field, with a capital letter marking
the *active* bound (the bound the variable currently sits on):

```
t_none               no bounds
t_l(L)   t_u(U)      inactive lower / upper bound
t_L(L)   t_U(U)      active lower / upper bound
t_lu(L,U)            two inactive bounds
t_Lu(L,U)            active lower, inactive upper
t_lU(L,U)            inactive lower, active upper
```

Only *independent* variables have an active bound; the `R` field of a
dependent variable's row is the weighted sum of the active bounds of the
independent variables it is defined over.

Strictness is two bits in `strictness(S)`: bit 1 (`S /\ 2`) marks a strict
lower bound, bit 0 (`S /\ 1`) a strict upper bound.  `ilb/3`, `iub/3` (check a
value), `llb//3`, `lub//3` (emit a constraint) and `dump_strict/4` all decode
it.

### 7.2 Adding an inequality

`ineq/4` in `ineq_*.pl` again dispatches on shape:

* `I < 0` with no variables — evaluate.
* `K*X + I < 0` — a *bound update* on a single variable.  This is the common
  case and it never introduces a slack variable.
* otherwise `ineq_more/4`:
  * if the row contains an *unconstrained* variable `U` (`unconstrained/4`
    finds one of category ≤ 2), solve the row for `U` against a fresh
    slack variable `S ≥ 0` and back-substitute.  This can never fail and
    never implies a value, because nothing constrains `U`.
  * otherwise create `S = Lin` with `S ≤ 0` (`var_with_def_intern/4`), add
    `S` to the basis, activate bounds (`determine_active_dec/1`) and call
    `reconsider/1`.

The bound-update predicates form a 4×8 table named by the mnemonic
*u(d|i)(l|u)(s?)* — **u**pdate **d**ependent/**i**ndependent
**l**ower/**u**pper, `s` for strict:

| | non-strict | strict |
| --- | --- | --- |
| dependent lower | `udl/5` | `udls/5` |
| dependent upper | `udu/5` | `udus/5` |
| independent lower | `uil/5` | `uils/5` |
| independent upper | `uiu/5` | `uius/5` |

Each has one clause per incoming `type(T)`, and each clause must decide
between: ignore the new bound (weaker), tighten it, detect that lower and
upper have met (`solve_bound/2`, which turns the pair into an equality), or
detect infeasibility.  Tightening the *active* bound of an independent
variable additionally shifts the `R` field of every row in the class by
`Delta` (`backsubst_delta/4`), or pivots first if the most constraining row
would be violated.

### 7.3 Restoring feasibility

`lb/3` and `ub/3` scan the basis for the *most constraining row* — the row
that limits how far a given independent variable may move.  `lb_inner/5` and
`ub_inner/5` compute, from a basic row and the coefficient of the variable in
it, how much the variable may move before that row's bound is violated.
Infeasible rows are deliberately excluded from the candidate set (`Lb =< 0`,
`Ub >= 0`); the comment in the source is emphatic: "We must NOT consider
infeasible rows as candidates to leave the basis!"

`rcb/3` finds a basic variable that is outside or at its bound and calls
`inc_step/2` or `dec_step/2`, which scan the row left to right for a variable
that can be moved in the desired direction.  The result is one of

* `applied` — a pivot was performed, try again;
* `optimum` — the row cannot be improved.  If the optimum *meets* the bound,
  the bound is an implied equality, which is fed back into `solve/5`;
* `unlimited(V,T)` — the row is unbounded in the needed direction, so the
  culprit can simply be pivoted out (`rcbl_unl/7`).

`rcbl/3` iterates this over the whole basis, threading the collected bindings.
The `*_cont` variants (`dec_step_cont/4`, `inc_step_cont/4`) additionally
maintain the *continuation*, i.e. the not-yet-examined part of the basis, so
that a pivot which swaps a variable into the basis updates the work list
(`replace_in_cont/4`).

Note that this is a pure feasibility (phase-I-like) procedure, not an
optimisation: no objective row exists until `inf/2` creates one.


## 8. Disequations

`X =\= Y` cannot be expressed in the simplex tableau, so `solve_=\=/1`

1. dereferences the normal form to `Lind`,
2. if it is ground, checks it is not 0,
3. otherwise creates a fresh variable `Nz` defined by `Nz = Lind` and sets
   argument 8 of its `clpqr_itf` attribute to `nonzero`.

Nothing else happens until `Nz` would be bound: `verify_nonzero/2` in
`itf_*.pl` then checks `Y =\= 0` for a number, or propagates the `nonzero`
mark to the variable `Y` is unified with.  The check is therefore *passive* —
it detects a violation at binding time, not at constraint time, which is
exactly what the OFAI manual's "Why disequations" section (the all-different
squared-rectangle tiling example) needs.

`dump_nz//3` renders the mark back as `Sum =\= I` for answer presentation.


## 9. Non-linear constraints

### 9.1 Delaying

When `submit_*` finds a normal form that is not linear it calls
`geler(CLP, Vars, Goal)`, which attaches `run(Mutex, Goal)` to the
`clpqr_geler` attribute of every variable in `Vars`.  The shared `Mutex`
ensures the goal runs *once* even though it is reachable from several
variables — `run/2` succeeds immediately if `Mutex` is already bound.

The delayed goals are one of `resubmit_eq/1`, `resubmit_lt/1`,
`resubmit_le/1`, `resubmit_ne/1` or `wait_linear_retry/3`.

### 9.2 Waking and repair

The `attr_unify_hook/2` in `geler.pl` runs the goals of the variable being
bound.  Each `resubmit_*` first calls `repair/2`, which re-normalises a stored
normal form whose bases may since have become (partly) ground:
`repair_p_one/2` re-runs the appropriate `nf` case for each non-variable base,
and `nf_power/3` re-expands integer powers.  The result is submitted again,
and may now be linear, solvable by an isolation axiom, or still delayed.

`wait_linear/3` is the entry point used by `inf/2`, `minimize/1` and
`bb_inf/3`: it delays the whole optimisation until its expression has become
linear.

### 9.3 Isolation axioms

`nl_invertible/4` implements the axioms that let a non-linear atom be solved
once enough of it is ground:

| Constraint | Solvable when |
| --- | --- |
| `A = B*C` | `B` or `C` ground; or `A` and one of `B`,`C` ground |
| `A = B/C` | `C` ground; or `A` and `B` ground |
| `X = min(Y,Z)`, `X = max(Y,Z)` | `Y` and `Z` ground |
| `X = abs(Y)` | `Y` ground |
| `X = pow(Y,Z)` / `Y^Z` | any two of `X`,`Y`,`Z` ground |
| `X = sin(Y)`, `cos`, `tan` | `X` or `Y` ground |

The multiplication and division cases are handled structurally by the normal
form (a product of a scalar and a variable *is* linear), the rest by
`nl_invertible/4` and `nl_eval/2`.

Inverting `A = Kb^X` for `X` needs a logarithm, which is in general
irrational and therefore not representable in Q at all.  `log_q/3` in
`nf_q.pl` computes the quotient in floating point, looks for an exact
rational answer with a denominator of at most 16 (verifying it with exact
rational arithmetic), and only falls back on `rationalize/1` when there is
none.  That recovers `3` from `{1000 =:= 10^Y}` — whose float quotient is
`2.9999999999999996` — and `1r3` from `{2 =:= 8^Y}`.

The `X = Y^Z` case is where Q and R differ most: CLP(R) has four extra
`submit_eq_c1/3` clauses (added later than the port) that solve `I + K*X^P = 0`
for a variable `X` and a numeric exponent `P`, including the two-solution case
for even integer `P`.  CLP(Q) has no such clauses, so `{8 =:= Y^3}` *succeeds
with `Y` unbound* in CLP(Q) while CLP(R) binds `Y = 2.0`.


## 10. Optimisation

`inf(Expr, Inf)` waits for `Expr` to be linear, then:

1. creates a fresh dependent variable `Dep = Expr`;
2. `determine_active_dec/1` activates a bound on every variable of the row,
   choosing the bound that makes `R` as small as possible;
3. `iterate_dec/2` repeatedly calls `dec_step/2` until it reports `optimum`,
   at which point the infimum is `R + I`;
4. stores `[Inf|Vertex]` in a global variable and **fails**, undoing every
   pivot;
5. the second clause reads the global back and posts `{Inf =:= Value}`.

If any variable of the row has `type(t_none)`, `determine_active_dec/1` fails
and so does `inf/2` — an unbounded expression has no infimum.  `sup/2` is
`inf/2` of the negation.

`minimize/1` performs the same pivoting but keeps the result, then constrains
`{Dep =:= Inf}`.  The source explains the duplication: going through
`inf(E,E)` would force the simplex to rediscover the optimal vertex from the
equation, but keeps no garbage in the tableau; both trade-offs are offered.

`inf/4` and `sup/4` additionally return the values of a caller-supplied vector
of variables at the optimal vertex (`vertex_value/2` in `bb_*.pl`, which reads
`R+I` of each row).


## 11. Branch and bound

`bb_inf(Ints, Expr, Inf, Vertex)` is a textbook depth-first branch and bound
over the LP relaxation:

* `bb_intern/3` checks each element of `Ints`: a number must be integral, a
  variable has its bounds tightened to the enclosing integers with
  `bb_narrow_lower/1` / `bb_narrow_upper/1` (which use `inf/2`, `sup/2` and
  `entailed/1` to get the *strict* case right);
* `bb_loop/2` re-optimises (`bb_reoptimize/2`), prunes against the incumbent
  (`bb_better_bound/1`), and finds the first variable whose value is not
  integral (`bb_first_nonint/5`);
* `bb_branch/3` is the choice point `{V =< Floor} ; {V >= Ceiling}`;
* when every integer variable is integral the incumbent is replaced
  (`nb_setval(prov_opt, …)`), and the whole search is driven by failure.

The incumbent lives in a *global variable*, not in the search state, so the
pruning survives backtracking.  This also means `bb_inf/3,4,5` is not
reentrant: a nested call would clobber `prov_opt`.

In CLP(R) the extra `Eps` argument says how far from an integer a value may
be and still count as integral; `bb_inf/3` uses `0.001`.  CLP(Q) needs no such
parameter and uses `integer/1` directly.


## 12. Projection and answer presentation

This is the most intricate part of the system and the part users see.

### 12.1 `project_attributes/2`

Driven from `dump/3` (and from `copy_term/3` via `attribute_goals//1`), given
the target variables `Tvs` and all variables of their classes `Avs`:

1. `mark_target/1` sets argument 9 of the targets.
2. `project_nonlin/3` collects the delayed non-linear goals.  This *consumes*
   the mutexes, which is why the whole projection must run inside a failure
   loop or on a copy.
3. `redundancy_vars/1` removes redundant bounds (§12.2).
4. `make_target_indep/2` pivots each target variable with a non-target partner
   so that targets become independent; the partners are marked `keep`.
5. `drop_dep/1` discards rows of unbounded, non-target, non-`keep` dependent
   variables.
6. `fm_elim/4` eliminates the remaining non-target variables by
   Fourier–Motzkin (§12.3).
7. `impose_ordering/1` applies the user's `ordering/1` graph.

### 12.2 Redundancy elimination

`redund.pl` uses the *semantic* definition: a bound is redundant if adding its
negation makes the store unsatisfiable.  `redundant/3` therefore detaches the
bound, asserts the opposite through `{}/1`, and keeps the bound only if that
*succeeded* (`negate_l/4` and `negate_u/4` are written to fail when the
opposite bound is consistent, so that backtracking restores the bound).  For
two-sided types each side is tried separately.

This is expensive — it runs a full consistency check per bound — but it is
what makes projected answers readable; the OFAI manual reports 18 inequalities
reduced to 9 on its example.

### 12.3 Fourier–Motzkin elimination

`fourmotz_*.pl` eliminates one non-target variable at a time:

* `prefilter/2` drops targets and variables that occur in no bounded row.
* `best/3` chooses the next variable to eliminate by *fill-in*: for every
  candidate, `cp_card/4` counts how many inequalities the cross product would
  generate, and `Delta = New - Old` is minimised.  This is the standard
  greedy heuristic; if no candidate can be scored the elimination gives up and
  the remaining variables simply stay in the answer.
* `crossproduct//2` combines every pair of rows in which the variable occurs
  with opposite signs, producing `lez(Strict, Lin)` items; `flip/2` and
  `flip_strict/2` handle the sign case.
* `activate_crossproduct/1` turns each item into a fresh variable `V = Lin`
  with `V ≤ 0`, added to the basis.
* `fm_detach/1` then drops the bounds of the eliminated variable, and
  `reverse_pivot/1`/`unkeep/1` restore the pivots made by
  `make_target_indep/2`.

### 12.4 `ordering/1`

`ordering/1` accepts `A<B`, `A>B` or a list, and records edges in a *priority
graph* stored in the class's `clpqr_class` attribute.  At projection time
`arrangement/2` runs `top_sort/2` over the graph; a cycle raises
`unsatisfiable_ordering`.  `arrange/2` then binds the `order` keys of the
arrangement to `1,2,…`, renormalises every row (`renorm_all/1`) and finally
pivots rows into the requested shape (`arrange_pivot/1`).

The direction is: **a variable that comes earlier is preferred as
independent**, so it appears on the right-hand sides, and later variables get
isolated on the left.  `arrange_pivot/1` establishes this by pivoting any
dependent variable whose row leads with a later-ordered variable.

`dump/3` applies `ordering(Target)` to its own first argument, so the order of
the target list already controls the shape of the answer:

```
?- {X+Y =:= 1}, dump([X,Y],[x,y],C).
C = [y=1-x].
?- {X+Y =:= 1}, dump([Y,X],[y,x],C).
C = [x=1-y].
```

One caveat remains, and it is really a defect (§14.3): `ordering/1` silently
does nothing for variables that are not yet in the store, and a user ordering
that disagrees with the `dump/3` target list makes the priority graph cyclic.

### 12.5 Rendering

`dump_var//4` in `bv_*.pl` turns a row plus a bound type into readable
constraints: an equality `V = Sum` for `t_none`, and one or two inequalities
otherwise, scaled so that the first coefficient is 1.  `nf2sum/3` and
`hom2sum/3` build the term, choosing `+`/`-` and omitting unit coefficients.

`attribute_goals//1` in `dump.pl` wraps this for `copy_term/3` and for the
toplevel: it calls `dump/3` on the attributed variables of the term, wraps the
result in `{}/1`, and deletes the `clpqr_itf` attribute of the variables it has
already reported so that the goals are not emitted once per variable.


## 13. CLP(Q) versus CLP(R)

CLP(Q) computes with SWI-Prolog rationals (`rdiv`, `rationalize/1`).  Every
comparison is exact and every answer is exact.

CLP(R) computes with doubles and replaces each exact test with an
epsilon test, hard-coded as `1.0e-10` throughout:

| Exact test (Q) | Fuzzy test (R) |
| --- | --- |
| `K =:= 0` | `K >= -1.0e-10, K =< 1.0e-10` |
| `K =:= 1` | `abs(K-1.0) =< 1.0e-10` |
| `I < 0` | `I < -1.0e-10` |
| `I =< 0` | `I < 1.0e-10` |
| `K =\= 0` | `\+ (K >= -1.0e-10, K =< 1.0e-10)` |

Other systematic differences:

* **Coefficients.** CLP(R) writes `0.0`, `1.0`, `-1.0` where CLP(Q) writes
  `0`, `1`, `-1`, so rows stay float-typed.
* **Binding.** CLP(R) has `export_binding/2`, which snaps a value within
  epsilon of zero to exactly `0.0`.  CLP(Q) just unifies.
* **`numbers_only/1`.** CLP(Q) demands `rational/1` (integers are rational),
  CLP(R) demands `integer/1` or `float/1`.
* **Symbolic constants.** `#(pi)`, `#(p)`, `#(e)`, `#(zero)` exist only in
  CLP(R) ("provided for compatibility only", per the manual).
* **Integer exponents.** CLP(R) accepts a float exponent that happens to be
  integral (`integerp/2`); CLP(Q) requires `integer/1`.
* **Root extraction.** Only CLP(R) solves `I + K*X^P = 0` for `X` (§9.3).
* **`bb_inf`.** `bb_inf/4` in Q, `bb_inf/5` with an epsilon in R; R rounds the
  returned vertex with `round/1`.
* **Global variables.** `bb_*.pl` in Q uses `nb_current/2`, in R
  `catch(nb_getval(...),_,...)`.

A consequence that bites in practice: because CLP(R) binds its variables to
*floats*, a clause head written with an integer no longer matches.  The
classic

```prolog
fib(0, 0).
fib(1, 1).
fib(N, F) :- {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1+F2}, fib(N1,F1), fib(N2,F2).
```

works in CLP(Q) but *fails* in CLP(R), where the recursion reaches
`fib(0.0, F)` and `0.0` does not unify with `0`.  The base cases have to be
written as constraints (`fib(N,F) :- {N =:= 0, F =:= 0}.`).

The practical consequence, which the OFAI manual states outright, is that
"the fact that you can switch between clp(R) and clp(Q) should solve most of
your numerical problems regarding precision" — ill-conditioned problems belong
in CLP(Q).


## 14. Known problems

The following were found while writing this document and the test suite.  They
are recorded here rather than fixed, so that the tests can pin down current
behaviour first.  Tests that encode a *wrong* answer are marked in the suite.

### 14.1 Dead code that changes behaviour

* `clpq/bv_q.pl:1271`, `clpr/bv_r.pl:1296` — `pivot/2` reads
  `arg(5,AttI,class(Class))` where argument 5 is `order(Ord)`.  `pivot/2` is
  currently unreachable (only `pivot/5` is called), so this is latent.
* `clpqr/redund.pl:85` — the first clause of `redundancy_vars/1` is `!`, so
  the second (timing) clause is dead.  Harmless, but misleading.
* `clpq/nf_q.pl:868`, `clpr/nf_r.pl:929` — `nf_power_pos/3` is superseded by
  `binom/3` and no longer called.
* `clpqr_itf` argument 7 is never read or written.

Further predicates that are defined but have no caller, and which the test
suite consequently cannot reach:

| Predicate | File |
| --- | --- |
| `'solve_='/1` | `bv_*.pl` (`nf_*.pl` calls `solve/1` directly) |
| `solve_x/2`, `solve_x/6` | `bv_*.pl` (superseded by `solve_ord_x/3`) |
| `iterate_inc/2` | `bv_*.pl` (only `iterate_dec/2` is used) |
| `basis/2`, `basis_drop/1` | `bv_*.pl` |
| `pivot/2` | `bv_*.pl` (and buggy, see above) |
| `nf_power_pos/3` | `nf_*.pl` |
| `l2conj/2`, `nonexhausted//1` | `clpqr/geler.pl` |
| `red_t_l/0`, `red_t_L/0`, `red_t_U/0` | `clpqr/redund.pl` (profiling hooks) |

`projecting_assert/1` in `clpqr/dump.pl` is exported by that module but
commented out of the `clpq`/`clpr` export lists, so it is only reachable as
`clpqr_dump:projecting_assert/1`.

Two more clauses look unreachable from `{}/1`, because `submit_lt_c/3` and
`submit_le_c/3` handle the single-variable case before the solver is
entered: the first clause of `ineq/4` and the first clause of
`ineq_cases/6` in `ineq_*.pl`.

### 14.2 Wrong results

* **Residual goals are duplicated for purely non-linear stores.**
  `clpqr/dump.pl:200-214`: `attribute_goals//1` deletes the `clpqr_itf`
  attribute of the variables it has reported, but not the `clpqr_geler`
  attribute, and `clpqr_geler:attribute_goals//1` forwards to the same code.
  A variable that only has delayed goals is therefore reported once per
  variable:

  ```
  ?- {X*Y =:= 6}.
  {-6+Y*X=0},
  {-6+Y*X=0}.
  ```

  With three delayed goals the answer is printed three times, and so on.

* **A pending optimisation leaks into the residual goals.**  When
  `minimize/1`, `inf/2` or `bb_inf/3` is still waiting for its expression to
  become linear, `transg//1`'s `wait_linear_retry/3` case emits the solver's
  own continuation as part of the `{}/1` term, so the answer of
  `copy_term/3` cannot be executed again:

  ```
  ?- {Y >= 1, Y =< 5}, minimize(X*Y), copy_term(Y,_,Gs), maplist(call,Gs).
  ERROR: Type error: `clpq_constraint' expected, found `minimize_lin(_123)'
  ```

### 14.3 `ordering/1` is largely unusable

* The arrangement itself used to be discarded: `arrange_pivot/1` in
  `clpqr/project.pl` tested `arg(6,AttY,clpqr_class(Class))` where argument 6
  of the `clpqr_itf` attribute holds `class(C)`, so the guard could never
  succeed and no pivot was ever made.  *Fixed*; `ordering/1` and the order of
  the `dump/3` target list now determine the shape of the answer.
* On variables that are not yet known to the solver, `join_class/2` fails
  (because `clp_type/2` fails), and `ordering/1` falls through to its catch-all
  clause `ordering(_).`  The call silently succeeds and does nothing.  Since
  the natural use is `ordering([X,Y]), {…}`, this is the common case.
* A single-element list generates no edges at all, so the manual's example
  `ordering([Mp])` has no effect.
* `dump/3` calls `ordering(Target)` internally on its first argument.  If the
  user's ordering disagrees with the order of the `dump/3` target list, the
  combined graph has a cycle and `arrangement/2` throws
  `unsatisfiable_ordering`:

  ```
  ?- {X+Y =:= 1}, ordering([Y,X]), dump([X,Y],[x,y],C).
  ERROR: Unknown message: unsatisfiable_ordering
  ```
* `unsatisfiable_ordering` is thrown as a bare term, not as an
  `error(_,_)` term, so it prints as "Unknown message".

### 14.4 Interface and documentation mismatches

* The documented isolation axiom "`X = exp(Y,Z)`, `X` and `Z` ground, e.g.
  `8 = Y^3`" is implemented in CLP(R) only.  In CLP(Q), `{8 =:= Y^3}`
  succeeds with `Y` unbound and a residual goal.
* `dump/3` requires its first argument to be a list of *unbound* variables;
  `{X = 1}, dump([X],[y],L)` raises `uninstantiation_error(1)`.  This is
  documented as a known problem but is still surprising, since `X` is exactly
  the kind of variable a user would want to dump.
* Answers for inequalities can mention fresh slack variables:
  `{X+Y >= 1}` prints `{Y=1-X+_A, _A>=0}`.  Documented.
* Division by zero *fails* silently (`zero_division :- fail.` with the comment
  `% raise_exception(_) ?`) instead of raising `evaluation_error(zero_divisor)`.
* `library(clpq)` and `library(clpr)` cannot both be imported into one module
  (name clashes on every exported predicate); the manual text "It is allowed
  to use both libraries in one program" is true only with explicit module
  qualification.

### 14.5 Robustness

* `bb_inf/3,4,5` uses the non-backtrackable global variable `prov_opt` and is
  therefore not reentrant and not thread-safe with respect to itself.
* Exceptions thrown by the solver mostly use ad-hoc terms
  (`instantiation_error(Goal,Arg)`, `unsatisfiable_ordering`,
  `permission_error('mix CLP(Q) variables with','CLP(R) variables:',X)`)
  rather than ISO `error/2` terms.


## 15. Testing

The suite lives in `test_clpq.pl` and `test_clpr.pl` (one file per solver,
because the two libraries export the same predicate names and cannot be
imported into a single module).  Both are ordinary `library(plunit)` suites
registered with CMake via `test_libs(clpq clpr)`, so they run as
`ctest -R clpqr:`.

The suites are organised to follow this document:

| Unit | Covers |
| --- | --- |
| `syntax` | the constraint/expression grammar and its type errors |
| `nf` | normal-form construction, cancellation, powers |
| `equations` | `solve/1`: rank, implied values, class merging |
| `inequalities` | bound updates, strictness, the simplex |
| `disequations` | `=\=` and the `nonzero` mark |
| `nonlinear` | delaying, waking, isolation axioms |
| `entailment` | `entailed/1` |
| `optimisation` | `inf/2,4`, `sup/2,4`, `minimize/1`, `maximize/1` |
| `bb` | `bb_inf/3,4,5` |
| `projection` | `dump/3`, redundancy elimination, Fourier–Motzkin |
| `residuals` | `copy_term/3` and toplevel answer shape |
| `unify` | `attr_unify_hook/2`, aliasing, solver mixing |
| `known_issues` | the defects of §14, pinned to current behaviour |

Coverage is measured with `library(prolog_coverage)`:

```prolog
?- use_module(library(prolog_coverage)).
?- [library(clpq), library(clpr)].
?- coverage((test_clpq, test_clpr), [dir('cov'), annotate(true)]).
```

Clause coverage of the solver as of writing (242 CLP(Q) tests + 229 CLP(R)
tests):

| File | Clauses | % covered |
| --- | --- | --- |
| `clpqr/project.pl` | 36 | 94 |
| `clpq/store_q.pl`, `clpr/store_r.pl` | 38 | 92 |
| `clpq/nf_q.pl` | 199 | 89 |
| `clpr/nf_r.pl` | 211 | 87 |
| `clpqr/itf.pl` | 14 | 86 |
| `clpq/fourmotz_q.pl` | 71 | 83 |
| `clpqr/dump.pl` | 28 | 82 |
| `clpqr/class.pl` | 16 | 81 |
| `clpr/bb_r.pl` | 26 | 81 |
| `clpq/bv_q.pl`, `clpr/bv_r.pl` | 194/195 | 80 |
| `clpr/fourmotz_r.pl` | 71 | 79 |
| `clpq/itf_q.pl` | 34 | 77 |
| `clpqr/ordering.pl` | 28 | 75 |
| `clpr/itf_r.pl` | 34 | 74 |
| `clpq/bb_q.pl` | 25 | 72 |
| `clpq/ineq_q.pl` | 100 | 70 |
| `clpr/ineq_r.pl` | 100 | 69 |
| `clpqr/geler.pl` | 18 | 67 |
| `clpqr/redund.pl` | 35 | 57 |

What is left uncovered is, in decreasing order of size:

1. Code that is structurally unreachable — see the table in §14.1.  This
   accounts for most of the gap in `bv_*.pl` and `clpqr/geler.pl`.
2. The `sandbox:safe_primitive/1` facts, which are declarations rather than
   executable clauses.
3. Bound-update clauses in `ineq_*.pl` and redundancy clauses in
   `clpqr/redund.pl` that only trigger for particular combinations of active
   bound and strictness (`t_L`, `t_Lu`, `t_lU`, `t_U`).  These are reachable
   in principle; each needs a simplex state that is awkward to construct from
   the outside.
4. `narrow_u/3`, `narrow_l/3` and the `inc_step_2*` clauses in `bv_*.pl`,
   which need a basic variable whose optimum lies strictly inside its bound.

To find these, ask `library(prolog_coverage)` for annotated sources
(`annotate(true), line_numbers(true)`): each clause is prefixed with its
entry/exit counts, `###` marking a clause that was never entered and `--`
one that was entered but never exited.
