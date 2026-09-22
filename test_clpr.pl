/*  Part of CLP(Q,R) (Constraint Logic Programming over Rationals and Reals)

    Author:        Jan Wielemaker
    E-mail:        jan@swi-prolog.org
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2026, SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(test_clpr,
          [ test_clpr/0
          ]).
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(clpr)).
:- use_module(library(clpq), []).          % for the solver-mixing tests

/** <module> Test CLP(R)

Tests for library(clpr).  The structure follows doc/design.md and mirrors
test_clpq.pl, with extra units for the features that only exist in CLP(R)
(symbolic constants, root extraction, the epsilon of bb_inf/5) and for the
consequences of computing with floats.

Numeric results are compared with =near/2=, which uses the solver's own
epsilon of 1.0e-10.

@see doc/design.md
*/

test_clpr :-
    run_tests([ clpr_syntax,
                clpr_nf,
                clpr_equations,
                clpr_inequalities,
                clpr_disequations,
                clpr_nonlinear,
                clpr_entailment,
                clpr_optimisation,
                clpr_bb,
                clpr_projection,
                clpr_residuals,
                clpr_unify,
                clpr_internals,
                clpr_examples,
                clpr_known_issues
              ]).

%!  near(+X, +Y) is semidet.
%
%   True when X and Y are equal within the solver's own epsilon.

near(X, Y) :-
    NX is X,
    NY is Y,
    abs(NX-NY) =< 1.0e-10.

		 /*******************************
		 *           SYNTAX		*
		 *******************************/

:- begin_tests(clpr_syntax).

test(conjunction) :-
    {X > 1, X < 3, X =:= 2},
    assertion(near(X, 2.0)).
test(nested_conjunction) :-
    {(X =:= 1, Y =:= 2)},
    assertion(near(X,1.0)),
    assertion(near(Y,2.0)).
test(disjunction, all(Ok == [true,true])) :-
    {X =:= 1 ; X =:= 2},
    ( near(X,1.0) ; near(X,2.0) ),
    Ok = true.
test(less) :-
    {X < 3, X > 2, X =:= 2.5}.
test(greater) :-
    {3 > X, 2 < X, X =:= 2.5}.
test(leq) :-
    {X =< 3, X >= 3},
    assertion(near(X, 3.0)).
test(leq_alt) :-
    {<=(X, 3)}, {X >= 3},
    assertion(near(X, 3.0)).
test(eq_is) :-
    {X =:= 3},
    assertion(near(X, 3.0)).
test(eq_unify) :-
    {X = 3},
    assertion(near(X, 3.0)).
test(result_is_float) :-
    {X =:= 3},
    assertion(float(X)).
test(unary_minus) :-
    {X =:= -(-3)},
    assertion(near(X, 3.0)).
test(unary_plus) :-
    {X =:= +3},
    assertion(near(X, 3.0)).
test(division) :-
    {X =:= 1/4},
    assertion(near(X, 0.25)).
test(abs) :-
    {X =:= abs(-7)},
    assertion(near(X, 7.0)).
test(min) :-
    {X =:= min(3,4)},
    assertion(near(X, 3.0)).
test(max) :-
    {X =:= max(3,4)},
    assertion(near(X, 4.0)).
test(pow) :-
    {X =:= pow(2,10)},
    assertion(near(X, 1024.0)).
test(hat) :-
    {X =:= 2^10},
    assertion(near(X, 1024.0)).
test(exp2) :-
    {X =:= exp(2,10)},
    assertion(near(X, 1024.0)).
test(negative_power) :-
    {X =:= 2^(-2)},
    assertion(near(X, 0.25)).
test(zero_power) :-
    {X =:= 5^0},
    assertion(near(X, 1.0)).
test(fractional_power) :-
    {X =:= 2^0.5},
    assertion(near(X, 1.4142135623730951)).

% Symbolic "Monash" constants; CLP(R) only.

test(constant_pi) :-
    {X =:= #(pi)},
    assertion(near(X, pi)).
test(constant_p) :-
    {X =:= #(p)},
    assertion(near(X, pi)).
test(constant_e) :-
    {X =:= #(e)},
    assertion(near(X, e)).
test(constant_zero) :-
    {X =:= #(zero)},
    assertion(near(X, 1.0e-10)).

% Errors

test(var_constraint, error(instantiation_error)) :-
    {_}.
test(bad_constraint, error(type_error(clpr_constraint, foo))) :-
    {foo}.
test(bad_expression, error(type_error(clpr_expression, a))) :-
    {_ =:= a}.
test(star_star_rejected, error(type_error(clpr_expression, 2**3))) :-
    {_ =:= 2**3}.
test(sqrt_rejected, error(type_error(clpr_expression, sqrt(4)))) :-
    {_ =:= sqrt(4)}.
test(unknown_constant_rejected, error(type_error(clpr_expression, #(foo)))) :-
    {_ =:= #(foo)}.
test(entailed_var, throws(instantiation_error(entailed(_),1))) :-
    entailed(_).
test(entailed_bad, error(type_error(clpr_constraint, foo))) :-
    entailed(foo).

:- end_tests(clpr_syntax).

		 /*******************************
		 *        NORMAL FORM		*
		 *******************************/

:- begin_tests(clpr_nf).

test(cancel) :-
    {X - X =:= 0}, var(X).
test(cancel_sum) :-
    {Y =:= X + 1 - X},
    assertion(near(Y, 1.0)).
test(collect) :-
    {Y =:= 2*X + 3*X - 5*X},
    assertion(near(Y, 0.0)).
test(distribute) :-
    {Y =:= (X+1)*(X-1) - X*X},
    assertion(near(Y, -1.0)).
test(binomial) :-
    {Y =:= (X+1)^2 - X^2 - 2*X},
    assertion(near(Y, 1.0)).
test(binomial_big) :-
    {Y =:= (1+X)^3 - (1 + 3*X + 3*X^2 + X^3)},
    assertion(near(Y, 0.0)).
test(scalar_product) :-
    {X =:= 3*4},
    assertion(near(X, 12.0)).
test(division_by_variable_is_nonlinear) :-
    {_ =:= 1/X},
    assertion(var(X)).
test(division_by_zero_fails, fail) :-
    {_ =:= 1/0}.
test(mult_two_vars_is_nonlinear) :-
    {Z =:= X*Y},
    assertion((var(X),var(Y),var(Z))).
test(mult_by_constant_is_linear) :-
    {Z =:= 3*X, X =:= 2},
    assertion(near(Z, 6.0)).
test(zero_snapping) :-
    % export_binding/2 snaps a result within epsilon of 0 to exactly 0.0
    {X =:= 1.0e-15},
    assertion(X == 0.0).

:- end_tests(clpr_nf).

		 /*******************************
		 *          EQUATIONS		*
		 *******************************/

:- begin_tests(clpr_equations).

test(two_by_two) :-
    {2*X + 3*Y =:= 7, X - Y =:= 1},
    assertion(near(X, 2.0)),
    assertion(near(Y, 1.0)).
test(three_by_three) :-
    { X + Y + Z =:= 6,
      X - Y + Z =:= 2,
      X + Y - Z =:= 0 },
    assertion(near(X, 1.0)),
    assertion(near(Y, 2.0)),
    assertion(near(Z, 3.0)).
test(fractional_solution) :-
    {3*X =:= 1},
    assertion(near(X, 1/3)).
test(inconsistent, fail) :-
    {X + Y =:= 1, X + Y =:= 2}.
test(dependent_rows) :-
    {X + Y =:= 1, 2*X + 2*Y =:= 2},
    assertion((var(X),var(Y))).
test(implied_value) :-
    {X + Y =:= 3},
    assertion((var(X),var(Y))),
    {X - Y =:= 1},
    assertion(near(X, 2.0)),
    assertion(near(Y, 1.0)).
test(class_merge) :-
    {X + Y =:= 1},
    {Z + W =:= 2},
    {Y =:= Z},
    {X =:= 0},
    assertion(near(Y, 1.0)),
    assertion(near(Z, 1.0)),
    assertion(near(W, 1.0)).
test(alias) :-
    {X =:= Y}, {X =:= 1},
    assertion(near(Y, 1.0)).
test(chain) :-
    {A =:= B, B =:= C, C =:= D, D =:= 7},
    assertion(near(A, 7.0)).
test(negative_coefficients) :-
    {-X - Y =:= -3, X - Y =:= 1},
    assertion(near(X, 2.0)),
    assertion(near(Y, 1.0)).

:- end_tests(clpr_equations).

		 /*******************************
		 *        INEQUALITIES		*
		 *******************************/

:- begin_tests(clpr_inequalities).

test(simple_bounds) :-
    {X >= 1, X =< 3},
    assertion(var(X)),
    inf(X, I), sup(X, S),
    assertion(near(I, 1.0)),
    assertion(near(S, 3.0)).
test(meeting_bounds) :-
    {X >= 2, X =< 2},
    assertion(near(X, 2.0)).
test(strict_meeting_bounds, fail) :-
    {X > 2, X =< 2}.
test(strict_both, fail) :-
    {X > 2, X < 2}.
test(empty_interval, fail) :-
    {X >= 3, X =< 2}.
test(tighten_lower) :-
    {X >= 1}, {X >= 2}, {X >= 0},
    assertion(entailed(X >= 2)),
    assertion(\+ entailed(X >= 3)).
test(tighten_upper) :-
    {X =< 5}, {X =< 3}, {X =< 9},
    assertion(entailed(X =< 3)),
    assertion(\+ entailed(X =< 2)).
test(strictness_kept) :-
    {X > 1},
    assertion(\+ {X =:= 1}),
    assertion(entailed(X >= 1)).
test(two_variables) :-
    {X + Y =< 10, X >= 0, Y >= 0},
    sup(X, S),
    assertion(near(S, 10.0)).
test(triangle) :-
    {X >= 0, Y >= 0, X + Y =< 1},
    assertion(\+ {X =:= 1, Y =:= 1}),
    {X =:= 1},
    assertion(near(Y, 0.0)).
test(unbounded_sup, fail) :-
    {X >= 0},
    sup(X, _).
test(unbounded_inf, fail) :-
    {X =< 0},
    inf(X, _).
test(transitive) :-
    {X =< Y, Y =< Z, Z =< X},
    {X =:= 1},
    assertion(near(Y, 1.0)),
    assertion(near(Z, 1.0)).
test(transitive_strict, fail) :-
    {X < Y, Y < Z, Z < X}.
test(slack_elimination) :-
    { A >= 0, B >= 0, C >= 0, D >= 0,
      A + B + C + D =< 4,
      A + B + C + D >= 4,
      A =< 1, B =< 1, C =< 1, D =< 1 },
    assertion(near(A, 1.0)),
    assertion(near(B, 1.0)),
    assertion(near(C, 1.0)),
    assertion(near(D, 1.0)).
test(negative_bounds) :-
    {X =< -5},
    assertion(entailed(X < 0)),
    sup(X, S),
    assertion(near(S, -5.0)).
test(scaled_bound) :-
    {3*X =< 7},
    sup(X, S),
    assertion(near(S, 7/3)).
test(mixed_eq_ineq) :-
    {X + Y =:= 10, X >= 0, Y >= 0},
    inf(X, I), sup(X, S),
    assertion(near(I, 0.0)),
    assertion(near(S, 10.0)).
test(epsilon_tolerance) :-
    % Differences below 1.0e-10 are not distinguished
    {X >= 1, X =< 1 + 1.0e-15},
    assertion(near(X, 1.0)).

:- end_tests(clpr_inequalities).

		 /*******************************
		 *        DISEQUATIONS		*
		 *******************************/

:- begin_tests(clpr_disequations).

test(ground_true) :-
    {1 =\= 2}.
test(ground_false, fail) :-
    {1 =\= 1}.
test(delayed_ok) :-
    {X =\= 3},
    {X =:= 4},
    assertion(near(X, 4.0)).
test(delayed_violated, fail) :-
    {X =\= 3},
    {X =:= 3}.
test(delayed_violated_unify, fail) :-
    {X =\= 3},
    X = 3.0.
test(two_variables) :-
    {X =\= Y},
    {X =:= 1},
    assertion(\+ {Y =:= 1}),
    {Y =:= 2}.
test(expression) :-
    {X + Y =\= 1},
    {X =:= 0},
    assertion(\+ {Y =:= 1}).
test(alldifferent) :-
    {A =\= B, B =\= C, A =\= C},
    {A =:= 1, B =:= 2, C =:= 3}.
test(alldifferent_violated, fail) :-
    {A =\= B, B =\= C, A =\= C},
    {A =:= 1, B =:= 2, C =:= 1}.
test(residual_shape) :-
    {X =\= 3},
    dump([X], [x], C),
    C = [x =\= V],
    assertion(near(V, 3.0)).

:- end_tests(clpr_disequations).

		 /*******************************
		 *         NON-LINEAR		*
		 *******************************/

:- begin_tests(clpr_nonlinear).

test(delayed_product, [nondet]) :-
    {X*Y =:= 6},
    assertion((var(X), var(Y))),
    {X =:= 2},
    assertion(near(Y, 3.0)).
test(delayed_product_other_way, [nondet]) :-
    {X*Y =:= 6},
    {Y =:= 3},
    assertion(near(X, 2.0)).
test(division_delayed, [nondet]) :-
    {X/Y =:= 2},
    {Y =:= 3},
    assertion(near(X, 6.0)).
test(abs_delayed, [nondet]) :-
    {X =:= abs(Y)},
    {Y =:= -4},
    assertion(near(X, 4.0)).
test(min_delayed, [nondet]) :-
    {X =:= min(Y,3)},
    {Y =:= 1},
    assertion(near(X, 1.0)).
test(max_delayed, [nondet]) :-
    {X =:= max(Y,3)},
    {Y =:= 5},
    assertion(near(X, 5.0)).
test(invert_sin) :-
    {0 =:= sin(X)},
    assertion(near(X, 0.0)).
test(invert_cos) :-
    {1 =:= cos(X)},
    assertion(near(X, 0.0)).
test(invert_tan) :-
    {0 =:= tan(X)},
    assertion(near(X, 0.0)).
test(invert_asin) :-
    {1 =:= sin(X)},
    assertion(near(X, pi/2)).
test(invert_exponent) :-
    % 2^Y = 8; CLP(R) gets this exactly right, CLP(Q) does not
    {8 =:= 2^Y},
    assertion(near(Y, 3.0)).
test(root_odd) :-
    % isolation axiom: X and Z ground in X = Y^Z
    {8 =:= Y^3},
    assertion(near(Y, 2.0)).
test(root_odd_negative) :-
    {-8 =:= Y^3},
    assertion(near(Y, -2.0)).
test(root_even, all(Ok == [true,true])) :-
    % an even root has two solutions and CLP(R) enumerates both
    {4 =:= Y^2},
    ( near(Y, 2.0) ; near(Y, -2.0) ),
    Ok = true.
test(square_is_solved, [nondet]) :-
    % unlike CLP(Q), this binds X
    {X*X =:= 2},
    assertion(near(X, 1.4142135623730951)).
test(nonlinear_becomes_linear, [nondet]) :-
    {Z =:= X*_Y + 1},
    {X =:= 0},
    assertion(near(Z, 1.0)).
test(goal_runs_once, [nondet]) :-
    {X*Y =:= 6},
    {X =:= 2, Y =:= 3}.
test(delayed_inequality, [nondet]) :-
    {X*Y =< 6},
    {X =:= 2},
    assertion(entailed(Y =< 3)).
test(delayed_inequality_violated, fail) :-
    {X*Y =< 6},
    {X =:= 2, Y =:= 4}.
test(delayed_disequation, fail) :-
    {X*Y =\= 6},
    {X =:= 2, Y =:= 3}.
test(power_of_variable_delayed, [nondet]) :-
    {Y =:= X^3},
    {X =:= 2},
    assertion(near(Y, 8.0)).

:- end_tests(clpr_nonlinear).

		 /*******************************
		 *         ENTAILMENT		*
		 *******************************/

:- begin_tests(clpr_entailment).

test(trivial) :-
    entailed(1 =:= 1).
test(trivial_false, fail) :-
    entailed(1 =:= 2).
test(from_equality) :-
    {X =:= 3},
    entailed(X > 2),
    entailed(X >= 3),
    entailed(X =\= 4).
test(from_bounds) :-
    {X >= 1, X =< 2},
    entailed(X > 0),
    entailed(X < 3),
    \+ entailed(X > 1),
    \+ entailed(X =:= 1).
test(conjunction) :-
    {X >= 1, X =< 2},
    entailed((X >= 1, X =< 2)).
test(disjunction) :-
    {X >= 1, X =< 2},
    entailed((X =< 0 ; X >= 1)).
test(linear_combination) :-
    {X + Y =:= 10, X >= 0, Y >= 0},
    entailed(X =< 10),
    entailed(X + Y >= 10).
test(does_not_change_store) :-
    {X >= 1, X =< 2},
    dump([X], [x], Before),
    ( entailed(X > 5) -> true ; true ),
    dump([X], [x], After),
    assertion(Before == After).

:- end_tests(clpr_entailment).

		 /*******************************
		 *        OPTIMISATION		*
		 *******************************/

:- begin_tests(clpr_optimisation).

test(inf_simple) :-
    {X >= 1, X =< 5},
    inf(X, I),
    assertion(near(I, 1.0)).
test(sup_simple) :-
    {X >= 1, X =< 5},
    sup(X, S),
    assertion(near(S, 5.0)).
test(inf_does_not_bind) :-
    {X >= 1, X =< 5},
    inf(X, _),
    assertion(var(X)),
    sup(X, S),
    assertion(near(S, 5.0)).
test(inf_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I),
    assertion(near(I, 2.0)).
test(sup_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X + Y, S),
    assertion(near(S, 4.0)).
test(inf_vertex) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I, [X,Y], V),
    assertion(near(I, 2.0)),
    V = [A,B],
    assertion(near(A,1.0)),
    assertion(near(B,1.0)).
test(minimize) :-
    {X >= 2, X =< 7},
    minimize(X),
    assertion(near(X, 2.0)).
test(maximize) :-
    {X >= 2, X =< 7},
    maximize(X),
    assertion(near(X, 7.0)).
test(minimize_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    minimize(X + Y),
    assertion(near(X, 1.0)),
    assertion(near(Y, 1.0)).
test(maximize_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    maximize(X + Y),
    assertion(entailed(X + Y =:= 4)).
test(lp_diet) :-
    { A >= 0, B >= 0,
      A + 2*B >= 4,
      3*A + B >= 6 },
    inf(2*A + 3*B, I),
    assertion(near(I, 6.8)).
test(unbounded_inf_fails, fail) :-
    {X >= 0},
    inf(-X, _).
test(inf_waits_for_linear, [nondet]) :-
    {X*Y >= 3},
    {X =:= 1},
    inf(Y, I),
    assertion(near(I, 3.0)).

:- end_tests(clpr_optimisation).

		 /*******************************
		 *      BRANCH AND BOUND	*
		 *******************************/

:- begin_tests(clpr_bb).

test(single_variable) :-
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, I),
    assertion(near(I, 1.0)).
test(single_variable_vertex) :-
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, I, V, 0.001),
    assertion(near(I, 1.0)),
    assertion(V == [1]).
test(two_variables) :-
    {X >= 0, Y >= 0, X + Y >= 1},
    bb_inf([X,Y], X + Y, I),
    assertion(near(I, 1.0)).
test(fractional_optimum) :-
    {2*X >= 1, X >= 0},
    bb_inf([X], X, I),
    assertion(near(I, 1.0)).
test(does_not_bind) :-
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, _),
    assertion(var(X)),
    inf(X, LpInf),
    assertion(near(LpInf, 0.5)).
test(knapsack) :-
    { A >= 0, B >= 0,
      A =< 3, B =< 3,
      2*A + 3*B >= 7 },
    bb_inf([A,B], A + B, I),
    assertion(near(I, 3.0)).
test(objective_not_integral) :-
    {X >= 0.5, Y >= 0.25},
    bb_inf([X], X + Y, I),
    assertion(near(I, 1.25)).
test(ground_integer_ok) :-
    {X >= 0},
    bb_inf([2], X, I),
    assertion(near(I, 0.0)).
test(ground_noninteger_fails, fail) :-
    {X >= 0},
    bb_inf([1.5], X, _).
test(unbounded_fails, fail) :-
    {X >= 0},
    bb_inf([X], -X, _).
test(does_not_touch_global_variables) :-
    nb_setval(prov_opt, mine),
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, I),
    assertion(near(I, 1.0)),
    nb_getval(prov_opt, V),
    assertion(V == mine),
    nb_delete(prov_opt).
test(bounds_are_narrowed_to_integers) :-
    % bb_intern/4 first narrows the *bounds* of each integer variable to
    % enclosing integers, independently of Eps
    {X >= 1.9999, X =< 5},
    bb_inf([X], X, I, _, 0.001),
    assertion(near(I, 2.0)).
test(epsilon_accepts_near_integer) :-
    % a ground value within Eps of an integer is accepted as integral
    {X =:= 1.9999},
    bb_inf([X], X, I, _, 0.001),
    assertion(near(I, 1.9999)).
test(small_epsilon_rejects_near_integer, fail) :-
    % ... and rejected when Eps is tight
    {X =:= 1.9999},
    bb_inf([X], X, _, _, 1.0e-9).

:- end_tests(clpr_bb).

		 /*******************************
		 *         PROJECTION		*
		 *******************************/

:- begin_tests(clpr_projection).

test(empty) :-
    dump([], [], C),
    assertion(C == []).
test(unconstrained) :-
    dump([_], [x], C),
    assertion(C == []).
test(equation) :-
    {X + Y =:= 1},
    dump([X,Y], [x,y], C),
    assertion(C = [y = 1.0-x]).
test(bounds) :-
    {X >= 1, X =< 3},
    dump([X], [x], C),
    C = [x >= L, x =< U],
    assertion(near(L,1.0)),
    assertion(near(U,3.0)).
test(strict_bounds) :-
    {X > 1, X < 3},
    dump([X], [x], C),
    assertion(C = [x > _, x < _]).
test(redundant_bounds_removed) :-
    {X >= 1, X >= 2, X >= 0},
    dump([X], [x], C),
    C = [x >= L],
    assertion(near(L, 2.0)).
test(projection_eliminates_variable) :-
    {X + Y >= 1, Y >= 0},
    dump([X], [x], C),
    assertion(C == []).
test(fourier_motzkin) :-
    {X =< Y, Y =< Z},
    dump([X,Z], [x,z], C),
    assertion(C = [x-z =< _]).
test(does_not_change_store) :-
    {X >= 1, X =< 3},
    dump([X], [x], _),
    inf(X, I), sup(X, S),
    assertion(near(I,1.0)),
    assertion(near(S,3.0)).
test(nonlinear_residue) :-
    {X*Y =:= 6},
    dump([X,Y], [x,y], C),
    assertion(C = [_]).
test(target_order_does_not_control_shape) :-
    {X + Y =:= 1},
    dump([X,Y], [x,y], C1),
    dump([Y,X], [y,x], C2),
    assertion(C1 == C2).
test(ordering_list_controls_shape) :-
    % the variable that comes first is the one the answer defines
    {X + Y =:= 1},
    ordering([Y,X]),
    dump([X,Y], [x,y], C),
    assertion(C = [y = _-x]).
test(ordering_list_controls_shape_2) :-
    {X + Y =:= 1},
    ordering([X,Y]),
    dump([X,Y], [x,y], C),
    assertion(C = [x = _-y]).
test(cyclic_ordering_list, error(cyclic_ordering(_))) :-
    {X + Y =:= 1},
    ordering([X,Y]),
    ordering([Y,X]).
test(cyclic_ordering_lt, error(cyclic_ordering(_))) :-
    {X + Y =:= 1},
    ordering(X < Y),
    ordering(Y < X).
test(cyclic_ordering_after_merge, error(cyclic_ordering(_))) :-
    % each class is acyclic on its own; unifying the variables merges the
    % priority graphs and only then is the result cyclic, so this one is
    % caught by arrangement/2 rather than by ordering/2
    {X + _ =:= 1}, {Y + _ =:= 2},
    ordering(X < Y),
    {A + _ =:= 3}, {B + _ =:= 4},
    ordering(B < A),
    X = A, Y = B,
    dump([X,Y], [x,y], _).
test(ordering_before_constraints) :-
    ordering([Y,X]),
    {X + Y =:= 1},
    dump([X,Y], [x,y], C),
    assertion(C = [y = _-x]).
test(target_must_be_free, error(uninstantiation_error(_))) :-
    {X =:= 1},
    dump([X], [x], _).
test(target_must_be_list, error(type_error(list(var), foo))) :-
    dump(foo, _, _).

:- end_tests(clpr_projection).

		 /*******************************
		 *         RESIDUALS		*
		 *******************************/

:- begin_tests(clpr_residuals).

test(copy_term_bounds) :-
    {X > 1, X < 3},
    copy_term(X, Y, Gs),
    assertion(Gs = [{_}]),
    assertion(var(Y)).
test(copy_term_is_independent) :-
    {X > 1},
    copy_term(X, Y, Gs),
    maplist(call, Gs),
    {Y =:= 2},
    assertion(var(X)).
test(copy_term_unconstrained) :-
    copy_term(_, _, Gs),
    assertion(Gs == []).
test(pending_optimisation_is_reusable) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    copy_term(f(X,Y), f(X2,Y2), Gs),
    assertion(Gs = [{_}, clpr:minimize(_)]),
    maplist(call, Gs),
    {X2 =:= 1},
    assertion(near(X2, 1.0)),
    assertion(near(Y2, 1.0)).
test(dump_omits_pending_goals) :-
    {Y >= 1, Y =< 5},
    minimize(_X*Y),
    dump([Y], [y], C),
    assertion(C = [y >= _, y =< _]).
test(residual_is_reusable) :-
    {X >= 1, X =< 3},
    copy_term(X, Y, Gs),
    maplist(call, Gs),
    inf(Y, I), sup(Y, S),
    assertion(near(I,1.0)),
    assertion(near(S,3.0)).

:- end_tests(clpr_residuals).

		 /*******************************
		 *        UNIFICATION		*
		 *******************************/

:- begin_tests(clpr_unify).

test(unify_number_ok) :-
    {X >= 1}, X = 2.
test(unify_number_violates, fail) :-
    {X >= 1}, X = 0.
test(unify_float) :-
    {X >= 0.5}, X = 0.5.
test(unify_integer) :-
    {X >= 1}, X = 1.
test(unify_rational_type_error, error(type_error(real, _))) :-
    R is 1 rdiv 2,
    {X >= 0}, X = R.
test(unify_atom_type_error, error(type_error(real, a))) :-
    {X >= 1}, X = a.
test(unify_two_constrained) :-
    {X >= 1}, {Y =< 0},
    \+ X = Y.
test(unify_two_constrained_ok) :-
    {X >= 1}, {Y =< 3},
    X = Y,
    inf(X, I), sup(X, S),
    assertion(near(I,1.0)),
    assertion(near(S,3.0)).
test(unify_propagates_equation) :-
    {X + Y =:= 1},
    X = Y,
    assertion(near(X, 0.5)).
test(clp_type_r) :-
    {X > 1},
    clp_type(X, T),
    assertion(T == clpr).
test(clp_type_unconstrained, fail) :-
    clp_type(_, _).
test(mix_clpr_clpq, error(permission_error(_,_,_))) :-
    {X > 1},
    clpq:{X > 2}.
test(mix_clpr_clpq_unify, error(permission_error(_,_,_))) :-
    {X > 1},
    clpq:{Y > 2},
    X = Y.

:- end_tests(clpr_unify).

		 /*******************************
		 *      SOLVER INTERNALS	*
		 *******************************/

:- begin_tests(clpr_internals).

test(fresh_strict_upper) :-
    {X < 0},
    sup(X, S),
    assertion(near(S, 0.0)),
    assertion(\+ {X =:= 0}).
test(fresh_strict_lower) :-
    {X > 0},
    inf(X, I),
    assertion(near(I, 0.0)),
    assertion(\+ {X =:= 0}).
test(fresh_nonstrict_upper) :-
    {X =< 0},
    sup(X, S),
    assertion(near(S, 0.0)),
    {X =:= 0}.
test(fresh_nonstrict_lower) :-
    {X >= 0},
    inf(X, I),
    assertion(near(I, 0.0)),
    {X =:= 0}.
test(ground_inequality_after_aliasing) :-
    {X =:= Y},
    {X - Y =< 1},
    assertion(\+ {X - Y < 0}),
    {X - Y =< 0}.
test(bound_on_dependent_variable) :-
    {Z =:= _X + _Y},
    {Z >= 1, Z =< 3},
    dump([Z], [z], C),
    assertion(C = [z >= _, z =< _]).
test(lower_bound_repair) :-
    {X =< 5, Y =< 5},
    {Z =:= X + Y},
    {Z >= 8},
    inf(X, I),
    assertion(near(I, 3.0)).
test(implied_bound_narrowing) :-
    {X >= 0, X =< 10, Y >= 0, Y =< 1, X =< Y},
    sup(X, S),
    assertion(near(S, 1.0)).
test(unbounded_culprit) :-
    {X >= 0},
    {Y =:= X + 1},
    {Y =< 100},
    {X =< 200},
    sup(X, S),
    assertion(near(S, 99.0)).
test(chained_classes) :-
    {A + B =:= 1, B + C =:= 2, C + D =:= 3},
    {A =:= 0},
    assertion(near(B,1.0)),
    assertion(near(C,1.0)),
    assertion(near(D,2.0)).
test(simplex_three_variables) :-
    { X >= 0, Y >= 0, Z >= 0,
      X + Y + Z =< 10,
      X + 2*Y =< 8,
      Y + 3*Z =< 9 },
    sup(X + Y + Z, S),
    assertion(near(S, 10.0)).
test(strict_slack) :-
    {X + Y < 1, X > 0, Y > 0},
    sup(X, S),
    assertion(near(S, 1.0)),
    assertion(\+ {X =:= 1}).
test(nonzero_with_bound) :-
    {X =\= 0},
    {X >= 0},
    \+ {X =:= 0}.
test(fourier_motzkin_two_sided) :-
    {X - Y =< 1, Y - X =< 1, Y >= 0, Y =< 10},
    dump([X], [x], C),
    assertion(C = [x >= _, x =< _]).

% Aliasing variables with different bound types re-posts the bounds of one
% on the other (verify_type_var/5 in itf_r.pl).

test(alias_upper_with_lower) :-
    {X =< 5}, {Y >= 0},
    X = Y,
    inf(X, I), sup(X, S),
    assertion(near(I, 0.0)),
    assertion(near(S, 5.0)).
test(alias_two_intervals) :-
    {X >= 1, X =< 5}, {Y >= 2, Y =< 9},
    X = Y,
    inf(X, I), sup(X, S),
    assertion(near(I, 2.0)),
    assertion(near(S, 5.0)).
test(alias_strict_bounds) :-
    {X > 1}, {Y < 5},
    X = Y,
    assertion(\+ {X =:= 1}),
    assertion(\+ {X =:= 5}).
test(alias_strict_intervals) :-
    {X > 1, X < 9}, {Y > 0, Y < 5},
    X = Y,
    dump([X], [x], C),
    assertion(C = [x > _, x < _]).
test(alias_after_pivoting) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X, _),
    {Z >= 2},
    X = Z,
    inf(X, I),
    assertion(near(I, 2.0)).

% Several delayed goals on one variable.

test(two_delayed_goals, [nondet]) :-
    {X*Y =:= 6},
    {X*Z =:= 12},
    {X =:= 2},
    assertion(near(Y, 3.0)),
    assertion(near(Z, 6.0)).
test(nonlinear_residual_is_reported_once) :-
    {X*Y =:= 6},
    copy_term(X-Y, _, Gs),
    assertion(Gs = [{_}]).
test(unrelated_stores_are_reported_separately) :-
    {X*Y =:= 6},
    {A + B =:= 1},
    copy_term(f(X,Y,A,B), _, Gs),
    assertion(Gs = [{_},{_}]).
test(alias_across_delayed_goals, [nondet]) :-
    {X*Y =:= 6},
    {Z*W =:= 12},
    Y = Z,
    {X =:= 2},
    assertion(near(Y, 3.0)),
    assertion(near(W, 4.0)).

% Projections leaving active bounds and mixed strictness behind.

test(project_strict_system) :-
    {X > 0, Y > 0, X + Y < 10, X - Y > -5},
    dump([X], [x], C),
    assertion(C = [x < _, x > _]).
test(project_with_equality) :-
    {X >= 0, Y >= 0, Z >= 0, X + Y + Z =:= 1, X =< Y},
    dump([X,Y], [x,y], C),
    assertion(C = [x-y =< _, x+y =< _, x >= _]).
test(project_mixed_strictness) :-
    {X >= 1, X < 5, Y > 1, Y =< 5, X + Y =:= 4},
    dump([X,Y], [x,y], C),
    assertion(C = [y = _-x, x < _, x >= _]).
test(project_after_optimisation) :-
    {X >= 1, Y >= 1, X + Y =< 6},
    sup(X + Y, _),
    dump([X,Y], [x,y], C),
    assertion(C = [y >= _, x+y =< _, x >= _]).
test(project_strict_interval) :-
    {X > 0, X < 10, Y > 0, Y < 10, X + Y =< 5},
    dump([X,Y], [x,y], C),
    assertion(C = [y > _, x+y =< _, x > _]).

% Ground evaluation of the non-linear functions (nl_eval/2).

test(eval_sin) :-
    {X =:= sin(0)},
    assertion(near(X, 0.0)).
test(eval_cos) :-
    {X =:= cos(0)},
    assertion(near(X, 1.0)).
test(eval_tan) :-
    {X =:= tan(0)},
    assertion(near(X, 0.0)).

% Trivially true and trivially false ground inequalities.

test(ground_leq) :-
    {0 =< 0}.
test(ground_geq) :-
    {1 >= 1}.
test(ground_lt, fail) :-
    {0 < 0}.

% Non-linear comparisons other than equality are delayed too.

test(nonlinear_lt_delayed) :-
    {X*Y < 0},
    assertion((var(X),var(Y))).
test(nonlinear_le_delayed) :-
    {X*_Y =< 0},
    assertion(var(X)).
test(nonlinear_lt_woken, [nondet]) :-
    {X*Y < 6},
    {X =:= 2},
    dump([Y], [y], C),
    assertion(C = [y < _]).

% Residual goals for each kind of delayed constraint (transg//1).

test(residual_nonlinear_le) :-
    {X*Y =< 6},
    dump([X,Y], [x,y], C),
    assertion(C = [_ + y*x =< _]).
test(residual_nonlinear_lt) :-
    {X*Y < 6},
    dump([X,Y], [x,y], C),
    assertion(C = [_ + y*x < _]).
test(residual_nonlinear_ne) :-
    {X*Y =\= 6},
    dump([X,Y], [x,y], C),
    assertion(C = [_ + y*x =\= _]).
test(residual_negative_exponent) :-
    {X =:= 1/Y},
    dump([X,Y], [x,y], C),
    assertion(C = [x - _/y = _]).
test(residual_nested_function) :-
    {X =:= sin(Y+1)},
    dump([X,Y], [x,y], C),
    assertion(C = [x - sin(_+y) = _]).

% Optimisation of an expression that is not yet linear waits.

test(minimize_waits_for_linear, [nondet]) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    {X =:= 1},
    assertion(near(X, 1.0)),
    assertion(near(Y, 1.0)).
test(inf_of_nonlinear_waits, [nondet]) :-
    {Y >= 1, Y =< 5},
    inf(X*Y, I),
    {X =:= 1},
    assertion(near(I, 1.0)).

% Division by a non-constant.

test(division_by_expression, [nondet]) :-
    {X =:= 1/(Y+1)},
    {Y =:= 1},
    assertion(near(X, 0.5)).

% Wide expressions take the recursive branches of the logarithmic helpers.

test(wide_product, [nondet]) :-
    {Z =:= (A+B+C+D+E)*(A+B+C+D+E)},
    {A =:= 1, B =:= 1, C =:= 1, D =:= 1, E =:= 1},
    assertion(near(Z, 25.0)).
test(wide_repair, [nondet]) :-
    {Z =:= A*B + C*D + E*F},
    {A =:= 1, B =:= 2, C =:= 3, D =:= 4, E =:= 5, F =:= 6},
    assertion(near(Z, 44.0)).
test(entailed_disequation) :-
    {X =:= 4},
    entailed(X =\= 3).

:- end_tests(clpr_internals).

		 /*******************************
		 *          EXAMPLES		*
		 *******************************/

:- begin_tests(clpr_examples).

% The mortgage relation from the OFAI manual / the Monash examples.

mg(P, T, I, B, MP) :-
    {T = 1, B + MP =:= P * (1 + I)}.
mg(P, T, I, B, MP) :-
    {T > 1, P1 =:= P*(1+I) - MP, T1 =:= T - 1},
    mg(P1, T1, I, B, MP).

test(mortgage_forward) :-
    mg(1000, 3, 0.1, B, 400),
    !,
    assertion(near(B, 7.0)).
test(mortgage_backward) :-
    mg(P, 3, 0.1, 0, 400),
    !,
    assertion(near(P, 1324000/1331)).
test(mortgage_relation) :-
    mg(P, 3, 0.1, B, MP),
    !,
    dump([P,B,MP], [p,b,mp], C),
    assertion(C = [b = _*p - _*mp]).

% Fibonacci, forwards and backwards.  Note that the base cases must be
% written as constraints: CLP(R) binds its variables to *floats*, so a
% clause head fib(0,0) would not unify with the 0.0 the solver produces.

fib(N, F) :- {N =:= 0, F =:= 0}.
fib(N, F) :- {N =:= 1, F =:= 1}.
fib(N, F) :-
    {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1 + F2},
    fib(N1, F1),
    fib(N2, F2).

test(fib_forward) :-
    fib(10, F), !,
    assertion(near(F, 55.0)).
test(fib_backward) :-
    fib(N, 55.0), !,
    assertion(near(N, 10.0)).
test(fib_integer_head_does_not_unify, fail) :-
    % the reason for the base cases above
    int_fib(10, _).

int_fib(0, 0).
int_fib(1, 1).
int_fib(N, F) :-
    {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1 + F2},
    int_fib(N1, F1),
    int_fib(N2, F2).

test(convex_combination) :-
    { A >= 0, B >= 0, C >= 0,
      A + B + C =:= 1,
      X =:= 1*A + 4*B + 9*C },
    inf(X, Min), sup(X, Max),
    assertion(near(Min, 1.0)),
    assertion(near(Max, 9.0)).

% The "Variable Ordering" section of OFAI TR-95-09 works these examples
% with the 12 period mortgage.  They are reproduced here verbatim; note
% that assertion/1 does not keep bindings, so the shape is matched with
% plain unification and only the coefficients are asserted.

test(ordering_manual_plain) :-
    % {B=1.1268250301319698*P-12.682503013196973*Mp}
    mg(P, 12, 0.01, B, Mp), !,
    dump([P,B,Mp], [p,b,mp], C),
    C = [b = Cp*p - Cm*mp],
    assertion(near(Cp, 1.1268250301319698)),
    assertion(near(Cm, 12.682503013196973)).
test(ordering_manual_mp) :-
    % "instead of B, you want Mp to be the defined variable":
    % {Mp= -0.0788487886783417*B+0.08884878867834171*P}
    mg(P, 12, 0.01, B, Mp), !,
    ordering([Mp]),
    dump([P,B,Mp], [p,b,mp], C),
    C = [mp = Cb*b + Cp*p],
    assertion(near(Cb, -0.0788487886783417)),
    assertion(near(Cp, 0.08884878867834171)).
test(ordering_manual_mp_p) :-
    % "require P to appear before (to the left of) B in an addition":
    % {Mp=0.08884878867834171*P-0.0788487886783417*B}
    mg(P, 12, 0.01, B, Mp), !,
    ordering([Mp,P]),
    dump([P,B,Mp], [p,b,mp], C),
    C = [mp = Cp*p - Cb*b],
    assertion(near(Cp, 0.08884878867834171)),
    assertion(near(Cb, 0.0788487886783417)).
test(ordering_manual_before_constraints) :-
    % "ordering/1 acts like a constraint: you can put it anywhere in the
    % computation": {B= -12.682503013196973*Mp+1.1268250301319698*P}
    ordering(B < Mp),
    mg(P, 12, 0.01, B, Mp), !,
    dump([P,B,Mp], [p,b,mp], C),
    C = [b = Cm*mp + Cp*p],
    assertion(near(Cm, -12.682503013196973)),
    assertion(near(Cp, 1.1268250301319698)).

% Newton's method for sqrt(2), from the OFAI manual's precision section.

newton(X, X0, X1) :-
    {X1 =:= X0 - (X0*X0 - X)/(2*X0)}.

test(newton_sqrt2) :-
    newton(2, 1.0, A),
    newton(2, A, B),
    newton(2, B, C),
    newton(2, C, D),
    newton(2, D, E),
    assertion(near(E, 1.4142135623730951)).

:- end_tests(clpr_examples).

		 /*******************************
		 *        KNOWN ISSUES		*
		 *******************************/

:- begin_tests(clpr_known_issues).

% See doc/design.md, section 14.

test(division_by_zero_does_not_raise, fail) :-
    {_ =:= 1/0}.

test(waking_leaves_choicepoint, [nondet]) :-
    {X*Y =:= 6},
    {X =:= 2},
    assertion(near(Y, 3.0)).

:- end_tests(clpr_known_issues).
