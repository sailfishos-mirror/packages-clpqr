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

:- module(test_clpq,
          [ test_clpq/0
          ]).
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(clpq)).
:- use_module(library(clpr), []).          % for the solver-mixing tests

/** <module> Test CLP(Q)

Tests for library(clpq).  The structure follows doc/design.md.  Tests in
the unit `clpq_known_issues` pin down behaviour that is *wrong*; they are
there to make sure a fix is noticed, and each carries a comment saying
what the answer should be.

@see doc/design.md
*/

test_clpq :-
    run_tests([ clpq_syntax,
                clpq_nf,
                clpq_equations,
                clpq_inequalities,
                clpq_disequations,
                clpq_nonlinear,
                clpq_entailment,
                clpq_optimisation,
                clpq_bb,
                clpq_projection,
                clpq_residuals,
                clpq_unify,
                clpq_examples,
                clpq_internals,
                clpq_known_issues
              ]).

		 /*******************************
		 *           SYNTAX		*
		 *******************************/

:- begin_tests(clpq_syntax).

test(conjunction) :-
    {X > 1, X < 3, X =:= 2},
    assertion(X == 2).
test(nested_conjunction) :-
    {(X =:= 1, Y =:= 2)},
    assertion(X-Y == 1-2).
test(disjunction, all(X == [1,2])) :-
    {X =:= 1 ; X =:= 2}.
test(less) :-
    {X < 3, X > 2, X =:= 5r2}.
test(greater) :-
    {3 > X, 2 < X, X =:= 5r2}.
test(leq) :-
    {X =< 3, X >= 3},
    assertion(X == 3).
test(leq_alt) :-
    {<=(X, 3)}, {X >= 3},
    assertion(X == 3).
test(eq_is) :-
    {X =:= 3},
    assertion(X == 3).
test(eq_unify) :-
    {X = 3},
    assertion(X == 3).
test(unary_minus) :-
    {X =:= -(-3)},
    assertion(X == 3).
test(unary_plus) :-
    {X =:= +3},
    assertion(X == 3).
test(division_exact) :-
    {X =:= 1/3},
    assertion(X == 1r3).
test(float_is_rationalized) :-
    {X =:= 1.5},
    assertion(X == 3r2).
test(abs) :-
    {X =:= abs(-7)},
    assertion(X == 7).
test(min) :-
    {X =:= min(3,4)},
    assertion(X == 3).
test(max) :-
    {X =:= max(3,4)},
    assertion(X == 4).
test(pow) :-
    {X =:= pow(2,10)},
    assertion(X == 1024).
test(hat) :-
    {X =:= 2^10},
    assertion(X == 1024).
test(exp2) :-
    {X =:= exp(2,10)},
    assertion(X == 1024).
test(negative_power) :-
    {X =:= 2^(-2)},
    assertion(X == 1r4).
test(zero_power) :-
    {X =:= 5^0},
    assertion(X == 1).

% Errors

test(var_constraint, throws(instantiation_error({_},1))) :-
    {_}.
test(bad_constraint, error(type_error(clpq_constraint, foo))) :-
    {foo}.
test(bad_expression, error(type_error(clpq_expression, a))) :-
    {_ =:= a}.
test(star_star_rejected, error(type_error(clpq_expression, 2**3))) :-
    {_ =:= 2**3}.
test(sqrt_rejected, error(type_error(clpq_expression, sqrt(4)))) :-
    {_ =:= sqrt(4)}.
test(rdiv_rejected, error(type_error(clpq_expression, 1 rdiv 2))) :-
    X = 1 rdiv 2,
    {_ =:= X}.
test(entailed_var, error(instantiation_error)) :-
    entailed(_).
test(entailed_bad, error(type_error(clpq_constraint, foo))) :-
    entailed(foo).

:- end_tests(clpq_syntax).

		 /*******************************
		 *        NORMAL FORM		*
		 *******************************/

:- begin_tests(clpq_nf).

test(cancel) :-
    {X - X =:= 0}, var(X).
test(cancel_sum) :-
    {Y =:= X + 1 - X},
    assertion(Y == 1).
test(collect) :-
    {Y =:= 2*X + 3*X - 5*X},
    assertion(Y == 0).
test(distribute) :-
    {Y =:= (X+1)*(X-1) - X*X},
    assertion(Y == -1).
test(binomial) :-
    {Y =:= (X+1)^2 - X^2 - 2*X},
    assertion(Y == 1).
test(binomial_big) :-
    {Y =:= (1+X)^3 - (1 + 3*X + 3*X^2 + X^3)},
    assertion(Y == 0).
test(scalar_product) :-
    {X =:= 3*4}, assertion(X == 12).
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
    assertion(Z == 6).

:- end_tests(clpq_nf).

		 /*******************************
		 *          EQUATIONS		*
		 *******************************/

:- begin_tests(clpq_equations).

test(two_by_two) :-
    {2*X + 3*Y =:= 7, X - Y =:= 1},
    assertion(X-Y == 2-1).
test(three_by_three) :-
    { X + Y + Z =:= 6,
      X - Y + Z =:= 2,
      X + Y - Z =:= 0 },
    assertion([X,Y,Z] == [1,2,3]).
test(rational_solution) :-
    {3*X =:= 1},
    assertion(X == 1r3).
test(inconsistent, fail) :-
    {X + Y =:= 1, X + Y =:= 2}.
test(dependent_rows) :-
    {X + Y =:= 1, 2*X + 2*Y =:= 2},
    assertion((var(X),var(Y))).
test(implied_value) :-
    % A rank-2 system over two variables implies both values
    {X + Y =:= 3},
    assertion((var(X),var(Y))),
    {X - Y =:= 1},
    assertion(X-Y == 2-1).
test(class_merge) :-
    {X + Y =:= 1},
    {Z + W =:= 2},
    {Y =:= Z},
    {X =:= 0},
    assertion(Y == 1),
    assertion(Z == 1),
    assertion(W == 1).
test(alias) :-
    {X =:= Y}, {X =:= 1},
    assertion(Y == 1).
test(chain) :-
    {A =:= B, B =:= C, C =:= D, D =:= 7},
    assertion(A == 7).
test(negative_coefficients) :-
    {-X - Y =:= -3, X - Y =:= 1},
    assertion(X-Y == 2-1).
test(large_system) :-
    numlist(1, 30, Ns),
    length(Vs, 30),
    make_chain(Vs, Ns),
    last(Vs, Last),
    {Last =:= 0},
    nth1(1, Vs, First),
    assertion(integer(First)).

% V1-V2 =:= N1, V2-V3 =:= N2, ...
make_chain([_], [_]) :- !.
make_chain([A,B|T], [N|Ns]) :-
    {A - B =:= N},
    make_chain([B|T], Ns).

:- end_tests(clpq_equations).

		 /*******************************
		 *        INEQUALITIES		*
		 *******************************/

:- begin_tests(clpq_inequalities).

test(simple_bounds) :-
    {X >= 1, X =< 3},
    assertion(var(X)),
    inf(X, I), sup(X, S),
    assertion(I-S == 1-3).
test(meeting_bounds) :-
    {X >= 2, X =< 2},
    assertion(X == 2).
test(strict_meeting_bounds, fail) :-
    {X > 2, X =< 2}.
test(strict_both, fail) :-
    {X > 2, X < 2}.
test(empty_interval, fail) :-
    {X >= 3, X =< 2}.
test(tighten_lower) :-
    {X >= 1}, {X >= 2}, {X >= 0},
    assertion(\+ entailed(X >= 3)),
    assertion(entailed(X >= 2)).
test(tighten_upper) :-
    {X =< 5}, {X =< 3}, {X =< 9},
    assertion(entailed(X =< 3)),
    assertion(\+ entailed(X =< 2)).
test(strictness_kept) :-
    {X > 1},
    assertion(\+ {X =:= 1}),
    assertion(entailed(X >= 1)).
test(strictness_upgrade) :-
    {X >= 1}, {X > 1},
    assertion(\+ {X =:= 1}).
test(no_strictness_downgrade) :-
    {X > 1}, {X >= 1},
    assertion(\+ {X =:= 1}).
test(two_variables) :-
    {X + Y =< 10, X >= 0, Y >= 0},
    sup(X, S),
    assertion(S == 10).
test(triangle) :-
    {X >= 0, Y >= 0, X + Y =< 1},
    assertion(\+ {X =:= 1, Y =:= 1}),
    {X =:= 1},
    assertion(Y == 0).
test(unbounded_sup, fail) :-
    {X >= 0},
    sup(X, _).
test(unbounded_inf, fail) :-
    {X =< 0},
    inf(X, _).
test(transitive) :-
    {X =< Y, Y =< Z, Z =< X},
    {X =:= 1},
    assertion(Y-Z == 1-1).
test(transitive_strict, fail) :-
    {X < Y, Y < Z, Z < X}.
test(slack_elimination) :-
    % 12 constraints over 4 variables, all implying a single point
    { A >= 0, B >= 0, C >= 0, D >= 0,
      A + B + C + D =< 4,
      A + B + C + D >= 4,
      A =< 1, B =< 1, C =< 1, D =< 1 },
    assertion([A,B,C,D] == [1,1,1,1]).
test(negative_bounds) :-
    {X =< -5},
    assertion(entailed(X < 0)),
    sup(X, S),
    assertion(S == -5).
test(scaled_bound) :-
    {3*X =< 7},
    sup(X, S),
    assertion(S == 7r3).
test(mixed_eq_ineq) :-
    {X + Y =:= 10, X >= 0, Y >= 0},
    inf(X, I), sup(X, S),
    assertion(I-S == 0-10).

:- end_tests(clpq_inequalities).

		 /*******************************
		 *        DISEQUATIONS		*
		 *******************************/

:- begin_tests(clpq_disequations).

test(ground_true) :-
    {1 =\= 2}.
test(ground_false, fail) :-
    {1 =\= 1}.
test(delayed_ok) :-
    {X =\= 3},
    {X =:= 4},
    assertion(X == 4).
test(delayed_violated, fail) :-
    {X =\= 3},
    {X =:= 3}.
test(delayed_violated_unify, fail) :-
    {X =\= 3},
    X = 3.
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
    assertion(C == [x =\= 3]).

:- end_tests(clpq_disequations).

		 /*******************************
		 *         NON-LINEAR		*
		 *******************************/

:- begin_tests(clpq_nonlinear).

test(delayed_product, [nondet]) :-
    {X*Y =:= 6},
    assertion((var(X), var(Y))),
    {X =:= 2},
    assertion(Y == 3).
test(delayed_product_other_way, [nondet]) :-
    {X*Y =:= 6},
    {Y =:= 3},
    assertion(X == 2).
test(square_root_is_delayed) :-
    % CLP(Q) cannot invert X^2 = 4, so the constraint just residuates
    {X*X =:= 4},
    assertion(var(X)).
test(square_checked_on_binding) :-
    {X*X =:= 4}, {X =:= 2}.
test(square_violation_detected, fail) :-
    {X*X =:= 4}, {X =:= 3}.
test(division_delayed, [nondet]) :-
    {X/Y =:= 2},
    {Y =:= 3},
    assertion(X == 6).
test(abs_delayed, [nondet]) :-
    {X =:= abs(Y)},
    {Y =:= -4},
    assertion(X == 4).
test(min_delayed, [nondet]) :-
    {X =:= min(Y,3)},
    {Y =:= 1},
    assertion(X == 1).
test(max_delayed, [nondet]) :-
    {X =:= max(Y,3)},
    {Y =:= 5},
    assertion(X == 5).
test(invert_sin) :-
    {0 =:= sin(X)},
    assertion(X == 0).
test(invert_cos) :-
    {1 =:= cos(X)},
    assertion(X == 0).
test(invert_tan) :-
    {0 =:= tan(X)},
    assertion(X == 0).
test(invert_exp_base) :-
    {8 =:= 2^Y},
    assertion(Y == 3).
test(invert_exp_base_rounding) :-
    % log(1000)/log(10) is 2.9999999999999996 in floating point
    {1000 =:= 10^Y},
    assertion(Y == 3).
test(invert_exp_base_large) :-
    {59049 =:= 3^Y},
    assertion(Y == 10).
test(invert_exp_base_negative) :-
    {1r8 =:= 2^Y},
    assertion(Y == -3).
test(invert_exp_base_fractional) :-
    {2 =:= 8^Y},
    assertion(Y == 1r3).
test(invert_exp_base_unity) :-
    {1 =:= 2^Y},
    assertion(Y == 0).
test(invert_exp_base_irrational) :-
    % log2(3) is irrational: the best we can do is the simplest rational
    % that maps back to the same float
    {3 =:= 2^Y},
    assertion(rational(Y)),
    assertion(abs(Y - 1.584962500721156) < 1r1000000000000000).
test(invert_exp_exponent) :-
    % the other branch of nl_invertible/4: X and Z ground in X = Y^Z
    {8 =:= Y^2.5},
    assertion(rational(Y)),
    assertion(abs(Y - 2.2973967099940698) < 1r1000000000000000).
test(nonlinear_becomes_linear, [nondet]) :-
    {Z =:= X*_Y + 1},
    {X =:= 0},
    assertion(Z == 1).
test(goal_runs_once, [nondet]) :-
    % X and Y in one delayed goal; binding both must not run it twice
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
    assertion(Y == 8).

:- end_tests(clpq_nonlinear).

		 /*******************************
		 *         ENTAILMENT		*
		 *******************************/

:- begin_tests(clpq_entailment).

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
test(strict_bound) :-
    {X > 1},
    entailed(X >= 1),
    \+ entailed(X > 1 + 1r1000000).
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

:- end_tests(clpq_entailment).

		 /*******************************
		 *        OPTIMISATION		*
		 *******************************/

:- begin_tests(clpq_optimisation).

test(inf_simple) :-
    {X >= 1, X =< 5},
    inf(X, I),
    assertion(I == 1).
test(sup_simple) :-
    {X >= 1, X =< 5},
    sup(X, S),
    assertion(S == 5).
test(inf_does_not_bind) :-
    {X >= 1, X =< 5},
    inf(X, _),
    assertion(var(X)),
    sup(X, S),
    assertion(S == 5).
test(inf_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I),
    assertion(I == 2).
test(sup_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X + Y, S),
    assertion(S == 4).
test(inf_rational) :-
    {3*X >= 1},
    inf(X, I),
    assertion(I == 1r3).
test(inf_vertex) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I, [X,Y], V),
    assertion(I == 2),
    assertion(V == [1,1]).
test(sup_vertex) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X + Y, S, [X,Y], V),
    assertion(S == 4),
    assertion(sum_of(V, 4)).
test(minimize) :-
    {X >= 2, X =< 7},
    minimize(X),
    assertion(X == 2).
test(maximize) :-
    {X >= 2, X =< 7},
    maximize(X),
    assertion(X == 7).
test(minimize_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    minimize(X + Y),
    assertion(X == 1),
    assertion(Y == 1).
test(maximize_expression) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    maximize(X + Y),
    assertion(entailed(X + Y =:= 4)).
test(lp_diet) :-
    % Minimise 2*A + 3*B subject to a couple of covering constraints
    { A >= 0, B >= 0,
      A + 2*B >= 4,
      3*A + B >= 6 },
    inf(2*A + 3*B, I),
    assertion(I == 34r5).
test(unbounded_inf_fails, fail) :-
    {X >= 0},
    inf(-X, _).
test(strict_bound_infimum) :-
    % The infimum of a strictly bounded expression is the open bound
    {X > 1, X =< 5},
    inf(X, I),
    assertion(I == 1).
test(inf_waits_for_linear, [nondet]) :-
    {X*Y >= 3},
    {X =:= 1},
    inf(Y, I),
    assertion(I == 3).

sum_of(L, S) :-
    foldl([X,A0,A]>>(A is A0+X), L, 0, S).

:- end_tests(clpq_optimisation).

		 /*******************************
		 *      BRANCH AND BOUND	*
		 *******************************/

:- begin_tests(clpq_bb).

test(single_variable) :-
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, I),
    assertion(I == 1).
test(single_variable_vertex) :-
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, I, V),
    assertion(I == 1),
    assertion(V == [1]).
test(two_variables) :-
    {X >= 0, Y >= 0, X + Y >= 1},
    bb_inf([X,Y], X + Y, I),
    assertion(I == 1).
test(fractional_optimum) :-
    % LP optimum is 1/2, MIP optimum is 1
    {2*X >= 1, X >= 0},
    bb_inf([X], X, I),
    assertion(I == 1).
test(does_not_bind) :-
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, _),
    assertion(var(X)),
    inf(X, LpInf),
    assertion(LpInf == 1r2).
test(strict_bound) :-
    {X > 1, X =< 5},
    bb_inf([X], X, I),
    assertion(I == 2).
test(knapsack) :-
    { A >= 0, B >= 0,
      A =< 3, B =< 3,
      2*A + 3*B >= 7 },
    bb_inf([A,B], A + B, I),
    assertion(I == 3).
test(objective_not_integral) :-
    % Only X is required to be integral
    {X >= 1r2, Y >= 1r4},
    bb_inf([X], X + Y, I),
    assertion(I == 5r4).
test(ground_integer_ok) :-
    {X >= 0},
    bb_inf([2], X, I),
    assertion(I == 0).
test(ground_noninteger_fails, fail) :-
    {X >= 0},
    bb_inf([3r2], X, _).
test(unbounded_fails, fail) :-
    {X >= 0},
    bb_inf([X], -X, _).
test(does_not_touch_global_variables) :-
    % the incumbent used to live in the global variable `prov_opt'
    nb_setval(prov_opt, mine),
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, I),
    assertion(I == 1),
    nb_getval(prov_opt, V),
    assertion(V == mine),
    nb_delete(prov_opt).
test(nested_calls_do_not_interfere) :-
    {X >= 1r2, X =< 7r2},
    {Y >= 5r2, Y =< 9r2},
    bb_inf([X], X, I1),
    bb_inf([Y], Y, I2),
    bb_inf([X], X, I3),
    assertion([I1,I2,I3] == [1,3,1]).

:- end_tests(clpq_bb).

		 /*******************************
		 *         PROJECTION		*
		 *******************************/

:- begin_tests(clpq_projection).

test(empty) :-
    dump([], [], C),
    assertion(C == []).
test(unconstrained) :-
    dump([_], [x], C),
    assertion(C == []).
test(equation) :-
    {X + Y =:= 1},
    dump([X,Y], [x,y], C),
    assertion(C == [y = 1-x]).
test(bounds) :-
    {X >= 1, X =< 3},
    dump([X], [x], C),
    assertion(C == [x >= 1, x =< 3]).
test(strict_bounds) :-
    {X > 1, X < 3},
    dump([X], [x], C),
    assertion(C == [x > 1, x < 3]).
test(scaled) :-
    {2*X >= 1},
    dump([X], [x], C),
    assertion(C == [x >= 1r2]).
test(redundant_bounds_removed) :-
    {X >= 1, X >= 2, X >= 0},
    dump([X], [x], C),
    assertion(C == [x >= 2]).
test(projection_eliminates_variable) :-
    % Y only has a lower bound, so X is unconstrained after projection
    {X + Y >= 1, Y >= 0},
    dump([X], [x], C),
    assertion(C == []).
test(fourier_motzkin) :-
    % X =< Y =< Z implies X =< Z
    {X =< Y, Y =< Z},
    dump([X,Z], [x,z], C),
    assertion(C == [x-z =< 0]).
test(does_not_change_store) :-
    {X >= 1, X =< 3},
    dump([X], [x], _),
    inf(X, I), sup(X, S),
    assertion(I-S == 1-3).
test(nonlinear_residue) :-
    {X*Y =:= 6},
    dump([X,Y], [x,y], C),
    assertion(C = [_]).
test(target_order_does_not_control_shape) :-
    % dump/3 only interns its targets; it does not impose an ordering of
    % its own, so an explicit ordering/1 is never contradicted
    {X + Y =:= 1},
    dump([X,Y], [x,y], C1),
    dump([Y,X], [y,x], C2),
    assertion(C1 == C2).
test(ordering_list_controls_shape) :-
    % the variable that comes first is the one the answer defines
    {X + Y =:= 1},
    ordering([Y,X]),
    dump([X,Y], [x,y], C),
    assertion(C == [y = 1-x]).
test(ordering_list_controls_shape_2) :-
    {X + Y =:= 1},
    ordering([X,Y]),
    dump([X,Y], [x,y], C),
    assertion(C == [x = 1-y]).
test(ordering_lt_controls_shape) :-
    {X + Y =:= 1},
    ordering(Y < X),
    dump([X,Y], [x,y], C),
    assertion(C == [y = 1-x]).
test(ordering_gt_controls_shape) :-
    {X + Y =:= 1},
    ordering(X > Y),
    dump([X,Y], [x,y], C),
    assertion(C == [y = 1-x]).
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
    % "ordering/1 acts like a constraint: you can put it anywhere in the
    % computation" (OFAI TR-95-09)
    ordering([Y,X]),
    {X + Y =:= 1},
    dump([X,Y], [x,y], C),
    assertion(C == [y = 1-x]).
test(ordering_of_three) :-
    {X + Y + Z =:= 1},
    ordering([Z,Y,X]),
    dump([X,Y,Z], [x,y,z], C),
    assertion(C == [z = 1-y-x]).
test(target_must_be_free, error(uninstantiation_error(1))) :-
    {X =:= 1},
    dump([X], [x], _).
test(target_must_be_list, error(type_error(list(var), foo))) :-
    dump(foo, _, _).

:- end_tests(clpq_projection).

		 /*******************************
		 *         RESIDUALS		*
		 *******************************/

:- begin_tests(clpq_residuals).

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
test(copy_term_equation) :-
    {X + Y =:= 1},
    copy_term(X-Y, _, Gs),
    assertion(Gs = [{_}]).
test(pending_optimisation_is_reusable) :-
    % a minimize/1 that is still waiting for its expression to become
    % linear is reported as the user level goal that created it, so the
    % answer of copy_term/3 can be executed again
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    copy_term(f(X,Y), f(X2,Y2), Gs),
    assertion(Gs = [{_}, clpq:minimize(_)]),
    maplist(call, Gs),
    {X2 =:= 1},
    assertion(X2-Y2 == 1-1).
test(pending_inf_is_reported) :-
    {Y >= 1, Y =< 5},
    inf(X*Y, I),
    copy_term(f(X,Y,I), _, Gs),
    assertion(Gs = [{_}, clpq:inf(_,_,_,_)]).
test(dump_omits_pending_goals) :-
    % dump/3 returns constraints; a pending optimisation is not one
    {Y >= 1, Y =< 5},
    minimize(_X*Y),
    dump([Y], [y], C),
    assertion(C == [y >= 1, y =< 5]).
test(residual_is_reusable) :-
    {X >= 1, X =< 3},
    copy_term(X, Y, Gs),
    maplist(call, Gs),
    inf(Y, I), sup(Y, S),
    assertion(I-S == 1-3).

:- end_tests(clpq_residuals).

		 /*******************************
		 *        UNIFICATION		*
		 *******************************/

:- begin_tests(clpq_unify).

test(unify_number_ok) :-
    {X >= 1}, X = 2.
test(unify_number_violates, fail) :-
    {X >= 1}, X = 0.
test(unify_rational) :-
    {X >= 1r2}, X = 1r2.
test(unify_float_rejected, error(type_error(rational, 1.5))) :-
    % numbers_only/1 in itf_q.pl only accepts rationals on unification,
    % even though {X =:= 1.5} is fine.
    {X >= 1}, X = 1.5.
test(unify_atom_type_error, error(type_error(rational, a))) :-
    {X >= 1}, X = a.
test(unify_two_constrained) :-
    {X >= 1}, {Y =< 0},
    \+ X = Y.
test(unify_two_constrained_ok) :-
    {X >= 1}, {Y =< 3},
    X = Y,
    inf(X, I), sup(X, S),
    assertion(I-S == 1-3).
test(unify_propagates_equation) :-
    {X + Y =:= 1},
    X = Y,
    assertion(X == 1r2).
test(unify_independent_variable) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    X = Y,
    sup(X, S),
    assertion(S == 2).
test(clp_type_q) :-
    {X > 1},
    clp_type(X, T),
    assertion(T == clpq).
test(clp_type_unconstrained, fail) :-
    clp_type(_, _).
test(mix_clpq_clpr, error(permission_error(_,_,_))) :-
    {X > 1},
    clpr:{X > 2}.
test(mix_clpq_clpr_unify, error(permission_error(_,_,_))) :-
    {X > 1},
    clpr:{Y > 2},
    X = Y.

:- end_tests(clpq_unify).

		 /*******************************
		 *          EXAMPLES		*
		 *******************************/

:- begin_tests(clpq_examples).

% The mortgage relation from the OFAI manual / the Monash examples.
%
%   P  principal, T  periods, I  interest, B  balance, MP  monthly payment

mg(P, T, I, B, MP) :-
    {T = 1, B + MP =:= P * (1 + I)}.
mg(P, T, I, B, MP) :-
    {T > 1, P1 =:= P*(1+I) - MP, T1 =:= T - 1},
    mg(P1, T1, I, B, MP).

test(mortgage_forward) :-
    mg(1000, 3, 1/10, B, 400),
    !,
    % 1000*1.1^3 - 400*(1.1^2+1.1+1) = 1331 - 1324
    assertion(B == 7).
test(mortgage_backward) :-
    mg(P, 3, 1/10, 0, 400),
    !,
    assertion(P == 1324000r1331).
test(mortgage_relation) :-
    mg(P, 3, 1/10, B, MP),
    !,
    dump([P,B,MP], [p,b,mp], C),
    assertion(C == [b = 1331r1000*p - 331r100*mp]).

% Fibonacci run backwards; classic CLP(Q) example.

fib(0, 0).
fib(1, 1).
fib(N, F) :-
    {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1 + F2},
    fib(N1, F1),
    fib(N2, F2).

test(fib_forward) :-
    fib(10, F), !,
    assertion(F == 55).
test(fib_backward) :-
    fib(N, 55), !,
    assertion(N == 10).

% A small linear program: the "diet" shape.

test(convex_combination) :-
    { A >= 0, B >= 0, C >= 0,
      A + B + C =:= 1,
      X =:= 1*A + 4*B + 9*C },
    inf(X, Min), sup(X, Max),
    assertion(Min-Max == 1-9).

:- end_tests(clpq_examples).

		 /*******************************
		 *      SOLVER INTERNALS	*
		 *******************************/

% Scenarios chosen to exercise paths in bv_q.pl / ineq_q.pl that the
% behavioural tests above do not reach: bounds on fresh variables, bounds
% on *dependent* variables, lower-bound repair (inc_step/2), implied
% bound narrowing and slack introduction.

:- begin_tests(clpq_internals).

test(fresh_strict_upper) :-
    % {X < 0} on a variable the solver has never seen takes the
    % var_intern/3 branch of ineq_one_s_p_0/1
    {X < 0},
    sup(X, S),
    assertion(S == 0),
    assertion(\+ {X =:= 0}).
test(fresh_strict_lower) :-
    {X > 0},
    inf(X, I),
    assertion(I == 0),
    assertion(\+ {X =:= 0}).
test(fresh_nonstrict_upper) :-
    {X =< 0},
    sup(X, S),
    assertion(S == 0),
    {X =:= 0}.
test(fresh_nonstrict_lower) :-
    {X >= 0},
    inf(X, I),
    assertion(I == 0),
    {X =:= 0}.
test(ground_inequality_after_aliasing) :-
    % After X and Y are aliased, X-Y =< 1 dereferences to a constant row
    {X =:= Y},
    {X - Y =< 1},
    assertion(\+ {X - Y < 0}),
    {X - Y =< 0}.
test(bound_on_dependent_variable) :-
    {Z =:= X + Y},
    {Z >= 1, Z =< 3},
    dump([X,Y,Z], [x,y,z], C),
    assertion(C == [z >= 1, z =< 3, y = z-x]).
test(strict_bound_on_dependent_variable) :-
    {Z =:= _X + _Y},
    {Z > 1, Z < 3},
    dump([Z], [z], C),
    assertion(C == [z > 1, z < 3]).
test(lower_bound_repair) :-
    % Z is basic and below its lower bound, so the solver must *raise* the
    % rhs: this drives inc_step/2 rather than dec_step/2
    {X =< 5, Y =< 5},
    {Z =:= X + Y},
    {Z >= 8},
    inf(X, I),
    assertion(I == 3).
test(implied_bound_narrowing) :-
    % sup(X) is limited to 1 by Y, which the optimiser only finds by
    % pivoting and then narrowing X's upper bound
    {X >= 0, X =< 10, Y >= 0, Y =< 1, X =< Y},
    sup(X, S),
    assertion(S == 1).
test(unbounded_culprit) :-
    {X >= 0},
    {Y =:= X + 1},
    {Y =< 100},
    {X =< 200},
    sup(X, S),
    assertion(S == 99).
test(two_sided_dump) :-
    {X >= 1, X =< 5, Y >= 1, Y =< 5, X + Y =:= 4},
    dump([X,Y], [x,y], C),
    assertion(C == [y = 4-x, x =< 3, x >= 1]).
test(chained_classes) :-
    {A + B =:= 1, B + C =:= 2, C + D =:= 3},
    {A =:= 0},
    assertion([B,C,D] == [1,1,2]).
test(simplex_three_variables) :-
    { X >= 0, Y >= 0, Z >= 0,
      X + Y + Z =< 10,
      X + 2*Y =< 8,
      Y + 3*Z =< 9 },
    sup(X + Y + Z, S),
    assertion(S == 10).
test(strict_slack) :-
    {X + Y < 1, X > 0, Y > 0},
    sup(X, S),
    assertion(S == 1),
    assertion(\+ {X =:= 1}).
test(equality_inside_bounds) :-
    {X >= 1, X =< 5},
    {X =:= 3},
    assertion(X == 3).
test(equality_outside_bounds) :-
    {X >= 1, X =< 5},
    \+ {X =:= 6}.
test(nonzero_on_expression) :-
    {X + Y =\= 1},
    dump([X,Y], [x,y], C),
    assertion(C == [x+y =\= 1]).
test(nonzero_with_bound) :-
    {X =\= 0},
    {X >= 0},
    \+ {X =:= 0}.
test(fourier_motzkin_chain) :-
    {X =< Y, Y =< Z, Z =< W},
    dump([X,W], [x,w], C),
    assertion(C == [x-w =< 0]).
test(fourier_motzkin_two_sided) :-
    {X - Y =< 1, Y - X =< 1, Y >= 0, Y =< 10},
    dump([X], [x], C),
    assertion(C == [x >= -1, x =< 11]).
test(redundant_two_sided) :-
    {X >= 1, X =< 5, X >= 0, X =< 10},
    dump([X], [x], C),
    assertion(C == [x >= 1, x =< 5]).
test(redundant_strictness) :-
    {X > 1, X >= 1, X < 5, X =< 5},
    dump([X], [x], C),
    assertion(C == [x > 1, x < 5]).
test(maximize_then_constrain) :-
    {X >= 1, X =< 5},
    maximize(X),
    {X =:= 5}.

% Aliasing two variables that carry different bound types makes
% attr_unify_hook/2 re-post the bounds of one on the other
% (verify_type_var/5 and friends in itf_q.pl).

test(alias_upper_with_lower) :-
    {X =< 5}, {Y >= 0},
    X = Y,
    inf(X, I), sup(X, S),
    assertion(I-S == 0-5).
test(alias_two_intervals) :-
    {X >= 1, X =< 5}, {Y >= 2, Y =< 9},
    X = Y,
    inf(X, I), sup(X, S),
    assertion(I-S == 2-5).
test(alias_strict_bounds) :-
    {X > 1}, {Y < 5},
    X = Y,
    assertion(\+ {X =:= 1}),
    assertion(\+ {X =:= 5}).
test(alias_strict_intervals) :-
    {X > 1, X < 9}, {Y > 0, Y < 5},
    X = Y,
    dump([X], [x], C),
    assertion(C == [x > 1, x < 5]).
test(alias_after_pivoting) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X, _),
    {Z >= 2},
    X = Z,
    inf(X, I),
    assertion(I == 2).

% Several delayed goals on one variable exercise the conjunction cases of
% geler.pl's trans//1 and transg//1.

test(two_delayed_goals, [nondet]) :-
    {X*Y =:= 6},
    {X*Z =:= 12},
    {X =:= 2},
    assertion(Y-Z == 3-6).
test(two_delayed_goals_residual) :-
    {X*_Y =:= 6},
    {X*_Z =:= 12},
    copy_term(X, _, Gs),
    assertion(Gs = [{_}]).
test(nonlinear_residual_is_reported_once) :-
    % every variable of a purely non-linear store carries the same delayed
    % goal; attribute_goals//1 must report the conjunction only once
    {X*Y =:= 6},
    copy_term(X-Y, _, Gs),
    assertion(Gs = [{_}]).
test(unrelated_stores_are_reported_separately) :-
    {X*Y =:= 6},
    {A + B =:= 1},
    copy_term(f(X,Y,A,B), _, Gs),
    assertion(Gs = [{_},{_}]).
test(alias_delayed_variables, [nondet]) :-
    {X*Y =:= 6},
    X = Y,
    assertion(var(X)).
test(alias_across_delayed_goals, [nondet]) :-
    {X*Y =:= 6},
    {Z*W =:= 12},
    Y = Z,
    {X =:= 2},
    assertion(Y == 3),
    assertion(W == 4).

% Projections that leave active bounds and mixed strictness behind,
% exercising the t_L/t_U/t_Lu/t_lU cases of redund.pl.

test(project_strict_system) :-
    {X > 0, Y > 0, X + Y < 10, X - Y > -5},
    dump([X], [x], C),
    assertion(C == [x < 10, x > 0]).
test(project_with_equality) :-
    {X >= 0, Y >= 0, Z >= 0, X + Y + Z =:= 1, X =< Y},
    dump([X,Y], [x,y], C),
    assertion(C == [x-y =< 0, x+y =< 1, x >= 0]).
test(project_mixed_strictness) :-
    {X >= 1, X < 5, Y > 1, Y =< 5, X + Y =:= 4},
    dump([X,Y], [x,y], C),
    assertion(C == [y = 4-x, x < 3, x >= 1]).
test(project_after_optimisation) :-
    {X >= 1, Y >= 1, X + Y =< 6},
    sup(X + Y, _),
    dump([X,Y], [x,y], C),
    assertion(C == [y >= 1, x+y =< 6, x >= 1]).
test(project_strict_interval) :-
    {X > 0, X < 10, Y > 0, Y < 10, X + Y =< 5},
    dump([X,Y], [x,y], C),
    assertion(C == [y > 0, x+y =< 5, x > 0]).

% Ground evaluation of the non-linear functions (nl_eval/2).

test(eval_sin) :-
    {X =:= sin(0)},
    assertion(X == 0).
test(eval_cos) :-
    {X =:= cos(0)},
    assertion(X == 1).
test(eval_tan) :-
    {X =:= tan(0)},
    assertion(X == 0).

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
test(nonlinear_eq_zero_delayed) :-
    {X*_Y =:= 0},
    assertion(var(X)).
test(nonlinear_lt_woken, [nondet]) :-
    {X*Y < 6},
    {X =:= 2},
    dump([Y], [y], C),
    assertion(C == [y < 3]).

% Residual goals for each kind of delayed constraint (transg//1).

test(residual_nonlinear_le) :-
    {X*Y =< 6},
    dump([X,Y], [x,y], C),
    assertion(C == [-6 + y*x =< 0]).
test(residual_nonlinear_lt) :-
    {X*Y < 6},
    dump([X,Y], [x,y], C),
    assertion(C == [-6 + y*x < 0]).
test(residual_nonlinear_ne) :-
    {X*Y =\= 6},
    dump([X,Y], [x,y], C),
    assertion(C == [-6 + y*x =\= 0]).
test(residual_negative_exponent) :-
    {X =:= 1/Y},
    dump([X,Y], [x,y], C),
    assertion(C == [x - 1/y = 0]).
test(residual_square) :-
    {X*X =:= 2},
    dump([X], [x], C),
    assertion(C == [-2 + x^2 = 0]).
test(residual_nested_function) :-
    {X =:= sin(Y+1)},
    dump([X,Y], [x,y], C),
    assertion(C == [x - sin(1+y) = 0]).

% Optimisation of an expression that is not yet linear waits
% (wait_linear_retry/3).

test(minimize_waits_for_linear, [nondet]) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    {X =:= 1},
    assertion(X == 1),
    assertion(Y == 1).
test(inf_of_nonlinear_waits, [nondet]) :-
    {Y >= 1, Y =< 5},
    inf(X*Y, I),
    {X =:= 1},
    assertion(I == 1).

% Division by a non-constant stays as an undigested quotient until the
% divisor is known (nf_div/3 third clause, repair_p_one/2).

test(division_by_expression, [nondet]) :-
    {X =:= 1/(Y+1)},
    {Y =:= 1},
    assertion(X == 1r2).

% Wide expressions take the recursive (N>2) branches of the logarithmic
% helpers nf_mul_log/6, nf_mul_factor_log/5, repair_log/4, repair_p_log/6.

test(wide_product, [nondet]) :-
    {Z =:= (A+B+C+D+E)*(A+B+C+D+E)},
    {A =:= 1, B =:= 1, C =:= 1, D =:= 1, E =:= 1},
    assertion(Z == 25).
test(wide_repair, [nondet]) :-
    {Z =:= A*B + C*D + E*F},
    {A =:= 1, B =:= 2, C =:= 3, D =:= 4, E =:= 5, F =:= 6},
    assertion(Z == 44).
test(entailed_disequation) :-
    {X =:= 4},
    entailed(X =\= 3).

:- end_tests(clpq_internals).

		 /*******************************
		 *        KNOWN ISSUES		*
		 *******************************/

:- begin_tests(clpq_known_issues).

% See doc/design.md, section 14.  These tests pin down *wrong* behaviour so
% that fixing it is noticed.  Each says what the right answer would be.

test(root_extraction_not_implemented) :-
    % The documented isolation axiom "8 = Y^3 with X and Z ground" is
    % implemented in CLP(R) only.  Should bind Y == 2.
    {8 =:= Y^3},
    assertion(var(Y)).

test(waking_leaves_choicepoint, [nondet]) :-
    % geler.pl's attr_unify_hook/2 has a catch-all second clause, and
    % run/2 has two clauses, so waking a delayed goal always leaves a
    % choice point even when the wake-up is deterministic.
    {X*Y =:= 6},
    {X =:= 2},
    assertion(Y == 3).

test(division_by_zero_does_not_raise, fail) :-
    % zero_division/0 is `fail' with the comment `% raise_exception(_) ?'.
    % An evaluation_error(zero_divisor) would be more useful.
    {_ =:= 1/0}.

:- end_tests(clpq_known_issues).
