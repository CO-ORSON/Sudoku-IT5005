"""Regression checks for the assignment's public solver functions.

Run from the project directory with ``python -m unittest discover -s tests -v``.
The JSON ``solution`` fields are read only here as independent expected results;
the solver receives only the dimensions, box dimensions, and givens.
"""

import ast
import itertools
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from logic_ import (
    PropDefiniteKB,
    PropKB,
    associate,
    expr,
    is_definite_clause,
    pl_fc_entails,
    pl_resolution,
    pl_true,
    tt_entails,
)
import sudoku_solver as solver


PROJECT_ROOT = Path(__file__).resolve().parents[1]
FOUR_BY_FOUR = {
    (r, c): value
    for r, row in enumerate(
        ((1, 2, 3, 4), (3, 4, 1, 2), (2, 1, 4, 3), (4, 3, 2, 1)),
        start=1,
    )
    for c, value in enumerate(row, start=1)
}


def read_cells(cells):
    """Decode the assignment's one-indexed JSON coordinate format."""
    return {tuple(map(int, key.split("_"))): value for key, value in cells.items()}


def make_horn_kb(*sentences):
    """Use the supplied definite-clause class for non-Sudoku inference tests."""
    kb = PropDefiniteKB()
    for sentence in sentences:
        kb.tell(expr(sentence))
    return kb


def grid_model(grid, n):
    """Map every candidate atom to a truth value for a concrete grid."""
    return {
        solver.atom("Is", r, c, v): grid.get((r, c)) == v
        for r in range(1, n + 1)
        for c in range(1, n + 1)
        for v in range(1, n + 1)
    }


def satisfies(kb, model):
    return all(pl_true(clause, model) is True for clause in kb.clauses)


class HornInferenceTests(unittest.TestCase):
    """Check soundness, conjunctions, cyclic dependencies, and KB changes."""

    def assert_agrees_with_library(self, kb, symbols):
        for name in symbols:
            with self.subTest(query=name):
                query = expr(name)
                self.assertIs(
                    solver.pl_bc_entails(kb, query), pl_fc_entails(kb, query)
                )

    def test_facts_conjunction_alternatives_and_unknown_query(self):
        kb = make_horn_kb(
            "A", "B", "(A & B) ==> C", "Missing ==> D", "C ==> D",
            "(A & Unknown) ==> Unprovable",
        )
        self.assert_agrees_with_library(
            kb, ("A", "B", "C", "D", "Missing", "Unknown", "Unprovable")
        )

    def test_unsupported_cycle_does_not_prove_itself(self):
        kb = make_horn_kb("A ==> B", "B ==> A", "A ==> A", "B ==> C")
        self.assert_agrees_with_library(kb, ("A", "B", "C"))
        self.assertFalse(solver.pl_bc_entails(kb, expr("A")))

    def test_supported_cycle_can_be_proved(self):
        kb = make_horn_kb("A ==> B", "B ==> A", "C ==> A", "C")
        self.assert_agrees_with_library(kb, ("A", "B", "C", "D"))

    def test_cycle_cutoff_must_not_cache_branch_failure_as_global_false(self):
        # While proving A, a naive DFS cuts B -> A as cyclic. After C proves A,
        # B becomes provable too: caching that first B failure breaks Q.
        clauses = (
            "B ==> A", "C ==> A", "A ==> B", "C", "(A & B) ==> Q"
        )
        for ordering in (clauses, tuple(reversed(clauses))):
            with self.subTest(ordering=ordering):
                kb = make_horn_kb(*ordering)
                self.assertTrue(solver.pl_bc_entails(kb, expr("Q")))
                self.assert_agrees_with_library(kb, ("A", "B", "Q", "Z"))

    def test_results_reflect_tell_and_retract(self):
        kb = make_horn_kb("A ==> B")
        self.assertFalse(solver.pl_bc_entails(kb, expr("B")))
        kb.tell(expr("A"))
        self.assertTrue(solver.pl_bc_entails(kb, expr("B")))
        kb.retract(expr("A"))
        self.assertFalse(solver.pl_bc_entails(kb, expr("B")))


class KnowledgeRepresentationTests(unittest.TestCase):
    def test_solver_imports_only_assignment_helpers(self):
        tree = ast.parse((PROJECT_ROOT / "sudoku_solver.py").read_text())
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                self.fail("The assignment allows imports only from utils and logic_.")
            if isinstance(node, ast.ImportFrom):
                self.assertIn(node.module, {"utils", "logic_"})

    def test_builders_return_supplied_kb_types(self):
        general = solver.build_general_kb(4, 2, 2, {(1, 1): 1})
        definite = solver.build_definite_kb(4, 2, 2, {(1, 1): 1})
        self.assertIsInstance(general, PropKB)
        self.assertIsInstance(definite, PropDefiniteKB)
        self.assertTrue(definite.clauses)
        self.assertTrue(all(is_definite_clause(c) for c in definite.clauses))

    def test_general_encoding_matches_all_two_by_two_truth_assignments(self):
        # Eight candidate atoms give only 256 models. This checks both missing
        # restrictions and accidental overrestriction of the general encoding.
        kb = solver.build_general_kb(2, 1, 2, {})
        atoms = [
            solver.atom("Is", r, c, v)
            for r in (1, 2) for c in (1, 2) for v in (1, 2)
        ]
        accepted_models = 0
        for values in itertools.product((False, True), repeat=len(atoms)):
            model = dict(zip(atoms, values))
            chosen = {
                (r, c): [v for v in (1, 2) if model[solver.atom("Is", r, c, v)]]
                for r in (1, 2) for c in (1, 2)
            }
            expected = all(len(cell) == 1 for cell in chosen.values())
            if expected:
                grid = {cell: candidates[0] for cell, candidates in chosen.items()}
                expected = all(
                    {grid[(r, c)] for c in (1, 2)} == {1, 2} for r in (1, 2)
                ) and all(
                    {grid[(r, c)] for r in (1, 2)} == {1, 2} for c in (1, 2)
                )
            with self.subTest(model=values):
                self.assertEqual(satisfies(kb, model), expected)
            accepted_models += int(expected)
        self.assertEqual(accepted_models, 2)

    def test_general_encoding_distinguishes_each_four_by_four_constraint(self):
        kb = solver.build_general_kb(4, 2, 2, {})
        valid = grid_model(FOUR_BY_FOUR, 4)
        self.assertTrue(satisfies(kb, valid))

        empty_cell = valid.copy()
        empty_cell[solver.atom("Is", 1, 1, 1)] = False
        self.assertFalse(satisfies(kb, empty_cell), "At least one value per cell")

        two_values = valid.copy()
        two_values[solver.atom("Is", 1, 1, 2)] = True
        self.assertFalse(satisfies(kb, two_values), "At most one value per cell")

        # Within-box swaps preserve boxes; horizontal swaps preserve rows,
        # and vertical swaps preserve columns. Each isolates a uniqueness rule.
        bad_columns = FOUR_BY_FOUR.copy()
        bad_columns[(1, 1)], bad_columns[(1, 2)] = 2, 1
        self.assertFalse(satisfies(kb, grid_model(bad_columns, 4)))
        bad_rows = FOUR_BY_FOUR.copy()
        bad_rows[(1, 1)], bad_rows[(2, 1)] = 3, 1
        self.assertFalse(satisfies(kb, grid_model(bad_rows, 4)))

        latin_square = {
            (r, c): (r + c - 2) % 4 + 1
            for r in range(1, 5) for c in range(1, 5)
        }
        self.assertFalse(satisfies(kb, grid_model(latin_square, 4)), "Box uniqueness")
        with_given = solver.build_general_kb(4, 2, 2, {(1, 1): 2})
        self.assertFalse(satisfies(with_given, valid), "Givens are mandatory")

    def test_general_kb_truth_table_and_resolution_on_small_cases(self):
        kb = solver.build_general_kb(2, 1, 2, {(1, 1): 1})
        sentence = associate("&", kb.clauses)
        self.assertTrue(tt_entails(sentence, solver.atom("Is", 2, 2, 1)))
        self.assertFalse(tt_entails(sentence, solver.atom("Is", 2, 2, 2)))
        empty = solver.build_general_kb(2, 1, 2, {})
        self.assertFalse(tt_entails(associate("&", empty.clauses), solver.atom("Is", 1, 1, 1)))

        # The provided resolution implementation is deliberately unindexed;
        # keep the CI regression tiny instead of saturating a 9x9 clause set.
        singleton = solver.build_general_kb(1, 1, 1, {})
        self.assertTrue(pl_resolution(singleton, solver.atom("Is", 1, 1, 1)))
        self.assertFalse(pl_resolution(singleton, expr("Unrelated")))

    def test_definite_kb_library_fc_and_bc_agree_on_every_small_grid_candidate(self):
        givens = {cell: value for cell, value in FOUR_BY_FOUR.items() if cell[0] != cell[1]}
        kb = solver.build_definite_kb(4, 2, 2, givens)
        for (r, c), actual in FOUR_BY_FOUR.items():
            for candidate in range(1, 5):
                with self.subTest(row=r, column=c, candidate=candidate):
                    query = solver.atom("Is", r, c, candidate)
                    self.assertIs(pl_fc_entails(kb, query), candidate == actual)
                    self.assertIs(solver.pl_bc_entails(kb, query), candidate == actual)
        self.assertEqual(solver.solve_full_grid_fc(4, 2, 2, givens), FOUR_BY_FOUR)
        self.assertEqual(solver.solve_full_grid_bc(4, 2, 2, givens), FOUR_BY_FOUR)

    def test_full_grid_fc_uses_the_supplied_algorithm(self):
        givens = {cell: value for cell, value in FOUR_BY_FOUR.items() if cell != (1, 1)}
        with patch.object(solver, "pl_fc_entails", wraps=pl_fc_entails) as library_fc:
            self.assertEqual(solver.solve_full_grid_fc(4, 2, 2, givens), FOUR_BY_FOUR)
            self.assertGreater(library_fc.call_count, 0)

    def test_single_cell_boundary_case(self):
        self.assertEqual(solver.solve_full_grid_fc(1, 1, 1, {}), {(1, 1): 1})
        self.assertEqual(solver.solve_full_grid_bc(1, 1, 1, {}), {(1, 1): 1})


class SuppliedPuzzleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pool = json.loads((PROJECT_ROOT / "puzzles.json").read_text())

    def test_both_algorithms_solve_all_five_supplied_puzzles(self):
        n, box_h, box_w = (self.pool[key] for key in ("n", "box_h", "box_w"))
        self.assertEqual(len(self.pool["puzzles"]), 5)
        for number, puzzle in enumerate(self.pool["puzzles"], start=1):
            givens = read_cells(puzzle["givens"])
            original_givens = givens.copy()
            expected = read_cells(puzzle["solution"])
            self.assertEqual(len(givens), puzzle["given_count"])
            for solve in (solver.solve_full_grid_fc, solver.solve_full_grid_bc):
                with self.subTest(puzzle=number, algorithm=solve.__name__):
                    result = solve(n, box_h, box_w, givens)
                    self.assertEqual(result, expected)
                    self.assertEqual(givens, original_givens, "Inputs must not be mutated")

    def test_all_729_backward_queries_in_first_puzzle_are_sound_and_complete(self):
        n, box_h, box_w = (self.pool[key] for key in ("n", "box_h", "box_w"))
        puzzle = self.pool["puzzles"][0]
        expected = read_cells(puzzle["solution"])
        kb = solver.build_definite_kb(n, box_h, box_w, read_cells(puzzle["givens"]))
        checked = 0
        for (r, c), actual in expected.items():
            for candidate in range(1, n + 1):
                with self.subTest(row=r, column=c, candidate=candidate):
                    self.assertIs(
                        solver.pl_bc_entails(kb, solver.atom("Is", r, c, candidate)),
                        candidate == actual,
                    )
                checked += 1
        self.assertEqual(checked, 729)


class InputAndUnresolvedTests(unittest.TestCase):
    def test_invalid_dimensions(self):
        for dimensions in ((0, 1, 1), (4, 0, 2), (4, 3, 2), (6, 2, 2)):
            for build in (solver.build_general_kb, solver.build_definite_kb):
                with self.subTest(dimensions=dimensions, builder=build.__name__):
                    with self.assertRaises(ValueError):
                        build(*dimensions, {})

    def test_out_of_bounds_or_malformed_givens(self):
        for givens in (
            {(0, 1): 1}, {(1, 5): 1}, {(1, 1): 0}, {(1, 1): 5},
            {"1_1": 1}, {(1, 1, 1): 1},
        ):
            for build in (solver.build_general_kb, solver.build_definite_kb):
                with self.subTest(givens=givens, builder=build.__name__):
                    with self.assertRaises(ValueError):
                        build(4, 2, 2, givens)

    def test_contradictory_givens_in_rows_columns_and_boxes(self):
        for givens in (
            {(1, 1): 1, (1, 4): 1},
            {(1, 1): 1, (4, 1): 1},
            {(1, 1): 1, (2, 2): 1},
        ):
            for solve in (solver.solve_full_grid_fc, solver.solve_full_grid_bc):
                with self.subTest(givens=givens, solver=solve.__name__):
                    with self.assertRaises(ValueError):
                        solve(4, 2, 2, givens)

    def test_unresolved_puzzle_is_reported_without_guessing(self):
        for solve in (solver.solve_full_grid_fc, solver.solve_full_grid_bc):
            with self.subTest(solver=solve.__name__):
                with self.assertRaises(ValueError) as caught:
                    solve(4, 2, 2, {})
                self.assertEqual(caught.exception.partial_grid, {})
                self.assertEqual(len(caught.exception.unresolved_cells), 16)


if __name__ == "__main__":
    unittest.main()
