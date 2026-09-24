# Sudoku-IT5005

Sudoku-IT5005 is a logic-based Sudoku solver that explores knowledge representation
and inference in artificial intelligence. It expresses Sudoku constraints as
propositional logic and derives cell values from the puzzle's given numbers.

The project combines a Jupyter notebook for experiments and explanations with an
interactive Streamlit app for solving puzzles and inspecting deductions. Both
use the same implementation in `sudoku_solver.py`. The supplied solutions serve
only as reference answers for verification; they are not used to make deductions.

## Knowledge representation

The solver builds two knowledge bases from the same puzzle:

| Representation | Approach |
| :--- | :--- |
| **General CNF clauses** | Express the Sudoku constraints directly: every cell has exactly one value, values cannot repeat within a row, column or box, and the givens are fixed. This representation is used to investigate resolution and truth-table model checking. |
| **Definite clauses** | Express deductions as rules with one positive conclusion. A known value eliminates other candidates in its cell and the same value from other cells sharing its row, column or box. When all other candidates in a cell have been eliminated, the remaining value is inferred. |

For example, placing 3 in a row eliminates 3 from the other cells in that row.
If a cell later has eight of its nine values eliminated, the final candidate
can be proved. The definite rules support these deductions, but do not express
all Sudoku constraints in the same way as the general representation.

## Inference methods

- **Forward chaining** starts with known facts and applies rules to derive more
  facts. The full-grid solver uses the supplied `pl_fc_entails` implementation
  to collect deductions and reconstruct the board.
- **Backward chaining** starts with a candidate cell value and works backward
  through rules that could prove it. The custom implementation handles cycles
  and reuses established proofs across queries on the same knowledge base.

Both methods solve all five supplied 9×9 puzzles. Their elapsed solve times
include knowledge-base construction and inference.

## Interactive web app

The Streamlit interface lets users:

- Select one of the five puzzles and distinguish given, derived and unresolved cells.
- Choose forward or backward chaining, solve the board and view the elapsed time.
- Query a row, column and value using backward chaining to obtain a
  **True/False entailment result**.
- Read a short explanation and browse a recorded proof for a successful
  query, including eliminations and last-candidate deductions.

The reasoning trace comes from the rules used during inference. A False result
means the current rules cannot prove that candidate; it does not by itself
establish that the candidate is impossible.

## Experiments and scope

The notebook explains the representations and algorithms, checks both solvers
against all five reference solutions, and compares FC and BC on all 729
cell/value candidates in the first puzzle. Its timing experiment repeats each
method six times per puzzle and reports medians and ranges.

Resolution and truth-table model checking are demonstrated on a small 2×2
puzzle. Recorded attempts on a 9×9 puzzle illustrate why these general methods
can become impractical as the knowledge base grows.

The definite solver uses elimination and last-candidate rules without guessing.
Some valid puzzles require additional techniques; when these rules cannot finish
a grid, the app displays the values proved so far.

## Main files

| File | Purpose |
| :--- | :--- |
| [Sudoku_Assignment.ipynb](Sudoku_Assignment.ipynb) | Experiments, verification, timing results and conceptual answers. |
| [sudoku_solver.py](sudoku_solver.py) | Knowledge-base construction, inference and reasoning traces. |
| [sudoku_app.py](sudoku_app.py) | Interactive Streamlit interface. |
| [logic_.py](logic_.py), [utils.py](utils.py) | Unchanged libraries supplied with the assignment. |
| [puzzles.json](puzzles.json) | Five puzzles, their givens and reference solutions. |
| [requirements.txt](requirements.txt), [requirements-dev.txt](requirements-dev.txt) | Runtime and notebook development dependencies. |
