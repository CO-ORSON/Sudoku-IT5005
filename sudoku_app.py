"""Interactive IT5005 Sudoku solver and proof tutor.

Launch from PyCharm with ``python -m streamlit run sudoku_app.py``.
Only interface concerns live here: all inference is in sudoku_solver.py.

Original lecturer setup (reference only; completed implementation below):
import json
import time
import streamlit as st
from utils import *
from logic_ import *
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails,
)

st.title('Sudoku Solver')

with open('puzzles.json') as f:
    pool = json.load(f)
"""

from html import escape
import json
from pathlib import Path
import re
import time

import streamlit as st

# All six required assignment functions remain available. General-KB examples
# are in the notebook; the interactive chaining tools use the definite KB.
# The TODO comments below retain the lecturer's original instructions; all are implemented.
# Keep the core solver functions in sudoku_solver.py; do not duplicate them here.
from sudoku_solver import (
    atom, build_definite_kb, build_general_kb, solve_full_grid_fc,
    solve_full_grid_bc, pl_bc_entails, explain_query,
    InconsistentPuzzleError, UnresolvedPuzzleError,
)

PUZZLES_PATH = Path(__file__).resolve().with_name("puzzles.json")
ALGORITHMS = {"Forward chaining": solve_full_grid_fc,
              "Backward chaining": solve_full_grid_bc}
BOARD_CSS = """
<style>
.sudoku-wrap { max-width: 570px; overflow-x: auto; margin: .3rem 0 1rem; }
.sudoku-board { width: 100%; border-collapse: collapse; table-layout: fixed;
    background: #fff; color: #172b4d; font-variant-numeric: tabular-nums; }
.sudoku-board caption { text-align: left; color: #475569; padding: 0 0 .5rem;
    font-size: .85rem; }
.sudoku-board th { padding: .25rem; background: #fff; color: #475569;
    border: 0; text-align: center; font-size: .8rem; font-weight: 500; }
.sudoku-board td { height: clamp(2rem, 4.8vw, 3.35rem); padding: 0;
    border: 1px solid #ccd5df; text-align: center;
    font-size: clamp(1rem, 2.4vw, 1.4rem); }
.sudoku-board td.given { background: #edf1f6; color: #172b4d; font-weight: 750; }
.sudoku-board td.derived { background: #fff; color: #075e8f; font-weight: 400; }
.sudoku-board td.empty { background: #fff; }
.sudoku-board td.box-top { border-top: 3px solid #62748a; }
.sudoku-board td.box-left { border-left: 3px solid #62748a; }
.sudoku-board td.box-right { border-right: 3px solid #62748a; }
.sudoku-board td.box-bottom { border-bottom: 3px solid #62748a; }
.sudoku-board td.query-cell { box-shadow: inset 0 0 0 3px #d97706; }
.sudoku-eyebrow { letter-spacing: .12em; text-transform: uppercase;
    font-size: .75rem; font-weight: 700; color: #64748b; }
</style>
"""


@st.cache_data(show_spinner=False)
def load_puzzles(path_string, modified_ns):
    """Cache dimensions and givens, discarding the JSON answer-key fields.

    The timestamp invalidates cached data when the local file changes.
    Expected solutions are never returned or used by the interface.
    """
    del modified_ns  # It participates in Streamlit's cache key.
    with Path(path_string).open(encoding="utf-8") as handle:
        data = json.load(handle)
    n, box_h, box_w = (data[key] for key in ("n", "box_h", "box_w"))
    if any(type(x) is not int or x < 1 for x in (n, box_h, box_w)):
        raise ValueError("Grid and box dimensions must be positive integers.")
    if box_h * box_w != n or n % box_h or n % box_w:
        raise ValueError("The box dimensions do not fit the grid.")
    puzzles = []
    for puzzle in data["puzzles"]:
        givens = {}
        for cell, value in puzzle["givens"].items():
            r, c = map(int, cell.split("_"))
            if not (1 <= r <= n and 1 <= c <= n):
                raise ValueError(f"Given cell {cell!r} is outside the grid.")
            if type(value) is not int or not 1 <= value <= n:
                raise ValueError(f"Given cell {cell!r} has an invalid value.")
            if (r, c) in givens:
                raise ValueError(f"Given cell {cell!r} is repeated.")
            givens[r, c] = value
        puzzles.append(givens)
    if not puzzles:
        raise ValueError("puzzles.json does not contain any puzzles.")
    return n, box_h, box_w, puzzles


def board_html(n, box_h, box_w, givens, grid, highlighted=None):
    """Create a board with box boundaries, headers and accessible cell labels."""
    parts = ['<div class="sudoku-wrap"><table class="sudoku-board">',
             '<caption>Columns run across; rows run down.</caption>',
             '<thead><tr><th scope="col" aria-label="Row / column"></th>']
    parts.extend(f'<th scope="col">{c}</th>' for c in range(1, n + 1))
    parts.append("</tr></thead><tbody>")
    for r in range(1, n + 1):
        parts.append(f'<tr><th scope="row">{r}</th>')
        for c in range(1, n + 1):
            value = grid.get((r, c))
            kind = "given" if (r, c) in givens else "derived" if value else "empty"
            classes = [kind]
            for boundary, condition in (
                ("top", (r - 1) % box_h == 0), ("left", (c - 1) % box_w == 0),
                ("bottom", r == n), ("right", c == n),
            ):
                if condition:
                    classes.append(f"box-{boundary}")
            if (r, c) == highlighted:
                classes.append("query-cell")
            label = f"Row {r}, column {c}: {value}, {kind}" if value else (
                f"Row {r}, column {c}: empty")
            parts.append(
                f'<td class="{" ".join(classes)}" aria-label="{escape(label)}" '
                f'title="{escape(label)}">{escape(str(value)) if value else ""}</td>')
        parts.append("</tr>")
    parts.append("</tbody></table></div>")
    return "".join(parts)


def describe_atom(proposition):
    """Translate assignment Is/Not symbols into readable cell statements."""
    match = re.fullmatch(r"(Is|Not)(\d+)_(\d+)_(\d+)", str(proposition))
    if match is None:
        return str(proposition)
    prefix, r, c, value = match.groups()
    relation = "is" if prefix == "Is" else "cannot be"
    return f"Row {r}, column {c} {relation} {value}"


def show_trace(steps):
    """Page the complete proof without dropping premises or hiding any rules."""
    page_size = 12
    page_count = max(1, (len(steps) + page_size - 1) // page_size)
    page = int(st.number_input("Proof page", min_value=1, max_value=page_count,
                              step=1, key="sudoku_trace_page")) if page_count > 1 else 1
    start = (page - 1) * page_size
    st.caption(f"Steps {start + 1}–{min(start + page_size, len(steps))} of {len(steps)}. "
               "Premises appear before the conclusions they support.")
    labels = {"given": "Given fact", "elimination": "Eliminate a candidate",
              "last_candidate": "Last remaining candidate", "rule": "Apply a rule",
              "unresolved": "No proof found"}
    for number, step in enumerate(steps[start:start + page_size], start + 1):
        title = labels.get(step["kind"], "Apply a rule")
        conclusion = describe_atom(step["conclusion"])
        with st.expander(f"{number}. {title} · {conclusion}"):
            st.write(step["explanation"])
            if step["premises"]:
                st.markdown("**Established premises**")
                for premise in step["premises"]:
                    st.markdown(f"- {describe_atom(premise)}.")
            if step["rule"] is not None:
                st.markdown("**Rule that fired**")
                st.code(str(step["rule"]), language="text")
                st.markdown(f"**Conclusion:** {conclusion}.")
            elif step["kind"] == "given":
                st.caption("This fact comes directly from the puzzle's givens.")
                st.code(str(step["conclusion"]), language="text")


def main():
    """Run puzzle selection, full solving, targeted queries and the proof tutor."""
    st.set_page_config(page_title="Sudoku Logic Lab", page_icon="🧩", layout="wide")
    st.markdown(BOARD_CSS, unsafe_allow_html=True)
    st.markdown('<div class="sudoku-eyebrow">IT5005 · Logic in action</div>',
                unsafe_allow_html=True)
    st.title("Sudoku Logic Lab")
    st.write("Solve a puzzle with propositional logic, then follow the proof behind a cell.")
    try:
        n, box_h, box_w, puzzles = load_puzzles(
            str(PUZZLES_PATH), PUZZLES_PATH.stat().st_mtime_ns)
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        st.error(f"Unable to load puzzles.json: {error}")
        st.info("Keep the supplied puzzles.json in the same folder as sudoku_app.py.")
        st.stop()

    # --- 1. Puzzle selection & visual board display ---
    # TODO: a dropdown/selectbox to pick a puzzle by index from pool['puzzles'].
    # TODO: render the grid (e.g. a table or grid of st.columns), showing given
    # cells and empty cells differently (e.g. bold givens, blank otherwise).
    selected = st.selectbox("Choose a puzzle", range(len(puzzles)),
                            format_func=lambda i: f"Puzzle {i + 1} · {len(puzzles[i])} givens",
                            key="sudoku_puzzle")
    givens = puzzles[selected]
    signature = (selected, n, box_h, box_w, tuple(sorted(givens.items())))
    if st.session_state.get("sudoku_signature") != signature:
        # Never carry another puzzle's board or answer into a new selection.
        st.session_state.update(sudoku_signature=signature, sudoku_solve_result=None,
                                sudoku_query_result=None, sudoku_trace_page=1)
        r, c = next(((r, c) for r in range(1, n + 1) for c in range(1, n + 1)
                     if (r, c) not in givens), (1, 1))
        st.session_state.update(sudoku_row=r, sudoku_column=c, sudoku_value=1)

    board_column, action_column = st.columns([1.12, 1], gap="large")
    with board_column:
        st.subheader(f"Puzzle {selected + 1}")
        board_slot = st.empty()
        st.caption("**Bold, shaded = given** · Blue = derived · Blank = unresolved")
        board_status = st.empty()
    with action_column:
        # --- 2. Full-grid auto-solver, with algorithm selection ---
        # TODO: a radio/selectbox letting the user choose forward chaining
        # (solve_full_grid_fc) or backward chaining (solve_full_grid_bc).
        # TODO: a button that times and calls the chosen solver on
        # (n, box_h, box_w, givens), then displays the solved grid and the elapsed
        # time.
        st.subheader("Solve the whole grid")
        algorithm = st.radio("Reasoning method", list(ALGORITHMS), horizontal=True)
        st.caption("Forward chaining propagates known facts. Backward chaining works "
                   "backward from a candidate to the premises needed to prove it.")
        if st.button("Solve puzzle", type="primary", key="sudoku_solve"):
            started = time.perf_counter()
            with st.spinner(f"Solving with {algorithm.lower()}…"):
                try:
                    grid = ALGORITHMS[algorithm](n, box_h, box_w, dict(givens))
                    result = {"grid": grid, "status": "solved", "message": ""}
                except UnresolvedPuzzleError as error:
                    result = {"grid": error.partial_grid, "status": "partial", "message": str(error)}
                except (InconsistentPuzzleError, ValueError) as error:
                    result = {"grid": dict(givens), "status": "error", "message": str(error)}
            result.update(algorithm=algorithm, elapsed=time.perf_counter() - started)
            st.session_state["sudoku_solve_result"] = result
        result = st.session_state["sudoku_solve_result"]
        if result:
            if result["status"] == "solved":
                st.success(f"All {n * n} cells solved with {result['algorithm'].lower()}.")
            elif result["status"] == "partial":
                st.warning("The rules reached a fixed point with unresolved cells. "
                           "The board shows the values proved so far.")
                st.caption(result["message"])
            else:
                st.error(f"The puzzle could not be solved: {result['message']}")
            st.metric("Elapsed solve time", f"{result['elapsed']:.3f} s")
            st.caption("Includes knowledge-base construction and inference for this run.")
        st.divider()
        # --- 3. Targeted cell entailment query ---
        # TODO: number inputs for row (r), column (c), value (v).
        # TODO: a button that builds the definite KB, calls
        # pl_bc_entails(kb, atom('Is', r, c, v)), and displays True/False.
        st.subheader("Ask about a cell")
        st.write("Can the rules prove that this cell has this value?")
        with st.form("sudoku_query_form"):
            columns = st.columns(3)
            with columns[0]:
                r = int(st.number_input("Row", 1, n, step=1, key="sudoku_row"))
            with columns[1]:
                c = int(st.number_input("Column", 1, n, step=1, key="sudoku_column"))
            with columns[2]:
                value = int(st.number_input("Value", 1, n, step=1, key="sudoku_value"))
            submitted = st.form_submit_button("Check entailment", type="primary")
        if submitted:
            started = time.perf_counter()
            with st.spinner("Checking the candidate and recording its proof…"):
                try:
                    # Always reason from original givens, even after a full solve.
                    kb = build_definite_kb(n, box_h, box_w, dict(givens))
                    query = atom("Is", r, c, value)
                    entailed = pl_bc_entails(kb, query)
                    traced_result, steps = explain_query(kb, query)
                    if entailed != traced_result:
                        raise ValueError("The trace disagrees with the entailment result.")
                    query_result = {"cell": (r, c), "value": value, "entailed": entailed,
                                    "steps": steps, "error": None}
                except (InconsistentPuzzleError, ValueError) as error:
                    query_result = {"cell": (r, c), "value": value, "error": str(error)}
            query_result["elapsed"] = time.perf_counter() - started
            st.session_state.update(sudoku_query_result=query_result, sudoku_trace_page=1)

    result = st.session_state["sudoku_solve_result"]
    query_result = st.session_state["sudoku_query_result"]
    grid = result["grid"] if result else givens
    highlighted = query_result["cell"] if query_result else None
    board_slot.markdown(board_html(n, box_h, box_w, givens, grid, highlighted),
                        unsafe_allow_html=True)
    board_status.caption(f"{len(givens)} given · {len(grid) - len(givens)} derived · "
                         f"{n * n - len(grid)} unresolved"
                         + (" · Amber outline = last queried cell" if highlighted else ""))
    st.divider()
    # --- 4. Reasoning trace ("tutor mode") ---
    # TODO: instrument your forward- or backward-chaining approach to record each
    # reasoning step (which rule fired, on what premises, producing what
    # conclusion) as it answers the query above.
    # TODO: render that trace as human-readable output -- e.g. a sequence of
    # st.expander(...) blocks, one per step, each with a plain-English sentence
    # -- not a raw list/dict dump.
    #
    st.subheader("Tutor mode")
    if not query_result:
        st.info("Use Check entailment to see a True/False answer and inspect its reasoning.")
    else:
        r, c = query_result["cell"]
        value = query_result["value"]
        st.markdown(f"**Last query:** row {r}, column {c}, value {value}")
        if query_result["error"]:
            st.error(f"The query could not be evaluated: {query_result['error']}")
        else:
            if query_result["entailed"]:
                st.success(f"True — the definite knowledge base proves this cell is {value}.")
            else:
                st.warning("False — this candidate is not derivable from the definite knowledge base.")
                st.caption("False means no proof was found using these rules. It does not, by itself, "
                           "prove the candidate is impossible or that the puzzle has no solution.")
            # The final recorded step explains the target, including given and unproved queries.
            st.markdown("**Why this result?**")
            st.write(query_result["steps"][-1]["explanation"])
            st.caption(f"Query and trace completed in {query_result['elapsed']:.3f} s.")
            if st.checkbox("Show reasoning trace", value=True):
                show_trace(query_result["steps"])


if __name__ == "__main__":
    main()
