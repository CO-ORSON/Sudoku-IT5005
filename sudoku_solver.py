"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

# Implementation notes (completed solution):
# Sudoku knowledge representation and inference using the supplied libraries.
#
# The general KB describes all valid completions. The definite KB uses sound
# elimination and last-candidate rules; it never guesses, so some valid puzzles
# cannot be completed by these rules. Only utils and logic_ are imported.

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


class InconsistentPuzzleError(ValueError):
    """The givens or inferred assignments violate a Sudoku constraint."""


class UnresolvedPuzzleError(ValueError):
    """Horn inference stalled; partial_grid contains only proved assignments."""

    def __init__(self, partial_grid, unresolved_cells):
        self.partial_grid = dict(partial_grid)
        self.unresolved_cells = tuple(unresolved_cells)
        super().__init__(
            f'Elimination and last-candidate rules resolved {len(partial_grid)} '
            f'cells; {len(unresolved_cells)} remain. '
            'This does not establish that the puzzle is unsatisfiable.'
        )


def _units(n, box_h, box_w):
    """Yield every row, column and box in a deterministic order."""
    for r in range(1, n + 1):
        yield tuple((r, c) for c in range(1, n + 1))
    for c in range(1, n + 1):
        yield tuple((r, c) for r in range(1, n + 1))
    for top in range(1, n + 1, box_h):
        for left in range(1, n + 1, box_w):
            yield tuple((r, c) for r in range(top, top + box_h)
                        for c in range(left, left + box_w))


def _validate_input(n, box_h, box_w, givens):
    """Validate dimensions, 1-indexed coordinates and immediate conflicts."""
    if any(type(value) is not int or value < 1
           for value in (n, box_h, box_w)):
        raise ValueError('n, box_h and box_w must be positive integers.')
    if box_h * box_w != n:
        raise ValueError('box_h * box_w must equal n.')
    if not isinstance(givens, collections.abc.Mapping):
        raise ValueError('givens must map (row, column) tuples to values.')
    copied = {}
    for cell, value in givens.items():
        if (not isinstance(cell, tuple) or len(cell) != 2
                or any(type(x) is not int or not 1 <= x <= n for x in cell)
                or type(value) is not int or not 1 <= value <= n):
            raise ValueError('Given coordinates and values must be integers in 1..n.')
        copied[cell] = value
    for unit in _units(n, box_h, box_w):
        values = [copied[cell] for cell in unit if cell in copied]
        if len(values) != len(set(values)):
            raise InconsistentPuzzleError(
                'The givens repeat a value in a row, column, or box.'
            )
    return copied


def _peers(n, box_h, box_w):
    """Map cells to the other cells sharing a row, column or box."""
    result = {(r, c): set() for r in range(1, n + 1)
              for c in range(1, n + 1)}
    for unit in _units(n, box_h, box_w):
        for cell in unit:
            result[cell].update(other for other in unit if other != cell)
    return {cell: tuple(sorted(others)) for cell, others in result.items()}


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """

    # Implementation notes (completed solution):
    # Return a supplied PropKB containing Sudoku's complete CNF encoding.
    #
    # Each cell has an at-least-one disjunction and a binary negative clause
    # for every pair of different values. Each pair of peer cells has a binary
    # negative clause for every value. Givens are unit clauses. Overlapping
    # row/box and column/box constraints are deduplicated.
    #
    # ~Is_r_c_v is logical negation here; the separate positive Not_r_c_v
    # atoms are used only in the definite representation.

    # Original starter placeholder (implemented below):
    # raise NotImplementedError(
    #     'build_general_kb: encode the puzzle as general clauses'
    # )
    givens = _validate_input(n, box_h, box_w, givens)
    peers = _peers(n, box_h, box_w)
    symbols = {(r, c, v): atom('Is', r, c, v)
               for r, c in peers for v in range(1, n + 1)}
    kb = PropKB()
    for r, c in peers:
        kb.tell(associate('|', [symbols[r, c, v] for v in range(1, n + 1)]))
        for v, w in combinations(range(1, n + 1), 2):
            kb.tell(~symbols[r, c, v] | ~symbols[r, c, w])
        for other_r, other_c in peers[r, c]:
            if (r, c) < (other_r, other_c):
                for v in range(1, n + 1):
                    kb.tell(~symbols[r, c, v] | ~symbols[other_r, other_c, v])
    for (r, c), v in sorted(givens.items()):
        kb.tell(symbols[r, c, v])
    return kb


class _IndexedDefiniteKB(PropDefiniteKB):
    """The supplied KB with lookup indexes; its inference code is unchanged.

    The library notes that clauses_with_premise may be cached. This override
    implements that suggestion and optionally observes facts that the actual
    library forward-chaining loop visits. It infers no new facts itself.
    """

    def __init__(self):
        super().__init__()
        self._premise_index = defaultdict(list)
        self._conclusion_index = defaultdict(list)
        self._rule_premises = {}
        self._facts = set()
        self._revision = 0
        self._fc_observed = None

    def tell(self, sentence):
        super().tell(sentence)
        premises, conclusion = parse_definite_clause(sentence)
        if premises:
            self._rule_premises[sentence] = tuple(dict.fromkeys(premises))
            self._conclusion_index[conclusion].append(sentence)
            for premise in self._rule_premises[sentence]:
                self._premise_index[premise].append(sentence)
        else:
            self._facts.add(conclusion)
        self._revision += 1

    def retract(self, sentence):
        """Keep the indexes and cached proofs consistent after a mutation."""
        super().retract(sentence)
        remaining = tuple(self.clauses)
        self.clauses.clear()
        self._premise_index.clear()
        self._conclusion_index.clear()
        self._rule_premises.clear()
        self._facts.clear()
        self._revision += 1
        for clause in remaining:
            self.tell(clause)

    def clauses_with_premise(self, p):
        if self._fc_observed is not None:
            self._fc_observed.add(p)
        return self._premise_index.get(p, ())


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """

    # Implementation notes (completed solution):
    # Return a PropDefiniteKB using elimination plus naked singles.
    #
    # Is(r,c,v) ==> Not(r,c,w), w != v, expresses one value per cell.
    # Is(r,c,v) ==> Not(s,t,v), for each peer, expresses unit uniqueness.
    # AND(Not(r,c,w) for w != v) ==> Is(r,c,v) expresses the last candidate.
    # Every given supplies an Is fact. Not is an ordinary positive proposition,
    # not the logical negation operator.
    #
    # The last-candidate rule is a sound consequence of at-least-one; it cannot
    # assert a choice until exclusions are proved. This Horn encoding is thus
    # incomplete as a Sudoku strategy, although Horn inference on it is complete.

    # Original starter placeholder (implemented below):
    # raise NotImplementedError(
    #     'build_definite_kb: encode the puzzle as definite clauses'
    # )
    givens = _validate_input(n, box_h, box_w, givens)
    peers = _peers(n, box_h, box_w)
    positive = {(r, c, v): atom('Is', r, c, v)
                for r, c in peers for v in range(1, n + 1)}
    negative = {(r, c, v): atom('Not', r, c, v)
                for r, c in peers for v in range(1, n + 1)}
    kb = _IndexedDefiniteKB()
    kb._sudoku_dimensions = (n, box_h, box_w)
    kb._sudoku_givens = givens
    for r, c in peers:
        for v in range(1, n + 1):
            current = positive[r, c, v]
            for w in range(1, n + 1):
                if w != v:
                    kb.tell(Expr('==>', current, negative[r, c, w]))
            for other_r, other_c in peers[r, c]:
                kb.tell(Expr('==>', current, negative[other_r, other_c, v]))
            excluded = [negative[r, c, w] for w in range(1, n + 1) if w != v]
            # A 1 x 1 board has its only domain value even without givens.
            kb.tell(Expr('==>', associate('&', excluded), current)
                    if excluded else current)
    for (r, c), v in sorted(givens.items()):
        kb.tell(positive[r, c, v])
    return kb


def _grid_from_proven(n, box_h, box_w, givens, proven):
    """Check inferred consistency and return a full grid or a useful error."""
    grid, unresolved = {}, []
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            values = [v for v in range(1, n + 1) if atom('Is', r, c, v) in proven]
            if (len(values) > 1
                    or any(atom('Not', r, c, v) in proven for v in values)
                    or all(atom('Not', r, c, v) in proven for v in range(1, n + 1))):
                raise InconsistentPuzzleError(f'Contradictory deductions at row {r}, column {c}.')
            if values:
                grid[r, c] = values[0]
            else:
                unresolved.append((r, c))
    _validate_input(n, box_h, box_w, grid)
    if any(grid.get(cell) != value for cell, value in givens.items()):
        raise InconsistentPuzzleError('The inferred grid does not preserve every given.')
    if unresolved:
        raise UnresolvedPuzzleError(grid, unresolved)
    return grid


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """

    # Implementation notes (completed solution):
    # Solve using one complete pass of the supplied pl_fc_entails.
    #
    # An unreachable query makes the library exhaust its agenda. The indexed
    # KB records each proposition visited by that actual library execution,
    # allowing the full grid to share a single forward-chaining pass. No custom
    # forward inference or solution data is used.
    #
    # Raise InconsistentPuzzleError for a detected contradiction, or
    # UnresolvedPuzzleError if these rules cannot complete the puzzle.

    # Original starter placeholder (implemented below):
    # raise NotImplementedError(
    #     'solve_full_grid_fc: solve every cell with forward chaining'
    # )
    kb = build_definite_kb(n, box_h, box_w, givens)
    observed = set()
    kb._fc_observed = observed
    try:
        pl_fc_entails(kb, Expr('SudokuUnreachableQuery'))
    finally:
        kb._fc_observed = None
    return _grid_from_proven(n, box_h, box_w, givens, observed)


def _backward_cache(kb):
    """Index a supplied definite KB and invalidate proofs when it changes."""
    if not isinstance(kb, PropDefiniteKB):
        raise ValueError('Backward chaining requires a PropDefiniteKB.')
    # The subclass tracks tell/retract. For the plain supplied KB, a snapshot
    # also detects direct replacement of a same-length clause list.
    signature = kb._revision if isinstance(kb, _IndexedDefiniteKB) else tuple(kb.clauses)
    cached = getattr(kb, '_sudoku_bc_cache', None)
    if cached is not None and cached['signature'] == signature:
        return cached
    if isinstance(kb, _IndexedDefiniteKB):
        heads, bodies, facts = kb._conclusion_index, kb._rule_premises, kb._facts
    else:
        heads, bodies, facts = defaultdict(list), {}, set()
        for clause in kb.clauses:
            if not is_definite_clause(clause):
                raise ValueError('The KB contains a non-definite clause.')
            premises, conclusion = parse_definite_clause(clause)
            if premises:
                heads[conclusion].append(clause)
                bodies[clause] = tuple(dict.fromkeys(premises))
            else:
                facts.add(conclusion)
    cached = {
        'signature': signature, 'heads': heads, 'bodies': bodies,
        'proofs': {fact: (None, ()) for fact in facts}, 'false_queries': set(),
    }
    kb._sudoku_bc_cache = cached
    return cached


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """

    # Implementation notes (completed solution):
    # Prove an atomic goal by sound, terminating tabled backward chaining.
    #
    # Start with rules concluding the goal and recursively demand their premises.
    # Explicit generator frames implement recursion without Python's stack limit.
    # An already active goal suspends its rule instead of becoming a permanent
    # failure. Whenever a premise is proved, waiting rules resume; a rule proves
    # its conclusion only when ALL premises have proofs. Alternative rules are
    # OR choices. This dependency bookkeeping handles cycles with grounding facts
    # and cannot invent proofs for unfounded cycles.
    #
    # Each goal is expanded at most once per query. A failed goal is cached only
    # after the entire query traversal has finished, never merely because a
    # recursive branch revisits it. Grounded proofs are reused on the same KB.

    # Original starter placeholder (implemented below):
    # raise NotImplementedError(
    #     'pl_bc_entails: implement backward chaining, soundly'
    # )
    if not isinstance(query, Expr) or query.args or not is_prop_symbol(query.op):
        raise ValueError('query must be an atomic propositional Expr.')
    cache = _backward_cache(kb)
    proofs = cache['proofs']
    if query in proofs:
        return True
    if query in cache['false_queries']:
        return False
    expanded, remaining, waiting = set(), {}, defaultdict(list)

    def establish(goal, rule):
        """Record an actual proof and awaken rules waiting on its conclusion."""
        agenda = [(goal, rule)]
        while agenda:
            conclusion, witness = agenda.pop()
            if conclusion in proofs:
                continue
            proofs[conclusion] = (witness, cache['bodies'][witness])
            for dependent in waiting.pop(conclusion, ()):
                missing = remaining[dependent]
                missing.discard(conclusion)
                if not missing and dependent.args[1] not in proofs:
                    agenda.append((dependent.args[1], dependent))

    def demand(goal):
        """One recursive goal frame; yielded premises create child frames."""
        expanded.add(goal)
        for rule in cache['heads'].get(goal, ()):
            if goal in proofs:
                return
            body = cache['bodies'][rule]
            missing = {premise for premise in body if premise not in proofs}
            remaining[rule] = missing
            if not missing:
                establish(goal, rule)
                return
            for premise in missing:
                waiting[premise].append(rule)
            # Explore all premises: a later one can ground an earlier cycle.
            for premise in body:
                if (premise not in proofs and premise not in expanded
                        and premise not in cache['false_queries']):
                    yield premise
                if goal in proofs:
                    return

    frames = [demand(query)]
    while frames:
        try:
            premise = next(frames[-1])
        except StopIteration:
            frames.pop()
            continue
        if premise not in proofs and premise not in expanded:
            frames.append(demand(premise))
    # At this point every unproved expanded goal has exhausted all its rules;
    # all their dependencies were expanded, proved or previously exhausted.
    # Only now is it sound to memoize these failures across later queries.
    cache['false_queries'].update(expanded.difference(proofs))
    return query in proofs


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """

    # Implementation notes (completed solution):
    # Try cell candidates with pl_bc_entails until one is proved per cell.
    #
    # Reuse one KB and its grounded proof cache, but start a backward query for
    # each tested candidate. Neither forward chaining nor solution data is used.

    # Original starter placeholder (implemented below):
    # raise NotImplementedError(
    #     'solve_full_grid_bc: solve every cell with backward chaining'
    # )
    kb = build_definite_kb(n, box_h, box_w, givens)
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                if pl_bc_entails(kb, atom('Is', r, c, v)):
                    break
    return _grid_from_proven(n, box_h, box_w, givens, _backward_cache(kb)['proofs'])


def _describe_proof(kb, conclusion, premises):
    """Translate a proved Sudoku rule into its human-readable meaning."""
    def unpack(symbol):
        prefix = 'Not' if symbol.op.startswith('Not') else 'Is'
        values = tuple(int(value) for value in symbol.op[len(prefix):].split('_'))
        if len(values) != 3:
            raise ValueError('Not a Sudoku symbol')
        return prefix, values

    try:
        prefix, (r, c, v) = unpack(conclusion)
        if not premises:
            if getattr(kb, '_sudoku_givens', {}).get((r, c)) == v:
                return 'given', f'Row {r}, column {c} is given as {v}.'
            if getattr(kb, '_sudoku_dimensions', (0,))[0] == 1:
                return 'last_candidate', 'The only cell must contain 1, its only possible value.'
            return 'given', f'{conclusion} is a fact in the knowledge base.'
        if prefix == 'Is':
            excluded = sorted(unpack(premise)[1][2] for premise in premises)
            options = ', '.join(str(value) for value in excluded)
            return 'last_candidate', (
                f'Row {r}, column {c} must be {v}: every other value '
                f'({options}) has been eliminated.'
            )
        _, (source_r, source_c, source_v) = unpack(premises[0])
        if (source_r, source_c) == (r, c):
            reason = f'this cell already contains {source_v}'
        elif source_r == r:
            reason = f'row {r} already contains {v} in column {source_c}'
        elif source_c == c:
            reason = f'column {c} already contains {v} in row {source_r}'
        else:
            reason = f'its box already contains {v} at row {source_r}, column {source_c}'
        return 'elimination', f'Eliminate {v} from row {r}, column {c}: {reason}.'
    except (ValueError, AttributeError):
        return 'rule', f'{conclusion} follows from ' + ', '.join(map(str, premises)) + '.'


def explain_query(kb, query):
    """Return (verdict, steps) for the actual backward-chaining proof.

    Successful steps are in dependency order and contain conclusion, premises,
    rule, kind and explanation. Witnesses are captured when deductions occur
    inside pl_bc_entails, never inferred from a completed grid. False means
    not derivable, not necessarily logically impossible.
    """
    verdict = pl_bc_entails(kb, query)
    if not verdict:
        return False, [{
            'conclusion': query, 'premises': (), 'rule': None, 'kind': 'unresolved',
            'explanation': 'This candidate is not derivable from the givens using '
                           'elimination and last-candidate rules.',
        }]
    proofs = _backward_cache(kb)['proofs']
    steps, visited, stack = [], set(), [(query, False)]
    while stack:
        goal, ready = stack.pop()
        if goal in visited:
            continue
        rule, premises = proofs[goal]
        if not ready:
            stack.append((goal, True))
            stack.extend((premise, False) for premise in reversed(premises))
            continue
        visited.add(goal)
        kind, explanation = _describe_proof(kb, goal, premises)
        steps.append({'conclusion': goal, 'premises': premises, 'rule': rule,
                      'kind': kind, 'explanation': explanation})
    return True, steps
