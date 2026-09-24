"""Package only the assignment's three deliverables after readiness checks."""

import argparse
import json
from pathlib import Path
import re
import sys
from zipfile import ZipFile, ZIP_DEFLATED

ROOT = Path(__file__).resolve().parents[1]
FILES = ('Sudoku_Assignment.ipynb', 'sudoku_solver.py', 'sudoku_app.py')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--draft', action='store_true',
                        help='Allow identity/deployment placeholders in a clearly marked draft ZIP.')
    args = parser.parse_args()
    for name in FILES:
        if not (ROOT / name).is_file():
            parser.error(f'Missing required deliverable: {name}')
    notebook = json.loads((ROOT / FILES[0]).read_text(encoding='utf-8'))
    markdown = '\n'.join(''.join(cell['source']) for cell in notebook['cells']
                         if cell['cell_type'] == 'markdown')
    code_cells = [cell for cell in notebook['cells'] if cell['cell_type'] == 'code'
                  and ''.join(cell['source']).strip()]
    if any(cell.get('execution_count') is None for cell in code_cells):
        parser.error('Execute every code cell and save the notebook first.')
    if any(output.get('output_type') == 'error' for cell in code_cells
           for output in cell.get('outputs', [])):
        parser.error('The notebook contains an error output; fix it and rerun all cells.')
    incomplete = bool(re.search(r'\[Student (?:name|ID)|\[Describe member', markdown))
    incomplete |= not bool(re.search(r'https://[a-zA-Z0-9][a-zA-Z0-9-]*\.streamlit\.app\b', markdown))
    if incomplete and not args.draft:
        parser.error('Fill all member placeholders and the deployed Streamlit URL, or use --draft for review.')
    output_dir = ROOT / 'submission'
    output_dir.mkdir(exist_ok=True)
    archive = output_dir / ('Group_26_DRAFT.zip' if args.draft else 'Group_26.zip')
    with ZipFile(archive, 'w', ZIP_DEFLATED) as zip_file:
        for name in FILES:
            zip_file.write(ROOT / name, f'Group_26/{name}')
    print(f'Created {archive}')
    if args.draft:
        print('DRAFT: complete identity, contribution and deployment fields before submission.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
