"""Verify packet integrity and recorded evidence. Does not run Lean."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MODULES = ['Sampling', 'Words', 'Occupancy', 'TailFormula', 'Pairing',
           'MatroidDual', 'Result', 'Audit', 'CodeLinear', 'CodeGenerator',
           'CodeResult', 'CodeProbability', 'CodeAudit']
THEOREMS = {'mem_codeDual', 'codeRecovers_iff_agreement',
            'codeRecovers_iff_decoder', 'generatedCode_recovers_iff_span',
            'code_complementary_recovery', 'codeExpectedReads_hasSum',
            'codeExpectedReads_dual', 'codeRecoveryBalanced_dual_iff',
            'self_dual_codeExpectedReads', 'code_word_failure_probability',
            'codeExpectedReads_eq_count_series'}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(name):
    return json.loads((ROOT / name).read_text(encoding='utf-8'))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check():
    manifest = read('packet-manifest.json')
    paths = manifest['files']
    for name, expected in paths.items():
        require(not Path(name).is_absolute() and '..' not in Path(name).parts,
                'Invalid manifest path: ' + name)
        path = ROOT / name
        require(path.is_file() and not path.is_symlink(), 'Missing file: ' + name)
        require(digest(path) == expected, 'Packet file hash mismatch: ' + name)

    report = read('verification-code-azure.json')
    build = read('evidence/build.json')
    negative = read('evidence/negative-control.json')
    require(report['pins'] == {
        'lean': '4.34.0',
        'mathlib': '5ed2965256430c3649e86755f9576b54eca72435'}, 'Wrong pins')
    require(build['status'] == 'PASS', 'Recorded build did not pass')
    require([r['module'] for r in build['records']] == MODULES,
            'Recorded module list is incomplete')
    require(all(r['exit_code'] == 0 for r in build['records']),
            'A recorded positive module failed')
    require(report['build_request'] == build['seq'], 'Build request differs')
    require(report['source_sha256'] == build['source_sha256'],
            'Source hashes differ between report and build')
    require(set(build['source_sha256']) ==
            {m + '.lean' for m in MODULES} |
            {'NegativeControl.lean', 'CodeNegativeControl.lean'},
            'Unexpected source list')
    for name, expected in build['source_sha256'].items():
        require(digest(ROOT / 'lean' / name) == expected,
                'Source differs from recorded build: ' + name)

    require(negative['source_sha256'] == build['source_sha256'],
            'Negative control used different sources')
    require(negative['status'] == 'FAIL' and len(negative['records']) == 1,
            'Negative control was not rejected')
    neg = negative['records'][0]
    require(neg['module'] == 'CodeNegativeControl' and neg['exit_code'] == 1
            and all(x in neg['log'] for x in ('Type mismatch', 'True.intro', 'False')),
            'Negative control failed for an unexpected reason')

    audit = build['records'][-1]['log']
    require((ROOT / 'evidence/axioms.txt').read_text(encoding='utf-8') == audit,
            'Axiom text differs from the recorded build')
    axioms = dict(re.findall(r"'DNA\.([^']+)' depends on axioms: \[([^]]*)\]", audit))
    require(set(axioms) == THEOREMS, 'Incomplete code axiom audit')
    for name, values in axioms.items():
        dependencies = set(filter(None, values.split(', ')))
        require(dependencies <= ALLOWED, 'Unexpected axioms in ' + name)
        require(dependencies == set(report['axioms_by_theorem'][name]),
                'Axiom report differs for ' + name)
    require(report['azure']['worker_exit_code'] == 0, 'Worker did not finish')
    require(report['azure']['results_downloaded'], 'Results were not retrieved')
    require(report['azure']['cleanup']['all_deleted'], 'Cleanup not confirmed')
    print('PASS: packet hashes, 15 original Lean sources, 13 successful module records,')
    print('11 code axiom audits, expected negative-control failure and recorded cleanup.')
    print('This checks recorded evidence; it does not re-run Lean or prove the theorem.')


if __name__ == '__main__':
    try:
        check()
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit('FAIL: ' + str(error))
