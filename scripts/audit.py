#!/usr/bin/env python3
"""Audit build pins, source mechanisms, and printed axiom dependencies.

This checks what the build used and what the theorems depend on; it does not check
mathematical truth.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
# native_decide in Lean 4.28 contributes exactly these two axioms.
NATIVE = STANDARD | {'Lean.ofReduceBool', 'Lean.trustCompiler'}
TARGETS = {
    'Gyires.gyires_4x4': NATIVE,
    'Gyires.permanent_gram_le': NATIVE,
    'Gyires.permanent_gram_add_ge': STANDARD,
    'Gyires.permanent_gram_lt': NATIVE,
    'Gyires.gyires_4x4_strict': NATIVE,
    'Gyires.gyires_4x4_eq_iff': NATIVE,
    'Gyires.gyires_4x4_ratio': NATIVE,
    'Gyires.gyires_4x4_ratio_eq_iff': NATIVE,
    'GyiresVerification.inequality': NATIVE,
    'GyiresVerification.equality_iff': NATIVE,
    'GyiresVerification.ratio': NATIVE,
    'GyiresVerification.denominator_pos': STANDARD,
    'GyiresVerification.ratio_equality_iff': NATIVE,
    'GyiresVerification.stronger': NATIVE,
    'GyiresVerification.gram_comparison': STANDARD,
}
LEAN_DIRS = ('RequestProject', 'GyiresCompute', 'GyiresStrictCompute', 'GyiresEquality')
LEAN_FILE_COUNT = 43
# Every native_decide use, by file. All other files must have none.
NATIVE_DECIDE = {
    'RequestProject/HEval.lean': 4,          # monomial multiplication tables
    'RequestProject/Cert/Assemble.lean': 5,  # symmetry fact and the four top-level splits
    'GyiresEquality/StrictSound.lean': 1,    # positions of the pure powers
    **{f'RequestProject/Cert/C_{p}.lean': 1 for p in (
        '65532_65516', '65532_65500', '65532_65468', '65518_65516', '65518_65486',
        '65518_65006', '65502_65500', '65502_65498', '65502_65486', '65502_65438',
        '65502_65246', '65502_64990', '65502_64478')},
    **{f'GyiresEquality/Cert/S_{p}.lean': 1 for p in (
        '65532_65516', '65532_65500', '65532_65468', '65518_65516', '65518_65486',
        '65518_65006', '65502_65500', '65502_65498', '65502_65486', '65502_65438',
        '65502_65246', '65502_64990', '65502_64478')},
}
FORBIDDEN = re.compile(r'\b(sorry|sorryAx|admit|axiom|unsafe|implemented_by|extern|csimp|'
                       r'opaque|skipKernelTC|debug|notation|infix|infixl|infixr|prefix|'
                       r'postfix|macro|macro_rules|syntax|elab|elab_rules|instance|'
                       r'attribute|export)\b|@\[')


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def manifest_hashes():
    entries = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed source digest')
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT), 'Source path escapes project')
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == digest, 'Source digest mismatch: ' + name)
        require(name not in entries, 'Duplicate source digest: ' + name)
        entries[name] = actual
    return entries


def axiom_reports(transcript):
    require(not re.search(r'\b(?:warning|error):', transcript),
            'Compiler warning or error in the restatement check')
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", transcript)
    found = {}
    for name, axioms in records:
        require(name in TARGETS, 'Unexpected axiom report: ' + name)
        require(name not in found, 'Duplicate axiom report: ' + name)
        deps = {a.strip() for a in axioms.split(',') if a.strip()}
        require(deps == TARGETS[name], 'Unexpected axiom dependencies: ' + name)
        found[name] = sorted(deps)
    require(set(found) == set(TARGETS), 'Missing axiom reports')
    return found


def lean_sources():
    paths = [ROOT / 'Verification.lean', ROOT / 'scripts/PrintAxioms.lean']
    for d in LEAN_DIRS:
        paths += (ROOT / d).rglob('*.lean')
    return sorted(paths)


mode = sys.argv[1]
if mode == 'pins':
    pin = json.loads((ROOT / 'TOOLCHAIN.json').read_text())
    require((ROOT / 'lean-toolchain').read_text().strip() ==
            'leanprover/lean4:v' + pin['lean_version'], 'Toolchain file')
    require(output('lean', '--short-version') == pin['lean_version'], 'Lean version')
    require(output('lean', '--githash') == pin['lean_commit'], 'Lean commit')
    require(output('lake', '--version').startswith('Lake version ' + pin['lake_version']),
            'Lake version')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    require(mathlib['rev'] == pin['mathlib_commit'], 'mathlib revision')
    require(mathlib['inputRev'] == pin['mathlib_tag'], 'mathlib tag')
    for package in manifest['packages']:
        require(package['type'] == 'git' and
                re.fullmatch(r'[0-9a-f]{40}', package['rev']),
                'Unpinned dependency: ' + package['name'])
        require(output('git', '-C', '.lake/packages/' + package['name'],
                       'rev-parse', 'HEAD') == package['rev'],
                'Dependency checkout: ' + package['name'])
    print('PASS: Lean, Lake, toolchain file, mathlib, and every locked dependency agree.')
elif mode == 'sources':
    paths = lean_sources()
    require(len(paths) == LEAN_FILE_COUNT, f'Expected {LEAN_FILE_COUNT} Lean files')
    total = 0
    for path in paths:
        name = path.relative_to(ROOT).as_posix()
        text = path.read_text()
        match = FORBIDDEN.search(text)
        require(match is None, f'Forbidden mechanism {match and match.group(0)!r} in {name}')
        count = len(re.findall(r'\bnative_decide\b', text))
        require(count == NATIVE_DECIDE.get(name, 0), 'Unexpected native_decide use in ' + name)
        total += count
    require(total == sum(NATIVE_DECIDE.values()), 'native_decide inventory')
    print(f'PASS: {len(paths)} Lean files; no sorry, admit, axiom declarations, unsafe code, '
          f'implemented_by, extern, csimp, kernel-check options, attributes, instances, '
          f'notation, or macros; native_decide appears exactly {total} times, all in the '
          f'expected certificate files.')
elif mode == 'axioms':
    transcript = Path(sys.argv[2]).read_text()
    found = axiom_reports(transcript)
    for name in sorted(found):
        print('PASS:', name, 'uses exactly', ', '.join(found[name]))
    print('PASS: no sorryAx or project-specific axiom in any audited theorem.')
elif mode == 'hashes':
    for name, digest in manifest_hashes().items():
        print(digest, name)
elif mode == 'record':
    exit_code = int(sys.argv[2])
    commit = None
    try:
        git_root = Path(subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel'], cwd=ROOT, text=True,
            stderr=subprocess.DEVNULL).strip()).resolve()
        if git_root == ROOT:
            commit = output('git', 'rev-parse', 'HEAD')
    except subprocess.CalledProcessError:
        pass
    dirty = output('git', 'status', '--porcelain', '--untracked-files=no') != '' if commit else None
    repository = os.environ.get('GITHUB_REPOSITORY')
    run_id = os.environ.get('GITHUB_RUN_ID')
    run_url = f'https://github.com/{repository}/actions/runs/{run_id}' if repository and run_id else None
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        require(commit == os.environ.get('GITHUB_SHA'), 'Commit differs from workflow SHA')
        require(dirty is False, 'Tracked sources changed during verification')
    actual_axioms = axiom_reports((ROOT / '.build/kernel-check.log').read_text()) if exit_code == 0 else None
    data = {
        'verification_exit_code': exit_code,
        'status': 'PASS' if exit_code == 0 else 'FAIL',
        'started_utc': sys.argv[3],
        'finished_utc': sys.argv[4],
        'repository_commit_at_run': commit,
        'tracked_worktree_dirty': dirty,
        'github_run_url': run_url,
        'github_event': os.environ.get('GITHUB_EVENT_NAME'),
        'repository_visibility': os.environ.get('REPOSITORY_VISIBILITY', 'local'),
        'identity_note': 'Precommit verification is identified by source hashes; timestamps do not establish priority.',
        'trust_note': 'Theorems marked with Lean.ofReduceBool and Lean.trustCompiler rely on native_decide: '
                      'the Lean compiler and runtime are trusted in addition to the kernel.',
        'toolchain': json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
        'source_sha256': manifest_hashes(),
        'audited_theorems': sorted(TARGETS),
        'expected_axioms': {k: sorted(v) for k, v in sorted(TARGETS.items())},
        'axiom_dependencies': actual_axioms,
        'transcript': 'verification.log',
        'theorem_types_and_axioms': 'kernel-check.log',
    }
    (ROOT / '.build/verification.json').write_text(json.dumps(data, indent=2) + '\n')
    print('Wrote .build/verification.json')
else:
    raise SystemExit('Unknown audit mode: ' + mode)
