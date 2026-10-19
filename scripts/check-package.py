#!/usr/bin/env python3
"""Check the package inventory, source manifest, evidence, and local documentation links.

SOURCE_SHA256SUMS covers every file that can affect verification or that preserves
supplied material. Documentation is inventoried and link-checked but not hashed, so that
editing prose does not invalidate recorded verification evidence.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
CERTS = ('65532_65516', '65532_65500', '65532_65468', '65518_65516', '65518_65486',
         '65518_65006', '65502_65500', '65502_65498', '65502_65486', '65502_65438',
         '65502_65246', '65502_64990', '65502_64478')
LEAN = {
    'Verification.lean', 'scripts/PrintAxioms.lean', 'GyiresCompute/Basic.lean',
    'GyiresStrictCompute/Basic.lean',
    *('RequestProject/' + n + '.lean' for n in
      ('Faces', 'Gyires', 'HEval', 'Main', 'PolySound', 'Reduction', 'TreeSound',
       'Cert/Defs', 'Cert/Assemble')),
    *(f'RequestProject/Cert/C_{c}.lean' for c in CERTS),
    *('GyiresEquality/' + n + '.lean' for n in ('StrictSound', 'Assemble', 'Equality', 'Ratio')),
    *(f'GyiresEquality/Cert/S_{c}.lean' for c in CERTS),
}
SOURCES = LEAN | {
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'TOOLCHAIN.json',
    'verify.sh', '.gitignore', '.github/workflows/verify.yml',
    'scripts/install-lean.sh', 'scripts/fetch-deps.sh', 'scripts/audit.py',
    'scripts/check-package.py',
    'crosscheck/tree.py', 'crosscheck/leafcheck.cpp', 'crosscheck/run.sh',
    'original/RESULTS.original.txt', 'original/RESULTS_certificate/generate.py',
    'original/RESULTS_certificate/verify.cpp', 'original/RESULTS_certificate/verification.txt',
    'provenance/aristotle/gyires-lean-complete.tar.gz',
    'provenance/aristotle/ARISTOTLE_SUMMARY_run_c0b83b52.md',
    'provenance/aristotle/ARISTOTLE_SUMMARY_run_eb710500.md',
    'provenance/aristotle/README.md', 'provenance/aristotle/REPRODUCE.md',
}
DOCS = {
    'README.md', 'PROOF.md', 'PRIOR_ART.md', 'PROVENANCE.md', 'VERIFICATION_REPORT.md',
    'REPRODUCE.md', 'CITATION.cff', 'LICENSE', 'crosscheck/README.md', 'original/README.md',
    'original/RESULTS.md',
}
EVIDENCE = {'evidence/' + n for n in
            ('verification.log', 'kernel-check.log', 'verification.json', 'crosscheck.log',
             'aristotle-asreceived-build.log')}
GENERATED = {'.git', '.lake', '.tools', '.build', '__pycache__'}
# GitHub's math renderer rejects \operatorname and \phantom ("The following macros are not
# allowed"). The rest are avoided because their support is unconfirmed or they are unsafe.
BLOCKED_MATH = re.compile(r'\\(operatorname|phantom|tag|boxed|text|DeclareMathOperator|'
                          r'newcommand|renewcommand|def|href|url|class|style|cssId|require|'
                          r'html[A-Za-z]*)\b')


def math_segments(text):
    """Math rendered by GitHub: ```math fences, $$...$$ and $...$ outside code."""
    segments, prose, fence, buffer = [], [], None, []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith('```'):
            if fence is None:
                fence, buffer = stripped[3:].strip(), []
            else:
                if fence == 'math':
                    segments.append('\n'.join(buffer))
                fence = None
            continue
        (buffer if fence is not None else prose).append(line)
    rest = re.sub(r'`[^`\n]*`', '', '\n'.join(prose))
    segments += re.findall(r'\$\$(.*?)\$\$', rest, flags=re.S)
    rest = re.sub(r'\$\$.*?\$\$', '', rest, flags=re.S)
    return segments + re.findall(r'\$([^$\n]+)\$', rest)


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def main():
    require(sys.argv[1:] in ([], ['--sources-only']), 'Unexpected arguments')
    sources_only = sys.argv[1:] == ['--sources-only']
    expected = SOURCES | DOCS | EVIDENCE | {'SOURCE_SHA256SUMS'}
    required = SOURCES | {'SOURCE_SHA256SUMS'} | (set() if sources_only else DOCS | EVIDENCE)
    present = set()
    for parent, dirs, files in os.walk(ROOT):
        dirs[:] = [n for n in dirs if n not in GENERATED]
        for name in files:
            path = Path(parent) / name
            require(not path.is_symlink(), 'Package must contain regular files')
            present.add(path.relative_to(ROOT).as_posix())
    require(not (present - expected), 'Unexpected package files: ' +
            ', '.join(sorted(present - expected)))
    require(required <= present, 'Missing required package files: ' +
            ', '.join(sorted(required - present)))

    hashes = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(name in SOURCES and name not in hashes, 'Invalid manifest inventory: ' + name)
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed digest')
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest,
                'Source hash mismatch: ' + name)
        hashes[name] = digest
    require(set(hashes) == SOURCES, 'Incomplete source manifest')

    math = 0
    for doc in sorted(ROOT.rglob('*.md')):
        if any(part in GENERATED for part in doc.relative_to(ROOT).parts):
            continue
        for segment in math_segments(doc.read_text()):
            bad = BLOCKED_MATH.search(segment)
            require(bad is None, f'Math macro {bad and bad.group(0)} will not render on GitHub: '
                    + doc.relative_to(ROOT).as_posix())
            math += 1

    links = 0
    for doc in sorted([*ROOT.glob('*.md'), *ROOT.glob('*/README.md'), ROOT / 'original/RESULTS.md']):
        text = re.sub(r'```.*?```', '', doc.read_text(), flags=re.S)
        for match in re.finditer(r'\[[^\]\n]+\]\(([^)]+)\)', text):
            target = match.group(1).strip().strip('<>')
            url = urlsplit(target)
            if url.scheme or url.netloc:
                continue
            path = (doc.parent / unquote(url.path)).resolve() if url.path else doc
            relative = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else None
            require(relative is not None, 'Documentation link outside package: ' + target)
            is_dir = path.is_dir() and any(e.startswith(relative + '/') for e in expected)
            require(relative in expected or is_dir,
                    f'Documentation link to an uninventoried path in {doc.name}: {target}')
            require(path.exists() or (sources_only and relative in EVIDENCE),
                    f'Broken documentation link in {doc.name}: {target}')
            links += 1

    if not sources_only:
        report = json.loads((ROOT / 'evidence/verification.json').read_text())
        require(report['verification_exit_code'] == 0 and report['status'] == 'PASS',
                'Recorded verification did not pass')
        require(report['source_sha256'] == hashes, 'Evidence covers different sources')
        require(report['toolchain'] == json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
                'Evidence uses different pins')
        require('VERIFY_EXIT_CODE=0' in (ROOT / 'evidence/verification.log').read_text(),
                'Missing successful verification transcript')
        require('NEGATIVE_CONTROL=PASS' in (ROOT / 'evidence/crosscheck.log').read_text(),
                'Missing successful cross-check transcript')
    print(f'PASS: package inventory, {len(hashes)} source hashes, {links} local links, and '
          f'{math} math segments free of macros GitHub rejects.')


if __name__ == '__main__':
    main()
