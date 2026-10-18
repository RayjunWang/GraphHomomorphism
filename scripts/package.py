"""Create a source-only ZIP; never traverse local dependency caches."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT.parent / (ROOT.name + '.zip')
ROOT_FILES = {'AbelianTargets.lean', 'AxiomAudit.lean', 'lean-toolchain',
              'lakefile.toml', 'lake-manifest.json', 'README.md', 'LICENSE',
              'NOTICE.md', '.gitignore'}
FILES = [ROOT / name for name in ROOT_FILES]
for path in FILES:
    if not path.is_file():
        raise RuntimeError('Required source file missing: ' + path.name)
for directory in ('AbelianTargets', 'docs', 'scripts', '.github'):
    FILES += [p for p in (ROOT / directory).rglob('*') if p.is_file()
              and '__pycache__' not in p.parts]
FILES = sorted(FILES, key=lambda p: str(p.relative_to(ROOT)))

report_path = ROOT / 'docs' / 'verification.json'
report = json.loads(report_path.read_text(encoding='utf-8'))
if (report.get('library_build') != 'passed' or
        report.get('kernel_axiom_audit') != 'passed' or
        report.get('proof_escape_source_scan') != 'passed'):
    raise RuntimeError('A recorded build and audit must pass before packaging')
audited_files = [ROOT / 'AbelianTargets.lean', ROOT / 'AxiomAudit.lean']
audited_files += sorted((ROOT / 'AbelianTargets').glob('*.lean'))
audited_files += [ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json']
current_sources = {str(p.relative_to(ROOT)).replace('\\', '/') for p in audited_files}
if current_sources != set(report['source_sha256']):
    raise RuntimeError('The audited source inventory changed; run verify.py --record again')
for name, expected in report['source_sha256'].items():
    actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    if actual != expected:
        raise RuntimeError('Source changed since verification: ' + name)

with zipfile.ZipFile(OUTPUT, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
    for path in FILES:
        archive.write(path, ROOT.name + '/' + str(path.relative_to(ROOT)).replace('\\', '/'))

with zipfile.ZipFile(OUTPUT) as archive:
    if archive.testzip() is not None:
        raise RuntimeError('ZIP integrity test failed')
    if any('/.lake/' in name or '/.git/' in name for name in archive.namelist()):
        raise RuntimeError('A local cache or Git internals entered the archive')
    assert len(archive.namelist()) == len(FILES)

print(json.dumps({'archive': str(OUTPUT), 'files': len(FILES),
                  'bytes': OUTPUT.stat().st_size,
                  'sha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}, indent=2))
