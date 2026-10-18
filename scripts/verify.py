"""Verify the library, reference-axiom boundary, and exact completion scope."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

REFERENCE_AXIOMS = {
    'References.lean': ['bernshteyn_theorem_1_12', 'gjks_theorem_3_5_1'],
    'FiniteSourceReferences.lean': ['gjks_direction_preserving_twelve_tiles',
                                  'gjks_eventual_twelve_tile_source',
                                  'bernshteyn_directed_twelve_tiles_universality'],
}
REFERENCE_NAMES = ['AbelianTargets.References.' + name
                   for names in REFERENCE_AXIOMS.values() for name in names]

def lean_code(text):
    """Remove nested comments and strings before looking for proof escapes."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            depth, i = 1, i + 2
            out.append(' ')
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            out.append('\n')
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise RuntimeError('Unterminated Lean block comment')
    return ''.join(out)

def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, encoding='utf-8',
                            errors='replace', capture_output=True)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError('Command failed: ' + ' '.join(command))
    return result.stdout

def main():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8', errors='replace')
    parser = argparse.ArgumentParser()
    parser.add_argument('--skip-build', action='store_true')
    parser.add_argument('--record', action='store_true',
                        help='Save the verification report in docs/verification.json')
    args = parser.parse_args()
    files = [ROOT / 'AbelianTargets.lean', ROOT / 'AxiomAudit.lean']
    files += sorted((ROOT / 'AbelianTargets').glob('*.lean'))
    checked_paths = files + [ROOT / 'lean-toolchain', ROOT / 'lakefile.toml',
                             ROOT / 'lake-manifest.json']
    source_snapshot = {str(p.relative_to(ROOT)).replace('\\', '/'):
                       hashlib.sha256(p.read_bytes()).hexdigest() for p in checked_paths}
    umbrella = (ROOT / 'AbelianTargets.lean').read_text(encoding='utf-8')
    umbrella_imports = set(re.findall(r'^\s*import\s+(AbelianTargets\.[\w]+)\s*$',
                                     lean_code(umbrella), re.MULTILINE))
    for path in files:
        code = lean_code(path.read_text(encoding='utf-8'))
        banned = re.findall(r'\b(?:sorry|admit|unsafe|native_decide)\b', code)
        if banned:
            raise RuntimeError(f'Untrusted proof escape in {path.name}: {banned}')
        declarations = re.findall(r'\baxiom\s+([\w.\']+)', code)
        expected = REFERENCE_AXIOMS.get(path.name, [])
        if sorted(declarations) != sorted(expected):
            raise RuntimeError(f'Unexpected or missing reference axioms in {path.name}: '
                               f'{declarations}; expected {expected}')
        if len(re.findall(r'\baxiom\b', code)) != len(declarations):
            raise RuntimeError(f'Unrecognized axiom syntax in {path.name}')
        if path.parent.name == 'AbelianTargets':
            if f'AbelianTargets.{path.stem}' not in umbrella_imports:
                raise RuntimeError(f'Module omitted from umbrella import: {path.name}')
    if not args.skip_build:
        run(['lake', 'build'])
    audit = run(['lake', 'env', 'lean', 'AxiomAudit.lean'])
    match = re.search(r'AUDIT_OK: (\d+) declarations', audit)
    if not match:
        raise RuntimeError('Kernel axiom audit did not report success')
    if 'FINAL_POSITIVE_AXIOMS_OK' not in audit:
        raise RuntimeError('Completed positive proofs did not pass their standard-axiom-only audit')
    current_paths = [ROOT / 'AbelianTargets.lean', ROOT / 'AxiomAudit.lean']
    current_paths += sorted((ROOT / 'AbelianTargets').glob('*.lean'))
    current_paths += [ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json']
    current_sources = {str(p.relative_to(ROOT)).replace('\\', '/'):
                       hashlib.sha256(p.read_bytes()).hexdigest() for p in current_paths}
    if current_sources != source_snapshot:
        raise RuntimeError('Source inventory or contents changed during verification; run again')
    print(audit.strip())
    report = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'library_modules': len(files) - 2,
        'library_build': 'passed' if not args.skip_build else 'supplied_by_caller',
        'kernel_axiom_audit': 'passed',
        'audited_declarations': int(match.group(1)),
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'allowed_reference_axioms': REFERENCE_NAMES,
        'reference_axioms_authorized_by_user': True,
        'archive_notes_used_as_axioms': False,
        'proof_escape_source_scan': 'passed',
        'lean_version': run(['lake', 'env', 'lean', '--version']).strip(),
        'paper_results_fully_proved': True,
        'proved_statements': {
            'Theorem14Statement': 'AbelianTargets.theorem1_4',
            'Proposition71Statement': 'AbelianTargets.proposition7_1',
            'Proposition77Statement': 'AbelianTargets.proposition7_7',
        },
        'proved_corollaries': ['AbelianTargets.finiteGraphClasses_strictDecrease'],
        'positive_results_dimensions_proved': 'all integers d >= 1',
        'positive_results_reference_axioms': [],
        'positive_results_additional_construction_hypotheses': [],
        'open_statements': [],
        'proved_geometric_components': {
            'continuous_rectangular_atlas': 'AbelianTargets.exists_regularAnisotropicAtlas',
            'uniform_whole_carrier_contractions':
                'AbelianTargets.IntervalCarriers.exists_uniformCarrierContractions',
            'uniform_carrier_support_projection':
                'AbelianTargets.SupportTorsionData.carrierProjection_uniform_modulus',
            'deterministic_quantitative_rank_builder':
                'AbelianTargets.actualQuantitativeSkeleton',
            'anisotropic_rank_estimates': 'AbelianTargets.anisotropic_rank_rates_bound',
            'canonical_cell_contraction_covariance':
                'AbelianTargets.canonicalCellContraction_translate',
            'canonical_rank_recursion_covariance':
                'AbelianTargets.canonicalQuantitativeSkeleton_translate',
            'finite_recursive_locality': 'AbelianTargets.actualQuantitativeSkeleton_locality',
            'action_parameter_origin_continuity':
                'AbelianTargets.ContinuousMarkerBoxes.continuous_canonicalProjectedMap',
            'action_parameter_origin_finite_range':
                'AbelianTargets.ContinuousMarkerBoxes.canonicalProjectedMap_finite_range',
            'unit_step_parity_closing':
                'AbelianTargets.approximateParityMaps_of_unitStepConstruction',
            'action_level_canonical_covariance':
                'AbelianTargets.ContinuousMarkerBoxes.canonicalProjectedMap_repoint_forward',
            'normalized_contractions_and_scale_selection':
                'AbelianTargets.exists_smallAtlasParameters',
            'actual_small_step_lattice_orbit_maps':
                'AbelianTargets.exists_smallStepLatticeOrbitMap',
            'inverse_sheared_action': 'AbelianTargets.ParitySheared',
            'universal_support_approximate_parity_maps':
                'AbelianTargets.approximateParityMaps_supportPair',
        },
        'source_sha256': source_snapshot,
    }
    if args.record:
        (ROOT / 'docs' / 'verification.json').write_text(
            json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('Checked library: PASS. Theorem 1.4 and Proposition 7.1: PROVED in every '
          'positive dimension, using only standard Lean axioms. Proposition 7.7: '
          'PROVED with named reference axioms.')

if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
