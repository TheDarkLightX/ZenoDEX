#!/usr/bin/env python3
from __future__ import annotations
import json
from pathlib import Path
import yaml


def main() -> int:
    root=Path(__file__).resolve().parents[1]
    suite=json.loads((root/'formal/esso/fcis_m6_formal_suite_v1.json').read_text())
    matrix=json.loads((root/'docs/research/FCIS_M6_FORMAL_RUNTIME_REFINEMENT_MATRIX_V1.json').read_text())
    result=json.loads((root/'docs/research/FCIS_M6_FORMAL_SUITE_BOUNDED_RESULT_V1.json').read_text())
    feature=(root/matrix['feature_file']).read_text()
    errors=[]
    by_id={e['model_id']:e for e in matrix['entries']}
    suite_ids=[]
    for item in suite['models']:
        model=yaml.safe_load((root/item['path']).read_text())
        mid=model['meta']['model_id']
        suite_ids.append(mid)
        entry=by_id.get(mid)
        if entry is None:
            errors.append(f'missing matrix entry {mid}')
            continue
        actions=[a['id'] for a in model['actions']]
        invariants=[i['id'] for i in model['invariants']]
        if entry['formal_actions'] != actions:
            errors.append(f'{mid}: action registry drift')
        if entry['formal_invariants'] != invariants:
            errors.append(f'{mid}: invariant registry drift')
        if set(entry['action_to_scenario']) != set(actions):
            errors.append(f'{mid}: incomplete action-to-scenario map')
        if any(entry['action_to_scenario'][a] != entry['scenario_tag'] for a in actions):
            errors.append(f'{mid}: crossed scenario mapping')
        if entry['scenario_tag'] not in feature:
            errors.append(f'{mid}: scenario tag absent from feature file')
        if not entry['runtime_projection']:
            errors.append(f'{mid}: no runtime projection obligation')
        if entry['runtime_status'] != 'SPEC_ONLY_UNMOUNTED':
            errors.append(f'{mid}: unsupported runtime promotion claim {entry["runtime_status"]}')
    if set(by_id) != set(suite_ids):
        errors.append('matrix/suite model set differs')
    if result['verdict'] != 'PASS_BOUNDED_INDEPENDENT_REPLAY':
        errors.append('bounded formal replay is not green')
    if result['mutants_killed'] != result['mutants_total']:
        errors.append('not all formal mutants are killed')
    if matrix['composition_obligation']['status'] != 'THEOREM_STATEMENT_FROZEN_PROOF_OPEN':
        errors.append('composition theorem must not be promoted by this packet')
    verdict='FORMAL_RUNTIME_MATRIX_MATCH' if not errors else 'FORMAL_RUNTIME_MATRIX_MISMATCH'
    print(json.dumps({'verdict':verdict,'models':len(suite_ids),'actions':sum(len(e['formal_actions']) for e in matrix['entries']),'invariants':sum(len(e['formal_invariants']) for e in matrix['entries']),'errors':errors},indent=2))
    return 0 if not errors else 1

if __name__=='__main__':
    raise SystemExit(main())
