"""Regenerate and verify the finite UNSAT instances for L-meta-652."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

from encoding import Instance, MATCHINGS, main_case, signature, subcubes, tables

HERE = Path(__file__).resolve().parent

def verify_witness():
    pairs = [((0,3),(1,4),(2,5)),((0,4),(1,5),(2,3)),((0,5),(1,3),(2,4))]
    assert [list(m) for m in pairs] == MATCHINGS
    for row in range(64):
        inputs = [bool(row & (1 << k)) for k in range(6)]
        values = inputs.copy()
        for edges in pairs:
            start = len(values)
            for a,b in edges:
                values.append(values[a] and values[b])
            values.append(values[start] or values[start+1])
            values.append(values[start+2] or values[start+3])
        assert len(values) == 21
        assert [values[j] for j in [10,15,20]] == [
            any(inputs[a] and inputs[b] for a,b in edges) for edges in pairs]

def build(cube, minimum, small_bounds=None):
    instance = Instance(cube, minimum-1, allow_dead=True, support_prune=False)
    if small_bounds is not None:
        for sub in subcubes(cube,4):
            instance.restrict(sub,small_bounds[signature(sub)])
    return instance

def verify(name, instance, args, manifest):
    prefix = args.output / name
    cnf = prefix.with_suffix('.cnf')
    proof = prefix.with_suffix('.lrat')
    instance.cnf.to_file(str(cnf))
    digest = hashlib.sha256(cnf.read_bytes()).hexdigest()
    if digest != manifest[name]['cnf_sha256']:
        raise RuntimeError(f'CNF hash differs for {name}')
    if [] in instance.cnf.clauses:
        print(name, 'contains the empty clause', flush=True)
        return
    if args.generate_only:
        print(name, 'CNF hash verified', flush=True)
        return
    with prefix.with_suffix('.solver.log').open('w') as log:
        result = subprocess.run([args.cadical,'--lrat',str(cnf),str(proof)],stdout=log)
    if result.returncode != 20:
        raise RuntimeError(f'CaDiCaL did not return UNSAT for {name}')
    result = subprocess.run([args.checker,str(cnf),str(proof)],capture_output=True,text=True)
    prefix.with_suffix('.checker.log').write_text(result.stdout+result.stderr)
    if result.returncode != 20 or 's VERIFIED' not in result.stdout.splitlines():
        raise RuntimeError(f'LRAT verification failed for {name}')
    print(name,'s VERIFIED',flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cadical',default='cadical')
    parser.add_argument('--checker',default='lrat-trim')
    parser.add_argument('--output',type=Path,default=Path('certificates'))
    parser.add_argument('--generate-only',action='store_true')
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    minima=json.loads((HERE/'minima.json').read_text())
    manifest=json.loads((HERE/'manifest.json').read_text())
    verify_witness()
    all_subcubes={signature(c) for free in [2,3,4] for c in subcubes('******',free)}
    assert all_subcubes==set(minima)
    for c,m in minima.items():
        if m:
            verify(c.replace('*','x'),build(c,m),args,manifest)
        else:
            assert not tables(c)[1]
    for cube,minimum in [('0*****',9),('1*****',12)]:
        verify(cube.replace('*','x'),build(cube,minimum,minima),args,manifest)
    for name in ['not','same','cross']:
        verify(name,main_case(name,minima),args,manifest)
if __name__=='__main__':main()
