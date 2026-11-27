"""Reproducible finite search for fair Hamiltonian-path distributions.

MILP/LP solutions are only discovery aids. Positive results are independently
checked using rational arithmetic and every left translation of the paths.
No negative numerical result is treated as a mathematical counterexample.
"""
import argparse
import itertools
import json
import math
from pathlib import Path
import random
import sys
import time

import numpy as np
import sympy as sp

from search import Oracle

ROOT = Path(__file__).resolve().parent


def connected(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = {0}
    todo = [0]
    while todo:
        for v in adj[todo.pop()]:
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return len(seen) == n


def cayley(elements, multiply, generator_classes):
    """Right Cayley edges, acted on by all left translations."""
    index = {x: i for i, x in enumerate(elements)}
    assignment = {}
    for j, generators in enumerate(generator_classes):
        for x in elements:
            for s in generators:
                e = tuple(sorted((index[x], index[multiply(x, s)])))
                assert e[0] != e[1]
                assert e not in assignment or assignment[e] == j
                assignment[e] = j
    edges = sorted(assignment)
    orbit = np.array([assignment[e] for e in edges], dtype=int)
    translations = [[index[multiply(g, x)] for x in elements] for g in elements]
    return len(elements), edges, orbit, translations


def exact_certificate(n, edges, orbit, translations, support):
    """Validate paths and integer multiplicities after all translations."""
    t = int(max(orbit)) + 1
    positions = {tuple(e): i for i, e in enumerate(edges)}
    columns = []
    paths = []
    for _, path, supplied_counts in support:
        assert sorted(path) == list(range(n))
        counts = [0] * t
        for u, v in zip(path, path[1:]):
            counts[orbit[positions[tuple(sorted((u, v)))]]] += 1
        assert counts == supplied_counts
        paths.append(path)
        columns.append(counts)
    A = sp.Matrix(t + 1, len(columns), lambda i, j: columns[j][i] if i < t else 1)
    sizes = np.bincount(orbit, minlength=t).tolist()
    target = sp.Matrix([sp.Rational((n - 1) * k, len(edges)) for k in sizes] + [1])
    sol, params = A.gauss_jordan_solve(target)
    if params.rows:
        sol = sol.subs({x: 0 for x in params})
    assert A * sol == target
    assert all(x.is_Rational and x >= 0 for x in sol)
    denom = int(sp.ilcm(*[x.q for x in sol])) if len(sol) > 1 else int(sol[0].q)
    weights = [int(x * denom) for x in sol]
    coverage = [0] * len(edges)
    # This checks the actual integer edge coverage, not just orbit totals.
    for permutation in translations:
        assert sorted(permutation) == list(range(n))
        for u, v in edges:
            assert tuple(sorted((permutation[u], permutation[v]))) in positions
        for weight, path in zip(weights, paths):
            for u, v in zip(path, path[1:]):
                coverage[positions[tuple(sorted((permutation[u], permutation[v])))]] += weight
    assert min(coverage) > 0 and len(set(coverage)) == 1
    r = sum(weights) * len(translations)
    k = coverage[0]
    assert r * (n - 1) == k * len(edges)
    return {'r': r, 'k': k, 'translation_count': len(translations),
            'path_multiplicities_before_translation': weights,
            'rational_weights': [str(x) for x in sol], 'paths': paths,
            'counts': columns, 'target': [str(x) for x in target[:-1]]}


def run_one(tag, graph, details, limit=2):
    n, edges, orbit, translations = graph
    if not connected(n, edges):
        return None
    start = time.monotonic()
    result = Oracle(n, edges, orbit).column_generation(limit=limit, rounds=50)
    record = {'tag': tag, 'n': n, 'm': len(edges), 'orbits': int(max(orbit)) + 1,
              'details': details, **result}
    if 'support' in result:
        record['certificate'] = exact_certificate(n, edges, orbit, translations, result['support'])
        record['result'] = 'fair_exactly_verified'
        del record['support']
    record['seconds'] = round(time.monotonic() - start, 3)
    with (ROOT / 'cayley_results.jsonl').open('a') as f:
        f.write(json.dumps(record) + '\n')
    if record['result'] != 'fair_exactly_verified':
        (ROOT / (tag + '_unresolved.json')).write_text(json.dumps({
            **record, 'edges': edges, 'orbit': orbit.tolist(), 'translations': translations}, indent=2))
        print(json.dumps({k: record[k] for k in ['tag', 'n', 'result', 'seconds']}), flush=True)
    return record['result']


def circulants():
    for n in range(4, 29):
        possible = list(range(1, n // 2 + 1))
        for size in (2, 3):
            combos = list(itertools.combinations(possible, size))
            if len(combos) > 100:
                rng = random.Random(1729 + n * 7 + size)
                combos = rng.sample(combos, 100)
            for steps in combos:
                if math.gcd(n, *steps) != 1:
                    continue
                classes = [sorted({s, (-s) % n}) for s in steps]
                graph = cayley(list(range(n)), lambda x, y: (x + y) % n, classes)
                yield 'C_' + str(n) + '_' + '_'.join(map(str, steps)), graph, {'family': 'circulant', 'steps': steps}


def dihedrals():
    for q in range(3, 21):
        el = [(i, b) for b in range(2) for i in range(q)]
        def mul(x, y):
            return ((x[0] + (-1 if x[1] else 1) * y[0]) % q, x[1] ^ y[1])
        classes = [sorted({(s, 0), ((-s) % q, 0)}) for s in range(1, q // 2 + 1)]
        classes += [[(s, 1)] for s in range(q)]
        combos = []
        for size in (2, 3, 4):
            pool = [x for x in itertools.combinations(range(len(classes)), size)
                    if 3 <= sum(len(classes[i]) for i in x) <= 6
                    and any(classes[i][0][1] for i in x)]
            if len(pool) > 50:
                pool = random.Random(2718 + q * 7 + size).sample(pool, 50)
            combos.extend(pool)
        for indices in combos:
            selected = [classes[i] for i in indices]
            graph = cayley(el, mul, selected)
            yield 'D_' + str(q) + '_' + '_'.join(map(str, indices)), graph, {'family': 'dihedral', 'q': q, 'classes': selected}


def permutations():
    for size in (3, 4):
        el = list(itertools.permutations(range(size)))
        identity = tuple(range(size))
        def mul(x, y):
            return tuple(x[y[i]] for i in range(size))
        def inverse(x):
            return tuple(x.index(i) for i in range(size))
        classes = []
        seen = {identity}
        for x in el:
            if x not in seen:
                cl = sorted({x, inverse(x)})
                seen.update(cl)
                classes.append(cl)
        for length in (3, 4):
            pool = [x for x in itertools.combinations(range(len(classes)), length)
                    if 3 <= sum(len(classes[i]) for i in x) <= 6]
            if len(pool) > 150:
                pool = random.Random(31415 + size * 11 + length).sample(pool, 150)
            for indices in pool:
                selected = [classes[i] for i in indices]
                yield 'S_' + str(size) + '_' + '_'.join(map(str, indices)), cayley(el, mul, selected), {'family': 'symmetric', 'size': size, 'classes': selected}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('family', choices=['circulant', 'dihedral', 'symmetric'])
    parser.add_argument('--limit', type=float, default=2)
    args = parser.parse_args()
    gen = {'circulant': circulants, 'dihedral': dihedrals, 'symmetric': permutations}[args.family]
    done = {json.loads(line)['tag'] for line in (ROOT/'cayley_results.jsonl').read_text().splitlines()} if (ROOT/'cayley_results.jsonl').exists() else set()
    counts = {}
    total = 0
    for tag, graph, details in gen():
        if tag in done:
            continue
        result = run_one(tag, graph, details, args.limit)
        if result:
            counts[result] = counts.get(result, 0) + 1
            total += 1
        if total and total % 25 == 0:
            print(json.dumps({'family': args.family, 'processed': total, 'counts': counts, 'last': tag}), flush=True)
    print(json.dumps({'family': args.family, 'completed': True, 'processed': total, 'counts': counts}), flush=True)


if __name__ == '__main__':
    main()
