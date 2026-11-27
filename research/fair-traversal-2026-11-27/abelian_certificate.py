"""Construct and independently verify fair paths in finite abelian Cayley graphs.

The existence proof is in structural-results.md. Linear programming only chooses
a convex combination of explicit subgroup-snake paths. The saved certificate is
checked with exact integers by expanding every translation of every seed path.

Examples:
  python abelian_certificate.py demo --output abelian_examples.json
  python abelian_certificate.py verify abelian_examples.json

Dependencies for construction: numpy, scipy, sympy.
Verification uses only Python's standard library.
"""
import argparse
from collections import Counter
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run this verifier without Python -O: assertions are required.')


class AbelianGraph:
    def __init__(self, moduli, generators):
        assert moduli and all(isinstance(m, int) and m >= 2 for m in moduli)
        self.moduli = tuple(moduli)
        self.vertices = list(itertools.product(*(range(m) for m in moduli)))
        self.index = {v: i for i, v in enumerate(self.vertices)}
        self.n = len(self.vertices)
        self.zero = self.vertices[0]
        classes = []
        used = set()
        for g in generators:
            assert len(g) == len(moduli)
            g = tuple(x % m for x, m in zip(g, moduli))
            assert g != self.zero
            cl = sorted({g, self.neg(g)})
            if g not in used:
                assert not used.intersection(cl)
                classes.append(cl)
                used.update(cl)
        assert classes
        self.classes = classes
        self.representatives = [cl[0] for cl in classes]
        self.class_of = {g: i for i, cl in enumerate(classes) for g in cl}
        self.d = len(used)
        self.t = len(classes)
        self.q = [Fraction((self.n - 1) * len(cl), self.d) for cl in classes]
        self.edges = sorted({tuple(sorted((self.index[x], self.index[self.add(x, g)])))
                             for x in self.vertices for g in used})
        self.edge_index = {e: i for i, e in enumerate(self.edges)}

    def add(self, a, b):
        return tuple((x + y) % m for x, y, m in zip(a, b, self.moduli))

    def neg(self, a):
        return tuple(-x % m for x, m in zip(a, self.moduli))

    def snake(self, order):
        assert sorted(order) == list(range(self.t))
        path = [self.zero]
        for i in order:
            g = self.representatives[i]
            H = set(path)
            offsets = [self.zero]
            current = g
            while current not in H:
                offsets.append(current)
                current = self.add(current, g)
            old = path
            path = [self.add(offset, v)
                    for j, offset in enumerate(offsets)
                    for v in (old if j % 2 == 0 else reversed(old))]
            assert len(set(path)) == len(path)
        if len(path) != self.n:
            raise ValueError('The supplied generators do not generate the whole group.')
        ids = [self.index[v] for v in path]
        return ids, self.path_counts(ids)

    def path_counts(self, path):
        assert sorted(path) == list(range(self.n))
        counts = [0] * self.t
        for a, b in zip(path, path[1:]):
            assert tuple(sorted((a, b))) in self.edge_index
            delta = self.add(self.vertices[b], self.neg(self.vertices[a]))
            counts[self.class_of[delta]] += 1
        assert sum(counts) == self.n - 1
        return counts

    def construct(self):
        import numpy as np
        from scipy.optimize import linprog
        import sympy as sp

        p, c = self.snake(list(range(self.t)))
        paths, columns = [p], [c]
        q = np.array(list(map(float, self.q)))
        # There are finitely many distinct orderings; an exact separating oracle
        # must add a new vector whenever the target is outside the current hull.
        while True:
            C = np.array(columns).T
            primal = linprog(np.zeros(len(columns)),
                             A_eq=np.vstack([C, np.ones(len(columns))]),
                             b_eq=np.r_[q, 1], bounds=(0, None), method='highs')
            if primal.success:
                indices = [i for i, x in enumerate(primal.x) if x > 1e-9]
                break
            D = C.T - q
            dual = linprog(np.r_[np.zeros(self.t), -1.0],
                           A_ub=np.c_[-D, np.ones(len(columns))],
                           b_ub=np.zeros(len(columns)),
                           bounds=[(-1, 1)] * self.t + [(None, None)], method='highs')
            if not dual.success:
                raise RuntimeError('Numerical separation failed; no mathematical conclusion.')
            # Ascending weights minimize the support functional.
            order = sorted(range(self.t), key=lambda i: (dual.x[i], i))
            path, counts = self.snake(order)
            if counts in columns:
                raise RuntimeError('Numerical solver stalled; no mathematical conclusion.')
            paths.append(path)
            columns.append(counts)

        active = [columns[i] for i in indices]
        A = sp.Matrix(self.t + 1, len(indices),
                      lambda i, j: active[j][i] if i < self.t else 1)
        target = sp.Matrix([sp.Rational(x.numerator, x.denominator) for x in self.q] + [1])
        weights, params = A.gauss_jordan_solve(target)
        if params.rows:
            weights = weights.subs({x: 0 for x in params})
        assert A * weights == target
        assert all(w.is_Rational and w >= 0 for w in weights)
        denominator = math.lcm(*(int(w.q) for w in weights))
        multiplicities = [int(w * denominator) for w in weights]
        cert = {
            'moduli': self.moduli,
            'generators': self.representatives,
            'n': self.n,
            'degree': self.d,
            'seed_paths': [paths[i] for i in indices],
            'seed_multiplicities': multiplicities,
            'rational_weights': [str(w) for w in weights],
            'orbit_counts': active,
            'r': self.n * denominator,
            'k': int(Fraction(2 * denominator * (self.n - 1), self.d)),
            'translation_rule': 'Add each group element to every vertex of each seed path.'
        }
        assert Fraction(2 * denominator * (self.n - 1), self.d).denominator == 1
        verify(cert)
        return cert


def verify(cert):
    """Check the actual integer multiset, with no optimizer or symbolic library."""
    G = AbelianGraph(cert['moduli'], cert['generators'])
    assert cert['n'] == G.n and cert['degree'] == G.d
    paths = cert['seed_paths']
    weights = cert['seed_multiplicities']
    assert len(paths) == len(weights) == len(cert['orbit_counts'])
    assert all(isinstance(w, int) and w >= 0 for w in weights)
    assert sum(weights) > 0
    assert [Fraction(w) for w in cert['rational_weights']] == [Fraction(w, sum(weights)) for w in weights]
    for path, supplied in zip(paths, cert['orbit_counts']):
        assert G.path_counts(path) == supplied
    coverage = [0] * len(G.edges)
    for g in G.vertices:
        permutation = [G.index[G.add(g, v)] for v in G.vertices]
        for path, weight in zip(paths, weights):
            translated = [permutation[v] for v in path]
            assert len(set(translated)) == G.n
            for a, b in zip(translated, translated[1:]):
                coverage[G.edge_index[tuple(sorted((a, b)))]] += weight
    assert len(set(coverage)) == 1 and coverage[0] > 0
    assert coverage[0] == cert['k']
    assert G.n * sum(weights) == cert['r']
    assert cert['r'] * (G.n - 1) == cert['k'] * len(G.edges)
    return {'n': G.n, 'degree': G.d, 'seed_paths': len(paths),
            'r': cert['r'], 'k': cert['k'], 'verified': True}


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest='action', required=True)
    demo = sub.add_parser('demo')
    demo.add_argument('--output', default='abelian_examples.json')
    audit = sub.add_parser('verify')
    audit.add_argument('file')
    args = parser.parse_args()
    if args.action == 'demo':
        examples = [
            ([6], [[2], [3]]),
            ([30], [[6], [10], [15]]),
            ([4, 6], [[1, 0], [0, 1], [1, 2]]),
            ([3, 3, 3], [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1]]),
            ([2, 2, 2, 2, 2], [[int(i == j) for i in range(5)] for j in range(5)]),
            ([8, 9], [[2, 0], [3, 0], [0, 3], [0, 2], [1, 1]]),
            ([6, 10], [[1, 0], [0, 1], [1, 1], [3, 5]])
        ]
        certificates = [AbelianGraph(m, g).construct() for m, g in examples]
        Path(args.output).write_text(json.dumps(certificates, indent=2) + '\n')
    else:
        certificates = json.loads(Path(args.file).read_text())
    print(json.dumps([verify(c) for c in certificates], indent=2))


if __name__ == '__main__':
    main()
