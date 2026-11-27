"""Convert cayley_search.py output into portable exact certificate records."""
import argparse
import itertools
import json
from pathlib import Path

from cayley_search import cayley


def normalize(record):
    assert record['result'] == 'fair_exactly_verified'
    details = record['details']
    family = details['family']
    if family == 'circulant':
        n = record['n']
        elements = list(range(n))
        classes = [sorted({s, (-s) % n}) for s in details['steps']]
        def mul(x, y):
            return (x + y) % n
    elif family == 'dihedral':
        q = details['q']
        elements = [(i, b) for b in range(2) for i in range(q)]
        classes = [[tuple(x) for x in cl] for cl in details['classes']]
        def mul(x, y):
            return ((x[0] + (-1 if x[1] else 1) * y[0]) % q, x[1] ^ y[1])
    elif family == 'symmetric':
        degree = details['size']
        elements = list(itertools.permutations(range(degree)))
        classes = [[tuple(x) for x in cl] for cl in details['classes']]
        def mul(x, y):
            return tuple(x[y[i]] for i in range(degree))
    else:
        raise ValueError(family)
    n, edges, _, translations = cayley(elements, mul, classes)
    assert n == record['n'] and len(edges) == record['m']
    index = {v: i for i, v in enumerate(elements)}
    generators = [translations[index[cl[0]]] for cl in classes]
    cert = record['certificate']
    return {'id': record['tag'], 'family': family + '_cayley', 'n': n,
            'edges': edges, 'generators': generators,
            'paths': cert['paths'], 'weights': cert['rational_weights']}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input')
    parser.add_argument('output')
    args = parser.parse_args()
    with Path(args.input).open() as source, Path(args.output).open('w') as dest:
        count = 0
        for line in source:
            if line.strip():
                dest.write(json.dumps(normalize(json.loads(line)), separators=(',', ':')) + '\n')
                count += 1
    print(json.dumps({'normalized_instances': count}))


if __name__ == '__main__':
    main()
