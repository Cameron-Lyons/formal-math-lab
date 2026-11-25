"""Independent tuple-monomial arithmetic for coordinate-model audits."""
from collections import Counter
from itertools import combinations, product
from exact_elementary_review import geometry, gf4_mul
from exact_msolve_review import parse_polynomial


def canonical(term, cubic_mod=False):
    if not cubic_mod:
        return tuple(sorted(term))
    return tuple(i for i,n in sorted(Counter(term).items()) for _ in range(n % 3))


def multiply(left,right,cubic_mod=False):
    result = set()
    for a in left:
        for b in right:
            term = canonical(a+b,cubic_mod)
            result.symmetric_difference_update((term,))
    return result


def square(polynomial,cubic_mod=False):
    result = set()
    for term in polynomial:
        result.symmetric_difference_update((canonical(term+term,cubic_mod),))
    return result


def solve_linears(rows,pivots):
    rows = [set(row) for row in rows]
    for index,pivot in enumerate(pivots):
        source = next(i for i in range(index,len(rows)) if pivot in rows[i])
        rows[index],rows[source] = rows[source],rows[index]
        for i in range(len(rows)):
            if i != index and pivot in rows[i]:
                rows[i] ^= rows[index]
    answers = {pivot:rows[i]-{pivot} for i,pivot in enumerate(pivots)}
    assert all(not(set(pivots)&value) for value in answers.values())
    return answers


def build_expected(forms,cubic_mod=False):
    windows,roles = geometry()
    linear = {cell:{(i,) for i in indices} for cell,indices in forms.items()}
    squares = {cell:square(poly,cubic_mod) for cell,poly in linear.items()}
    domains = {f'domain:{cell}':multiply(linear[cell],squares[cell],cubic_mod)^{()}
               for cell in range(100)}
    moments = {}
    vanished = []
    for exponents in product(range(3),repeat=4):
        if not any(exponents):
            continue
        polynomial = set()
        for window in windows:
            term = {()}
            for cell,exponent in zip(window,exponents):
                if exponent:
                    term = multiply(term,linear[cell] if exponent==1 else squares[cell],cubic_mod)
            polynomial ^= term
        label = 'moment:'+','.join(map(str,exponents))
        if polynomial:
            moments[label] = polynomial
        else:
            vanished.append(label)
    role_e2 = {}
    for label,cells in roles.items():
        polynomial = set()
        for a,b in combinations(sorted(cells),2):
            polynomial ^= multiply(linear[a],linear[b],cubic_mod)
        role_e2[label] = polynomial
    elementary = {'e2:T':role_e2['T'],
        **{f'e2:{a}:{b}':role_e2[a]^role_e2[b] for a,b in (('T','M'),('M','L'),('M','R'))}}
    elementary.update({label+':square':square(polynomial,cubic_mod)
                       for label,polynomial in list(elementary.items())})
    assert len(moments)==72 and len(vanished)==8
    return domains,moments,elementary,vanished


def decode_polynomials(equations,variables,width,max_exponent):
    result = {}
    for equation in equations:
        label = equation['label']
        assert label not in result
        polynomial = set()
        for encoded in equation['terms']:
            value = int(encoded,16)
            assert value>=0 and not value>>(width*variables)
            factors=[]
            for i in range(variables):
                exponent = (value>>(width*i))&((1<<width)-1)
                assert exponent <= max_exponent
                factors += [i]*exponent
            term=tuple(factors)
            assert term not in polynomial
            polynomial.add(term)
        assert polynomial
        result[label]=polynomial
    return result


def input_polynomials(text,variables):
    lines=text.splitlines()
    assert lines[0]==','.join(f'x{i+1}' for i in range(variables)) and lines[1]=='2'
    result=[]
    for raw in '\n'.join(lines[2:]).split(','):
        polynomial=parse_polynomial(''.join(raw.split()),variables,2)
        decoded=set()
        for exponents,coefficient in polynomial.items():
            assert coefficient==1
            decoded.add(tuple(i for i,e in enumerate(exponents) for _ in range(e)))
        result.append(decoded)
    return result


def evaluate(polynomial,values):
    result=0
    for term in polynomial:
        value=1
        for i in term:
            value=gf4_mul(value,values[i])
        result ^= value
    return result
