#!/usr/bin/env python3
from pathlib import Path
import itertools,json
import runner
from exact_msolve_backend import parse_leading
from exact_algebra_backend import monomial_dimension
from exact_standard_monomials import count_standard_monomials
R=Path(__file__).resolve().parent

def main():
    fixtures=[('domains1',1,[]),('domains2',2,[]),('sum3',3,['x1+x2+x3']),
      ('product1',2,['x1*x2-1']),('graph3',3,['x1*x2-x3']),
      ('chain4',4,['x1*x2-x3','x2*x3-x4']),('symmetric3',3,['x1*x2+x1*x3+x2*x3']),
      ('unit',1,['1']),('squares2',2,['x1^2+x2^2-1']),('product_zero',3,['x1*x2*x3']),
      ('mixed5',5,['x1*x2+x3*x4+x5','x1^2+x2*x5-x3','x4^2-x1*x5'])]
    cases=[]
    for name,n,extra in fixtures:
        eq=[f'x{i}^3-x{i}' for i in range(1,n+1)]+extra
        text=','.join(f'x{i}' for i in range(1,n+1))+'\n3\n'+',\n'.join(eq)+'\n'
        count=sum(all(eval(p.replace('^','**'),{'__builtins__':{}},dict(zip([f'x{i}' for i in range(1,n+1)],values)))%3==0 for p in extra) for values in itertools.product(range(3),repeat=n))
        cases.append((name,text,n,count))
    cases.append(('natural_six',(R.parent/'exact_native_field_probe_runs/ternary_six.ms').read_text(),19,6))
    n=127;text=','.join(f'x{i}' for i in range(1,n+1))+'\n3\n'+',\n'.join(f'x{i}^3-x{i}' for i in range(1,n+1))+'\n'
    cases.append(('maximum_variables',text,n,3**127))
    results=[]
    for name,text,n,expected in cases:
      for mode in [1,2]:
        old,a=runner.execute(name,'baseline',text,mode,seconds=20)
        new,b=runner.execute(name,'selective',text,mode,seconds=20)
        assert a==b,(name,mode)
        counts=[]
        if mode==1:
          leading=parse_leading(b,n,3);x=monomial_dimension(leading,n)[0];y=count_standard_monomials(leading,n,standard_basis_complete=True)
          assert x==y==expected,(name,x,y,expected);counts=[str(x),str(y)]
        results.append(dict(fixture=name,variables=n,mode=mode,status='COMPLETE',expected_dimension=str(expected),counts=counts,exports_byte_identical=True,runs=[old,new]))
        print(name,mode,'PASS',flush=True)
    (R/'validation.json').write_text(json.dumps(dict(status='PASS',complete_basis_comparisons=len(results),full_board_solver_runs=0,results=results),indent=2)+'\n')
    print('PASS',len(results),'paired comparisons')
if __name__=='__main__':main()
