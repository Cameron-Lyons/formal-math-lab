#!/usr/bin/env python3
"""Rigorous weighted-prefix rotor upper bounds; only tiny capped censuses.
Never enumerates ternary five-row caps or starts a full ternary solver.
"""
from pathlib import Path
from itertools import product,permutations
from math import factorial,gcd
from fractions import Fraction
from collections import Counter
import argparse,hashlib,json,resource,subprocess,sys
import exact_mobius_small as mobius

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'exact_rotor_upper_census.cpp'
BINARY=HERE/'exact_rotor_upper_census'
LIMIT=1024**3


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(LIMIT,)*2)
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
def mathematical_record(data):
    return {k:v for k,v in data.items() if k not in ('wall_seconds','cpu_seconds','peak_rss_kib')}


def weighted(data):
    q=data['colors'];h=data['height'];triple_count=q**3
    assert data['apex']==0 and data['cells']==h*h and data['placements']==(h-1)**2
    assert data['known_boundary_cells']==2*h-1
    total=0;caps=0;bins=[]
    for b in data['histogram']:
        counts=[b[f'n{i}'] for i in range(4)]
        assert sum(counts)==triple_count
        assert sum(i*c for i,c in enumerate(counts))==(h-1)**2
        assert all(c==0 for c in counts[q+1:])
        weight=1
        for k in range(q+1):weight*=factorial(q-k)**counts[k]
        contribution=b['caps']*weight;total+=contribution;caps+=b['caps']
        bins.append(dict(b,rotor_suffixes_per_cap=str(weight),weighted_contribution=str(contribution)))
    assert caps==data['caps']
    full_boundary=2*q*q+1;known_boundary=2*h-1;unfixed=full_boundary-known_boundary
    factor=q**(unfixed+1) # remaining boundary digits, then q possible apex colors
    upper=factor*total;old=q**full_boundary*factorial(q)**triple_count
    assert upper<=old
    ratio=Fraction(upper,old)
    return {'colors':q,'height':h,'apex_zero_caps':caps,
            'full_boundary_cells':full_boundary,'known_boundary_cells':known_boundary,
            'remaining_boundary_cells':unfixed,'apex_color_factor':q,
            'weighted_cap_sum':str(total),'boundary_and_apex_factor':str(factor),
            'upper_bound':str(upper),'original_rotor_bound':str(old),
            'ratio_to_original':[ratio.numerator,ratio.denominator],
            'histogram':bins}


def binary_rotor_prefix_counts():
    # Independent parameter enumeration: all2^9 boundary words and2^8 rotors.
    # No used-pattern DFS or histogram weights are used in this calculation.
    survives=[0]*6;accepted=set();attempted=0
    for boundary in product(range(2),repeat=9):
        for rotor_word in range(256):
            attempted+=1;survives[1]+=1
            rows=[[boundary[0]]];usage=[0]*8
            for r in range(1,5):
                row=[boundary[2*r-1],boundary[2*r]];failed=False
                for j in range(2*r-1):
                    g=4*rows[-1][j]+2*row[j]+row[j+1]
                    if usage[g]==2:failed=True;break
                    row.append(((rotor_word>>g)&1)^usage[g]);usage[g]+=1
                if failed:break
                rows.append(row);survives[r+1]+=1
            if len(rows)==5:
                flat=tuple(c for row in rows for c in row)
                assert flat not in accepted;accepted.add(flat)
                assert usage==[2]*8
                # Cartesian geometry is separate from the C++ top-index table.
                cells={(j-r,-r):c for r,row in enumerate(rows) for j,c in enumerate(row)}
                patterns=[]
                for x,y in cells:
                    coords=((x,y+1),(x-1,y),(x,y),(x+1,y))
                    if all(p in cells for p in coords):patterns.append(tuple(cells[p] for p in coords))
                assert set(patterns)==set(product(range(2),repeat=4)) and len(patterns)==16
                recovered_boundary=[rows[0][0]];outputs=[[] for _ in range(8)]
                for r in range(1,5):
                    recovered_boundary.extend(rows[r][:2])
                    for j in range(2*r-1):
                        g=4*rows[r-1][j]+2*rows[r][j]+rows[r][j+1]
                        outputs[g].append(rows[r][j+2])
                assert tuple(recovered_boundary)==boundary
                assert all(v==[(rotor_word>>g)&1,1-((rotor_word>>g)&1)] for g,v in enumerate(outputs))
    assert attempted==131072 and len(accepted)==survives[5]==168
    return {'parameter_tuples':attempted,'surviving_inputs_by_height':{h:survives[h] for h in range(1,6)},
            'exact_full_binary_boards':len(accepted),'accepted_board_geometry_and_tuple_roundtrips_checked':True}


def ternary_lazy_rotor_sum(height):
    assert 1<=height<=3
    q=3;rotors=list(permutations(range(q)));windows=[((r-1)**2+j,r*r+j,r*r+j+1,r*r+j+2)
                                                   for r in range(1,height) for j in range(2*r-1)]
    boundary=[0]+[r*r+j for r in range(1,height) for j in (0,1)]
    used=[0]*27;assigned=[None]*27;cells=[0]*(height*height)
    total=0;leaves=0;failures=0
    def visit(index,assigned_count):
        nonlocal total,leaves,failures
        if index==len(windows):total+=6**(27-assigned_count);leaves+=1;return
        t,l,m,r=windows[index];g=9*cells[t]+3*cells[l]+cells[m];k=used[g]
        if k==3:failures+=1;return
        if assigned[g] is None:
            assert k==0
            for rotor in rotors:
                assigned[g]=rotor;used[g]=1;cells[r]=rotor[0]
                visit(index+1,assigned_count+1)
            used[g]=0;assigned[g]=None
        else:
            cells[r]=assigned[g][k];used[g]=k+1
            visit(index+1,assigned_count)
            used[g]=k
    for values in product(range(3),repeat=len(boundary)-1):
        for cell,color in zip(boundary[1:],values):cells[cell]=color
        visit(0,0)
    return {'height':height,'known_apex_zero_boundary_words':3**(2*height-2),
            'complete_lazy_rotor_leaves':leaves,'capacity_failure_nodes':failures,
            'weighted_sum_of_full27_rotor_assignments':str(total)}


def build(check=False):
    # The driver and every child have an explicit1GiB address-space ceiling.
    limits()
    command=['c++','-O3','-std=c++23','-Wall','-Wextra','-Wpedantic','-Werror',str(SOURCE),'-o',str(BINARY)]
    if not BINARY.exists():subprocess.run(command,check=True,timeout=30)
    source_hash=sha(SOURCE);binary_hash=sha(BINARY)
    if check:
        old=json.loads((HERE/'exact_rotor_upper_results.json').read_text())
        assert old['census_source_sha256']==source_hash and old['census_executable_sha256']==binary_hash
    records=[];raw_files=[]
    for q,max_height in ((2,5),(3,4)):
        previous=None
        for h in range(1,max_height+1):
            run=subprocess.run([str(BINARY),str(q),str(h)],capture_output=True,text=True,
                               check=True,timeout=30,preexec_fn=limits)
            data=json.loads(run.stdout)
            path=(HERE/'exact_rotor_upper_ternary4_census.json') if (q,h)==(3,4) else HERE/f'exact_rotor_upper_q{q}_h{h}.json'
            if path.exists():assert mathematical_record(json.loads(path.read_text()))==mathematical_record(data)
            else:
                assert not check;path.write_text(run.stdout)
            assert data['peak_rss_kib']<=LIMIT//1024
            record=weighted(data)
            assert previous is None or int(record['upper_bound'])<=previous
            previous=int(record['upper_bound']);record['raw_census_file']=path.name
            records.append(record);raw_files.append(path)
    by_key={(r['colors'],r['height']):r for r in records}
    assert by_key[3,4]['apex_zero_caps']==9391598
    assert by_key[2,5]['upper_bound']=='168' and by_key[2,5]['apex_zero_caps']==84
    # Recompute all small cap counts by independent placement-partition Mobius
    # inversion; h4 visits21147 partitions, not ternary colorings.
    independent=[]
    for h in range(1,5):
        data,_,_=mobius.compute(h)
        for q in (2,3):
            expected=mobius.evaluate(data['coefficients'],q)
            assert expected==q*by_key[q,h]['apex_zero_caps']
        independent.append({'height':h,'placement_partitions':data['placement_partitions'],
                            'polynomial_coefficients':data['coefficients'],
                            'binary_labeled_caps':mobius.evaluate(data['coefficients'],2),
                            'ternary_labeled_caps':mobius.evaluate(data['coefficients'],3)})
    binary=binary_rotor_prefix_counts()
    for h,count in binary['surviving_inputs_by_height'].items():assert int(by_key[2,h]['upper_bound'])==count
    ternary=[]
    for h in range(1,4):
        test=ternary_lazy_rotor_sum(h);assert test['weighted_sum_of_full27_rotor_assignments']==by_key[3,h]['weighted_cap_sum']
        ternary.append(test)
    final=by_key[3,4];upper=int(final['upper_bound']);old=int(final['original_rotor_bound'])
    assert old==1189563417824350846613100429312
    assert upper==1185818059470602086065654202368
    improvement=Fraction(old-upper,old)
    # Existing five-row cap count is full-label, not apex-zero. This is a
    # throughput extrapolation for planning only; no five-row job is launched.
    old_census=json.loads((HERE/'exact_algo_census_results.json').read_text())
    assert old_census['status']=='COMPLETE' and old_census['count_completed_orbits']==198649032096
    apex0_five=old_census['count_completed_orbits']//3
    observed=json.loads((HERE/'exact_rotor_upper_ternary4_census.json').read_text())
    estimated=apex0_five*observed['cpu_seconds']/observed['caps']
    result={
      'status':'PASS','claim':'rigorous unrestricted ternary upper bound, not the exact count and not a lower bound',
      'upper_bound':str(upper),'previous_documented_rotor_upper_bound':str(old),
      'improvement_integer':str(old-upper),'new_to_old_ratio':final['ratio_to_original'],
      'relative_decrease':[improvement.numerator,improvement.denominator],
      'relative_decrease_percent_approximate':float(100*improvement),
      'formula':'U4=3^13*sum_apex0_four_row_caps(6^n0*2^n1)',
      'weighted_apex0_four_row_cap_sum':final['weighted_cap_sum'],
      'full_boundary_cells':19,'known_boundary_cells':7,'unknown_boundary_cells':12,
      'apex_color_factor':3,'fiber_proof':'For every cap, the compatible full boundary/rotor parameter tuples number exactly3^12*product_g(3-k_g)!; complete valid boards inject into this cap fiber.',
      'four_row_cap_count_apex0':9391598,'four_row_cap_count_labeled':28174794,
      'cap_censuses_and_bounds':records,
      'independent_mobius_cap_count_checks':independent,
      'independent_binary_all_parameter_check':binary,
      'independent_ternary_tiny_lazy_rotor_checks':ternary,
      'source_geometry':'one apex plus first two cells in each later row are boundary; right outputs decoded row-major from(T,L,M)',
      'census_source_sha256':source_hash,'census_executable_sha256':binary_hash,
      'compile_command':command,'raw_census_sha256':{p.name:sha(p) for p in raw_files},
      'python_checker_sha256':sha(Path(__file__)),
      'independent_mobius_source_sha256':sha(HERE/'exact_mobius_small.py'),
      'address_space_limit_bytes':LIMIT,'native_census_workers':1,
      'five_row_scope_estimate':{'existing_full_label_caps':198649032096,'apex0_caps':apex0_five,
        'estimated_seconds_at_four_row_leaf_throughput':estimated,
        'estimate_is_not_a_run_or_guarantee':True,'five_row_run_started':False,
        'reflection_caveat':'Right-output rotor weight is not generally reflection-invariant; prefix orbit weighting requires both right and left weights, or a new proof.'},
      'unrestricted_exact_count_status':'UNKNOWN','lower_bound_change':None,
    }
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    result=build(args.check);path=HERE/'exact_rotor_upper_results.json'
    if args.check:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    else:path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','upper_bound','previous_documented_rotor_upper_bound',
          'new_to_old_ratio','relative_decrease_percent_approximate','independent_binary_all_parameter_check',
          'independent_ternary_tiny_lazy_rotor_checks','five_row_scope_estimate')},indent=2))
if __name__=='__main__':main()
