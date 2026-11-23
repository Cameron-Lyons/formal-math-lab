#!/usr/bin/env python3
"""Independent graph-component audit of a failed closure-state coarsening.

The recorded witness was discovered with union-find on flattened indices.
This checker constructs T placements geometrically and uses graph traversal.
It does not compute the unrestricted board count.
"""
from collections import Counter
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent


def main():
    data=json.loads((ROOT/'exact_partition_coarsening.json').read_text())
    cells=[(j-r,-r) for r in range(10) for j in range(2*r+1)]
    universe=set(cells)
    windows=[]
    for x,y in cells:
        window=((x,y+1),(x-1,y),(x,y),(x+1,y))
        if set(window)<=universe:
            windows.append(window)
    assert len(windows)==81
    selected=[p['index'] for p in data['selected_placements']]
    union={p for i in selected for p in windows[i]}
    assert len(selected)==17 and len(union)==68
    assert [i for i,w in enumerate(windows) if set(w)<=union]==selected

    def components(events):
        neighbors={p:set() for p in cells}
        for first,second in events:
            for a,b in zip(windows[first],windows[second]):
                neighbors[a].add(b)
                neighbors[b].add(a)
        unseen=set(cells)
        sizes=[]
        while unseen:
            start=unseen.pop()
            component={start}; pending=[start]
            while pending:
                p=pending.pop()
                new=neighbors[p]-component
                component.update(new)
                pending.extend(new)
            unseen-=component
            sizes.append(len(component))
        return Counter(sizes)

    extra=data['future_collision']['indices']
    assert any(i not in selected for i in extra)
    after=[]
    for case in data['examples']:
        event=case['initial_collision']
        assert all(i in selected for i in event)
        before=components([event])
        assert before==Counter({1:92,2:4})
        assert sum(before.values())==data['initial_cell_class_count']==96
        sizes=components([event,extra])
        count=sum(sizes.values())
        assert count==case['cell_classes_after_future_collision']
        after.append(count)
    assert after==[93,92]
    print(json.dumps({'result':'PASS','independent_geometric_windows':len(windows),
                      'induced_disjoint_T_placements':len(selected),
                      'equal_initial_component_shapes':{'singletons':92,'pairs':4},
                      'different_class_counts_after_same_external_collision':after,
                      'unrestricted_exact_count':None}))


if __name__=='__main__':
    main()
