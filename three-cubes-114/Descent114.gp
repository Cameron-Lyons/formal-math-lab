\\ Run with PARI/GP 2.19.1: gp -fq Descent114.gp
\\ For each signed a, a solution with x+y=a gives an affine rational point
\\ on this curve. Rank upper bound 0 and torsion order 1 leave only infinity.
\\ This descent uses PARI. The associated integer identity is in Descent114.lean.
default(parisizemax, 512000000);
pair_sums = [-20246,-20381,-20438,-20639,-20789,-20822,-20939,-21110,-21689,-21767,-21839,-22094,-22214,-22742,-22814,-22877,-23189,-23222,-23246,-23318,-23339,-23603,-23990,-315859094,10208993386,4053332798386];
{
  for(i=1,#pair_sums,
    my(a=pair_sums[i], E=ellinit([0,432*a^3*(456-a^3)]));
    my(r=ellrank(E), t=elltors(E));
    if(r[2] != 0 || t[1] != 1, error("inconclusive descent for a=",a));
    print(a, ": rank upper bound ", r[2], ", torsion order ", t[1]);
  );
}
