\\ Run with gp -fq cubic/ellipticGroups.gp (PARI 2.19).
\\ For full saturation, feed the four minimal models below to mwrank -S -1.
ratios = [2,5/2,5,10];
expected = [[0,-1,0,-65,261],[0,1,0,-1633,32963],[0,-1,0,-408,6912],[0,1,0,-1633,97763]];
bases = [[[5,-6],[-7,18],[-4,21]],[[23,-90],[-37,210],[-31,234]],[[-24,48],[12,-60],[-18,90]],[[-58,27],[23,-270],[-37,330]]];
conductors = [71688,9544200,3224400,20041800];
{
  for(i=1,#ratios,
    u=numerator(ratios[i]); v=denominator(ratios[i]);
    E=ellinit([0,-8*u*v,0,5*u^2*v^2,9*u^4*v^2+9*u^2*v^4+32*u^3*v^3]);
    M=ellminimalmodel(E,&change);
    coeff=vector(5,j,M[j]);
    if(coeff!=expected[i] || ellglobalred(M)[1]!=conductors[i],error("model mismatch"));
    if(elltors(M)[1]!=1 || ellrank(M)[1..2]!=[3,3],error("group mismatch"));
    if(!vecprod(vector(3,j,ellisoncurve(M,bases[i][j]))),error("generator mismatch"));
    print("ratio ",ratios[i],", model ",coeff,", conductor ",conductors[i],", basis ",bases[i],", x(original) = x(minimal) + ",change[2]);
  );
}
