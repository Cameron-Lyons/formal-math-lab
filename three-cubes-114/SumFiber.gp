\\ Run with PARI/GP: gp -fq SumFiber.gp
\\ Exhaust every integer triple with a prescribed total h=x+y+z, up to permutation.
\\ A triple has pair sums a,b,c with sum 2h and product t=(h^3-k)/3. At least
\\ one has absolute value at most |t|^(1/3). For either sign of each possible
\\ smallest divisor c, recover a,b from their sum 2h-c and product t/c.
default(factor_proven,1);
default(parisizemax,256000000);

sum_fiber(k,h) = {
  if((h^3-k)%3, return([]));
  my(t=(h^3-k)/3, hits=[]);
  if(!t, error("the zero-product fiber requires separate treatment"));
  my(F=factor(abs(t)), ds=divisors(F));
  for(i=1,#ds,
    my(d=ds[i]); if(d^3>abs(t),break);
    forstep(s=-1,1,2,
      my(c=s*d, u=2*h-c, D=u^2-4*t/c, w);
      if(D<0 || !issquare(D,&w) || (u-w)%2,next);
      my(a=(u-w)/2,b=(u+w)/2,xyz=vecsort([h-a,h-b,h-c]));
      if(vecsum(xyz)!=h || sum(j=1,3,xyz[j]^3)!=k,error("incorrect recovery"));
      hits=setunion(hits,[xyz]);
    );
  );
  hits;
}

{
  my(known=vecsort([-80538738812075974,80435758145817515,12602123297335631]));
  if(!setsearch(sum_fiber(42,vecsum(known)),known),error("42 control failed"));
  if(sum_fiber(3,3)!=[[-5,4,4],[1,1,1]], error("3 control failed"));
  print("Recovered the known 42 triple and both triples in the k=h=3 fiber.");
}

\\ Enumerating residues lets the interval check include every integer h.
sum_residues(k,m) = {
  my(ok=vector(m));
  for(x=0,m-1,for(y=0,m-1,for(z=0,m-1,
    if((x^3+y^3+z^3-k)%m==0,ok[1+(x+y+z)%m]=1))));
  ok;
}

search_window(start, count) = {
  my(hits=0,nfact=0,ms=[2,27,5,7],ok=vector(#ms,i,sum_residues(114,ms[i])));
  for(i=0,count-1,forstep(s=-1,1,2,
    my(h=s*(start+i));
    if(!prod(j=1,#ms,ok[j][1+h%ms[j]]),next);
    my(sol=sum_fiber(114,h)); nfact++;
    if(#sol,print("h=",h," ",sol); hits+=#sol);
  ));
  print("Checked ",2*count," signed sums with ",start," <= |h| < ",start+count,
        "; factored ",nfact," fibers; triples: ",hits);
}
search_window(10^21,1024);
