\\ Run with gp -q secant_orbit.gp. All thueinit calls request unconditional certification.
default(parisizemax, "2G");
normpoint(p) = [p[1], abs(p[2]), max(p[3], -p[2]^2-p[3])];
accepted(p) = normpoint(p)==[0,1,1] || normpoint(p)==[-7,8,5];
cubic(p) = p[1]^3+p[2]^2*p[3]+p[3]^2;
lead3(d) = d[1]^3+d[2]^2*d[3];
lead2(p,d) = 3*p[1]*d[1]^2 + p[3]*d[2]^2 + 2*p[2]*d[2]*d[3] + d[3]^2;
lead1(p,d) = 3*p[1]^2*d[1] + 2*p[2]*p[3]*d[2] + (p[2]^2+2*p[3])*d[3];

\\ For a homogeneous pair f,g, work in both affine charts. At each prime
\\ power dividing both values, at least one of m,n is invertible.
rev(f, d) = Polrev(vector(d+1, k, polcoef(f,d-k+1)), x);
divisorbound(f, d, g, e) = {
  my(r1=polresultant(f,g), r2=polresultant(rev(f,d),rev(g,e)));
  if(!r1 || !r2, error("common projective root"));
  lcm(abs(r1), abs(r2))
};
homvalue(f,d,m,n) = sum(i=0,d,polcoef(f,i)*m^i*n^(d-i));
\\ Evaluate a compact product at the three roots of a split prime.
\\ An unusable compact factor makes us skip the prime.
splitvalues(bnf,factors,roots,q) = {
  my(z=vector(3,k,Mod(1,q)));
  for(i=1,matsize(factors)[1],
    my(p=lift(nfbasistoalg(bnf,factors[i,1])));
    if(denominator(content(p))%q==0,return(0));
    for(k=1,3,
      my(v=Mod(1,q)*subst(p,x,roots[k]));
      if(v==0,return(0));
      z[k]*=v^factors[i,2]
    )
  ); z
};

\\ If F(m,n)=d then a*m-theta*n has norm a^2*d. Work in a reduced
\\ defining polynomial and keep theta as an explicit element of that field.
cubicsieve(f) = {
  my(a=pollead(f),red=polredbest(a^2*subst(f,x,x/a),1));
  my(T=red[1],theta=lift(red[2]),bnf=bnfinit(T,1),primes=List());
  if(bnfcertify(bnf)!=1 || bnf.sign!=[1,1] || bnf.tu[1]!=2,
    error("expected a certified rank-one cubic field with torsion {1,-1}"));
  my(unit=bnfunits(bnf)[1][1]);
  forprime(q=5,2000,
    if(a%q==0 || denominator(content(theta))%q==0,next);
    my(roots=polrootsmod(T,q)); if(#roots!=3,next);
    my(y=vector(3,k,subst(theta,x,roots[k]))); if(#Set(y)!=3,next);
    my(v=splitvalues(bnf,unit,roots,q)); if(type(v)!="t_VEC",next);
    listput(primes,[q,roots,[y[2]-y[3],y[3]-y[1],y[1]-y[2]],v])
  );
  [bnf,Vec(primes),a]
};

\\ Every member of the unit orbit of beta is +/-beta*u^k. If it is
\\ in span(1,theta), then its three reductions are collinear with the
\\ reductions of 1 and theta at every usable split prime.
excludeunit(data,beta) = {
  my(bnf=data[1],primes=data[2]);
  for(i=1,#primes,
    my(q=primes[i][1],z=splitvalues(bnf,beta,primes[i][2],q));
    if(type(z)!="t_VEC",next);
    my(h=primes[i][3],v=primes[i][4],s=h[1]*z[1],t=h[2]*z[2],w=h[3]*z[3]);
    my(g=v[1]/v[3],j=v[2]/v[3],ok=0);
    for(k=0,q-2, if(s+t+w==0,ok=1;break); s*=g; t*=j);
    if(!ok,return(1))
  ); 0
};

allcases(f,d,g,e,visit,usesieve=0) = {
  my(R=divisorbound(f,d,g,e),fac=factor(R));
  for(k=1,matsize(fac)[1],if(!isprime(fac[k,1]),error("unproven factor")));
  if(poldegree(f)!=d || !polisirreducible(f),error("unexpected denominator form"));
  my(data=if(usesieve,cubicsieve(f),thueinit(f,1)), ds=divisors(fac), count=0);
  my(ncases=0,norbits=0);
  my(possible=vector(9));
  for(m=0,8,for(n=0,8,if(m%3 || n%3,
    my(val=homvalue(f,d,m,n)%9,der=homvalue(g,e,m,n));
    if(der%gcd(val,9)==0,possible[1+val]=1)
  )));
  for(i=1,#ds,forstep(s=if(d%2,1,-1),1,2,
    my(value=s*ds[i]);if(!possible[1+value%9],next);
    if(usesieve,
      ncases++;
      my(reps=bnfisintnorm(data[1],data[3]^2*value,1));
      for(j=1,#reps,
        if(!excludeunit(data,reps[j]),error("unit sieve inconclusive at ",value));
        norbits++
      ); next
    );
    my(solutions=thue(data,value));
    for(j=1,#solutions,
      my(m=solutions[j][1],n=solutions[j][2]);
      if((d%2 || n>0 || (n==0 && m>0)) && gcd(m,n)==1, count+=visit(m,n,value))
    )
  ));
  if(usesieve,print("  excluded ",norbits," norm representatives for ",ncases," right-hand sides"));
  count
};

visitboundary(p,m,n,value) = {
    if(!m || !n,return(0));
    my(d=[-n^2*m,n^3,m^3],v=lead1(p,d));
    if(lead2(p,d)!=value || lead3(d)!=0,error("boundary restriction mismatch"));
    if(!v || v%value,return(0));
    my(q=p-(v/value)*d);
    if(cubic(q)!=2 || !accepted(q),error("new point ",q));
    print("  chord ",p," -> ",q); 1
};

infinitysecants(p) = {
  my(px=p[1],py=p[2],pz=p[3]);
  my(f=x^6+2*py*x^3+3*px*x^2+pz, g=(py^2+2*pz)*x^3-3*px^2*x+2*py*pz);
  my(visit=(m,n,value)->visitboundary(p,m,n,value));
  allcases(f,6,g,3,visit)
};

visittangent(p,v,w,m,n,value) = {
    my(d=m*v+n*w, coef=lead2(p,d));
    if(lead3(d)!=value || lead1(p,d)!=0,error("tangent restriction mismatch"));
    if(!coef || coef%value,return(0));
    my(q=p-(coef/value)*d);
    if(cubic(q)!=2 || !accepted(q),error("new point ",q));
    print("  tangent ",p," -> ",q); 1
};

affinetangents(p,change,usesieve=0) = {
  my(a=3*p[1]^2,b=2*p[2]*p[3],c=p[2]^2+2*p[3],h=gcd([a,b,c]));
  a/=h;b/=h;c/=h;
  my(uv=bezout(a,b),e=[b/uv[3],-a/uv[3],0],k=[-c*uv[1],-c*uv[2],uv[3]]);
  if(abs(matdet(change))!=1,error("non-unimodular parameter change"));
  my(v=e*change[1,1]+k*change[2,1],w=e*change[1,2]+k*change[2,2]);
  my(direction=x*v+w, f=lead3(direction), g=lead2(p,direction));
  my(visit=(m,n,value)->visittangent(p,v,w,m,n,value));
  allcases(f,3,g,2,visit,usesieve)
};

finitechords() = {
  my(S=[[0,1,1],[0,1,-2],[-7,8,5],[-7,8,-69]]);
  S=concat(S,vector(#S,i,[S[i][1],-S[i][2],S[i][3]]));
  for(i=1,#S,for(j=i+1,#S,
    my(p=S[i],v=S[j]-p,h=gcd(v),d=v/h,f=lead3(d));
    if(!f,
      if(!lead2(p,d) && !lead1(p,d),error("line on surface")),
      my(t=lead1(p,d)/(h*f));
      if(denominator(t)==1 && (cubic(p+t*d)!=2 || !accepted(p+t*d)),error("new chord ",p+t*d))
    )
  ));
  print("All 28 pairs of distinct finite points checked.")
};

run() = {
  my(points=[[0,1,1],[0,1,-2],[-7,8,5],[-7,8,-69]]);
  my(changes=[matid(2),matid(2),[-137,34;4,-1],[-3,-1;1,0]]);
  for(i=1,#points,
    my(p=points[i]);
    if(i>1, my(c=infinitysecants(p)); print(p," non-axis boundary chords: ",c));
    my(c=affinetangents(p,changes[i],i==4)); print(p," nontrivial tangent intersections: ",c);
  );
  finitechords();
};
iferr(run(),E,print(E);quit(1));
