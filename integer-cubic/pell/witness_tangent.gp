\\ Run with gp -q -f witness_tangent.gp.
default(factor_proven,1);

collect(n) = {
  my(t=n^4, answer=Set([]), s, a, m, y, x, z);
  \\ From n² | z and x³ = 2 modulo n², n cannot contain 2 or 3,
  \\ and 2 must be a cube modulo every other prime factor.
  my(f=factor(n));
  for(i=1,matsize(f)[1],
    my(p=f[i,1]);
    if(p<=3 || (p%3==1 && Mod(2,p)^((p-1)/3)!=1), return(answer)));
  fordiv(4*(n^24+540*n^12-108), d,
    forstep(e=-1,1,2,
      my(h=e*d, c=(4*t^2-h)/3);
      if(denominator(c)==1 && issquare(c,&s),
        forstep(u=-1,1,2,
          a=t+u*s; m=4*(2-a^3)/h;
          if(denominator(m)==1,
            y=(2*m-t-3*a)/(2*n);
            if(denominator(y)==1,
              x=a-m; z=n^2*m;
              if(x^3+z^2+y^2*z!=2, error("unexpected point"));
              answer=setunion(answer,Set([[x,y,z]]))))))));
  return(answer)
}
{for(n=1,250, my(p=collect(n)); if(#p,print(n," ",p)))}
quit
