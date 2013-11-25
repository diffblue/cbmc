#include <iostream>

#include <solvers/sat/satcheck.h>
#include "float_utils.h"

float random_float()
{
  unsigned u=random();
  u=(u<<16)^random();
  return *(float *)&u;
}

bool eq(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.is_NaN() && b.is_NaN()) return true;
  if(a.is_infinity() && b.is_infinity() &&
     a.get_sign()==b.get_sign()) return true;
  return a==b;
}

std::string to_str(const bvt &bv)
{
  std::string result;
  for(unsigned i=0; i<bv.size(); i++)
  {
    char ch;
    if(bv[i]==const_literal(true))
      ch='1';
    else if(bv[i]==const_literal(false))
      ch='0';
    else
      ch='?';
    result=ch+result;
  }
  return result;
}

typedef enum { PLUS=0, MINUS=1, MULT=2, DIV=3 } binopt;
const char *binopsyms[]={ " + ", " - ", " * ", " / " };

int main()
{
  ieee_floatt i1, i2, i3;
  bvt b1, b2, b3, res;
  float f1, f2, f3;

  for(unsigned i=0; i<200; i++)
  {
    if(i%20==0)
      std::cout << "*********** " << i << std::endl;

    satcheckt satcheck;
    float_utilst float_utils(satcheck);

    #if 0
    f1=random_float();
    f2=random_float();
    i1.from_float(f1);
    i2.from_float(f2);
    float_utils.spec=i1.spec;
    b1=float_utils.build_constant(i1);
    b2=float_utils.build_constant(i2);
    f3=f1;

    int op=(binopt)i%3;
    //op=PLUS;
    #else
    f1=-0.25;
    f2=-2.5;
    i1.from_float(f1);
    i2.from_float(f2);
    float_utils.spec=i1.spec;
    b1=float_utils.build_constant(i1);
    b2=float_utils.build_constant(i2);
    f3=f1;

    int op=DIV;
    #endif

    switch(op)
    {
    case PLUS:
      f3+=f2;
      res=float_utils.add(b1, b2);
      break;

    case MINUS:
      f3-=f2;
      res=float_utils.sub(b1, b2);
      break;

    case MULT:
      f3*=f2;
      res=float_utils.mul(b1, b2);
      break;

    case DIV:
      f3/=f2;
      res=float_utils.div(b1, b2);
      break;

    default:assert(0);
    }

    i3.from_float(f3);

    satcheckt::resultt result=satcheck.prop_solve();
    assert(result==satcheckt::P_SATISFIABLE);

    ieee_floatt fres;
    fres=float_utils.get(res);

    if(!eq(fres, i3))
    {
      const char *opsym=binopsyms[op];
      std::cout << i1 << opsym << i2 << " != " << fres << std::endl;
      std::cout << f1 << opsym << f2 << " == " << f3 << std::endl;
      std::cout << integer2binary(i1.get_exponent(), i1.spec.e) << " " <<
                   integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
                   integer2binary(i2.get_exponent(), i1.spec.e) << " " <<
                   integer2binary(i2.get_fraction(), i1.spec.f+1) << " != " <<
                   integer2binary(fres.get_exponent(), i1.spec.e) << " " <<
                   integer2binary(fres.get_fraction(), i1.spec.f+1) << std::endl;
      std::cout << integer2binary(i1.get_exponent(), i1.spec.e) << " " <<
                   integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
                   integer2binary(i2.get_exponent(), i1.spec.e) << " " <<
                   integer2binary(i2.get_fraction(), i1.spec.f+1) << " == " <<
                   integer2binary(i3.get_exponent(), i1.spec.e) << " " <<
                   integer2binary(i3.get_fraction(), i1.spec.f+1) << std::endl;
      std::cout << std::endl;
    }
  }
}
