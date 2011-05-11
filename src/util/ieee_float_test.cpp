#include <stdlib.h>
#include <time.h>
#include <limits>
#include <float.h>
#include <math.h>

#ifdef _WIN32
#define random() rand()
#define nextafterf(a, b) throw "no nextafterf";
#endif

#include "ieee_float.h"

#define PINF (std::numeric_limits<float>::infinity())
#define NINF (-std::numeric_limits<float>::infinity())
#define NZERO (-0.0f)
#define PZERO (0.0f)

#ifndef NAN
#  define NAN (std::numeric_limits<float>::quiet_NaN())
#endif


float random_float()
{
  union
  {
    float f;
    unsigned i;
  } u;


  unsigned r = ((unsigned) random()) % 20;

  switch(r)
  {
    case 0:
      return PINF;
      break;
    case 1:
      return NINF;
      break;
    case 2:
      return NAN;
      break;
    case 3:
      return PZERO;
      break;
    case 4:
      return NZERO;
      break;
    default: 
      u.i=random();
      u.i=(u.i<<16)^random();
      return u.f;
  }

}

bool eq(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.is_NaN() && b.is_NaN()) return true;
  if(a.is_infinity() && b.is_infinity() && a.get_sign()==b.get_sign()) return true;
  return a==b;
}

typedef enum { PLUS=0, MINUS=1, MULT=2, DIV=3 } binopt;
typedef enum { EQ=0, NEQ=1, LT=2, LE=3, GT=4, GE=5} binrel;
const char *binopsyms[]={ " + ", " - ", " * ", " / " };
const char *binrelsyms[]={ " == ", " != ", " < ", " <= ", " > ", " >= "};

void check_arithmetic(int i)
{
  ieee_floatt i1, i2, i3, res;
  float f1, f2, f3;

  f1=random_float();
  f2=random_float();
  i1.from_float(f1);
  i2.from_float(f2);
  res=i1;
  f3=f1;

  int op=(binopt)i%4;

  switch(op)
  {
    case PLUS:
      f3+=f2;
      res+=i2;
      break;

    case MINUS:
      f3-=f2;
      res-=i2;
      break;

    case MULT:
      f3*=f2;
      res*=i2;
      break;

    case DIV:
      f3/=f2;
      res/=i2;
      break;

    default:assert(0);
  }

  i3.from_float(f3);

  if(!eq(res, i3))
  {
    const char *opsym=binopsyms[op];
    std::cout << i1 << opsym << i2 << " != " << res << std::endl;
    std::cout << f1 << opsym << f2 << " == " << f3 << std::endl;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " != " <<
      integer2binary(res.get_fraction(), i1.spec.f+1) <<
      " (" << res.get_fraction() << ")" << std::endl;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " == " <<
      integer2binary(i3.get_fraction(), i1.spec.f+1) <<
      " (" << i3.get_fraction() << ")" << std::endl;
    std::cout << std::endl;
  }
}

void check_comparison(int i)
{
  ieee_floatt i1, i2;
  float f1, f2;

  bool ires, fres;

  f1=random_float();
  f2=random_float();
  i1.from_float(f1);
  i2.from_float(f2);

  int op=(binrel)i%6;
 
  switch(op) 
  {
    case EQ:
      ires = ieee_equal(i1,i2);
      fres = (f1 == f2);
      break;
    case NEQ:
      ires = ieee_not_equal(i1,i2);
      fres = (f1 != f2);
      break;
    case LT:
      ires = (i1 < i2);
      fres = (f1 < f2);
      break;
    case LE:
      ires = (i1 <= i2);
      fres = (f1 <= f2);
      break;
    case GT:
      ires = (i1 > i2);
      fres = (f1 > f2);
      break;
    case GE:
      ires = (i1 >= i2);
      fres = (f1 >= f2);
      break;
    default:
      assert(0);
  }

  if(ires != fres)
  {
    const char *opsym=binrelsyms[op];
    std::cout << i1 << opsym << i2 << " != " << ires << std::endl;
    std::cout << f1 << opsym << f2 << " == " << fres << std::endl;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " != " << ires;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " == " << fres;
    std::cout << std::endl;
  }

}

void check_conversion(int i)
{
  union 
  { 
    float f;
    unsigned i;
  } a, b;

  a.f = random_float();

  ieee_floatt t;
  t.from_float(a.f);

  assert(t.is_float());
  b.f = t.to_float();

  if(a.i != b.i && !((a.f != a.f) && (b.f != b.f)))
  {
    std::cout << "conversion failure: " << a.f << " -> " << t << " -> " 
              << b.f << std::endl;
  }
}

void check_nextafter(int i)
{
  float f1 = random_float();
  float f2 = nextafterf(f1, PINF);
  float f3 = nextafterf(f1, NINF);
  
  ieee_floatt i1, i2, i3;
  
  i1.from_float(f1);
  i2.from_float(f2);
  i3.from_float(f3);

  if((f1 != i1.to_float() && !(f1 != f1 && i1.is_NaN())) ||
     (f2 != i2.to_float() && !(f2 != f2 && i2.is_NaN())) ||
     (f3 != i3.to_float() && !(f3 != f3 && i3.is_NaN())))
  {
    std::cout << "Incorrect nextafter: " << std::endl 
              << "float: " << f1 << " " << f2 << " " << f3 << std::endl
              << "ieee_float: " << i1.to_float() << " " 
                  << i2.to_float() << " " << i3.to_float() << std::endl;
  }

}

void check_minmax()
{
  float f = 0;
  ieee_floatt t;
  t.from_float(f);

  t.make_fltmax();
  if(t.to_float() != FLT_MAX)
    std::cout << "make_fltmax is broken" << std::endl;

  t.make_fltmin();
  if(t.to_float() != FLT_MIN)
    std::cout << "make_fltmin is broken:"
             << std::endl << " machine float: " << FLT_MIN 
            << ", ieee_floatt: " << t.to_float() << "(" 
            << (t.to_float() == FLT_MIN) <<  ")" << std::endl;
}

int main()
{
  srand(time(0));
  check_minmax();

  for(unsigned i=0; i<100000000; i++)
  {
    if(i%100000==0) std::cout << "*********** " << i << std::endl;
    check_arithmetic(i);
    check_comparison(i);
    check_conversion(i);
    check_nextafter(i);
  }
}
