#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

//#define IO

#ifdef IO
#include <iostream>
#include <bitset>
#endif

int main(int argc, char *argv[])
{
  sc_uint<3> a(6), d(5);
  sc_uint<1> b, c;

  b = (sc_uint<1>)a.range(2,2);
  c = (sc_uint_base)a.range(0,0);
  a.range(0,0) = b;
  a.range(1,1) = c;

#ifdef IO
  std::cout << "a: " << a.to_uint() << std::endl;
  std::cout << "b: " << b.to_uint() << std::endl;
  std::cout << "c: " << c.to_uint() << std::endl;
  std::cout << "d: " << d.to_uint() << std::endl;
#endif

  assert(a == d);

  return 0;
}

