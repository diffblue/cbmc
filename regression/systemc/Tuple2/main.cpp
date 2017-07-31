#include <cassert>
#include "tuple.h"

#ifndef NO_STRING
#include <string>
#endif

int main(int argc, char** argv)
{
  tuple<int,int> p;
  int x=0, y=0;

  p = tuple<int,int>(1,2);

#ifndef NO_IO
  std::cout << p << std::endl;
#endif

  p = tuple<int,int>(3,4);

#ifndef NO_IO
  std::cout << p << std::endl;

  std::cout << x << "," << y << std::endl;
#endif
  assert(x==0);
  assert(y==0);

  tie(x,y) = p;

#ifndef NO_IO
  std::cout << x << "," << y << std::endl;
#endif
  assert(x==3);
  assert(y==4);

  p = tuple<int,int>(5,6);

#ifndef NO_IO
  std::cout << p << std::endl;

  std::cout << x << "," << y << std::endl;
#endif
  assert(x==3);
  assert(y==4);

  x = 42; y = 69;

#ifndef NO_IO
  std::cout << p << std::endl;

  std::cout << x << "," << y << std::endl;
#endif
  assert(x==42);
  assert(y==69);

  tuple<bool,bool> q;
  q = tuple<bool,bool>(true,false);

#ifndef NO_IO
  std::cout << q << std::endl;
#endif

  bool foo, bar;

  tie(foo,bar) = q;

#ifndef NO_IO
  std::cout << foo << " " << bar << std::endl;
#endif
  assert(foo);
  assert(!bar);

  tuple<int> one;
  one = 69;

#ifndef NO_IO
  std::cout << one << std::endl;
#endif

  tie(x) = one;

#ifndef NO_IO
  std::cout << x << std::endl;
#endif
  assert(x==69);

#ifndef NO_STRING
  tuple<int,std::string,int> three;
  three =   tuple<int,std::string,int>(42," does not equal ",69);

#ifndef NO_IO
  std::cout << three << std::endl;
#endif

  tuple<std::string,int,std::string,int> four;
  four =   tuple<std::string,int,std::string,int>("and ", 42," is less than ",69);

#ifndef NO_IO
  std::cout << four << std::endl;
#endif

  tuple<std::string,std::string> msg;
  msg = tuple<std::string,std::string>("hello","world");

#ifndef NO_IO
  std::cout << msg << std::endl;
#endif

  std::string xx,yy;
  tie(xx,yy) = tuple<std::string,std::string>("hello","world");

#ifndef NO_IO
  std::cout << xx << " " << yy << std::endl;
#endif
  assert(xx=="hello");
  assert(yy=="world");
#endif

}
