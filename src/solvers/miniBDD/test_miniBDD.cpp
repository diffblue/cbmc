#include <iostream>

#include "miniBDD.h"

using namespace miniBDD;

void test1()
{
  mgr mgr;

  BDD x=mgr.Var("x");
  BDD y=mgr.Var("y");
  BDD z=mgr.Var("z");
  BDD f=(x&y&z)|(!x&!y&z);
  y.clear();
  x.clear();
  z.clear();

  //mgr.DumpDot(std::cout);
  mgr.DumpTikZ(std::cout);
}

void test2()
{
  mgr mgr;
  
  BDD a=mgr.Var("a");
  BDD b=mgr.Var("b");
  BDD c=mgr.Var("c");
  BDD d=mgr.Var("d");
  
  BDD final=(a == b) & (c == d);  

  a.clear();
  b.clear();
  c.clear();
  d.clear();

  mgr.DumpTikZ(std::cout, true);
}

void test3()
{
  mgr mgr;
  
  BDD final=mgr.Var("x") & mgr.Var("y");

  mgr.DumpDot(std::cout);
  //mgr.DumpTikZ(std::cout);
  //mgr.DumpTable(std::cout);
}

int main()
{
  test3();
}
