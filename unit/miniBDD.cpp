#include <iostream>

#include <solvers/miniBDD/miniBDD.h>

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

#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#include <solvers/prop/bdd_expr.h>

void test4()
{
  register_language(new_ansi_c_language);

  symbol_exprt a("a", bool_typet());
  symbol_exprt b("b", bool_typet());

  or_exprt o(and_exprt(a, b), not_exprt(a));

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  std::cout << from_expr(ns, "", o) << std::endl;

  bdd_exprt t(ns);
  t.from_expr(o);

  std::cout << from_expr(ns, "", t.as_expr()) << std::endl;
}

int main()
{
  test3();
}
