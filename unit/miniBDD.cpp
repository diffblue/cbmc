/*******************************************************************\

Module: A minimalistic BDD library, following Bryant's original paper
        and Andersen's lecture notes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <solvers/miniBDD/miniBDD.h>

void test1()
{
  mini_bdd_mgrt mgr;

  mini_bddt x=mgr.Var("x");
  mini_bddt y=mgr.Var("y");
  mini_bddt z=mgr.Var("z");
  mini_bddt f=(x&y&z)|(!x&!y&z);
  y.clear();
  x.clear();
  z.clear();

  //mgr.DumpDot(std::cout);
  mgr.DumpTikZ(std::cout);
}

void test2()
{
  mini_bdd_mgrt mgr;

  mini_bddt a=mgr.Var("a");
  mini_bddt b=mgr.Var("b");
  mini_bddt c=mgr.Var("c");
  mini_bddt d=mgr.Var("d");

  mini_bddt final=(a == b) & (c == d);

  a.clear();
  b.clear();
  c.clear();
  d.clear();

  mgr.DumpTikZ(std::cout, true);
}

void test3()
{
  mini_bdd_mgrt mgr;

  mini_bddt final=mgr.Var("x") & mgr.Var("y");

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
