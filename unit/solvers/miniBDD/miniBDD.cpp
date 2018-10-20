/*******************************************************************\

 Module: Unit tests for miniBDD

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for miniBDD

#include <testing-utils/catch.hpp>

#include <solvers/flattening/boolbv.h>
#include <solvers/miniBDD/miniBDD.h>
#include <solvers/prop/bdd_expr.h>

#include <util/arith_tools.h>
#include <util/expanding_vector.h>
#include <util/format_expr.h>
#include <util/symbol_table.h>

class bdd_propt:public propt
{
public:
  mini_bdd_mgrt &mgr;

  explicit bdd_propt(mini_bdd_mgrt &_mgr):mgr(_mgr)
  {
    // True and False
    bdd_map.push_back(mgr.False());
    bdd_map.push_back(mgr.True());
  }

  mini_bddt to_bdd(literalt a)
  {
    if(a.is_true())
      return mgr.True();
    if(a.is_false())
      return mgr.False();
    INVARIANT(a.var_no()<bdd_map.size(), "literal in map");
    mini_bddt bdd=bdd_map[a.var_no()];
    INVARIANT(bdd.is_initialized(), "initialized");
    if(a.sign())
      return !bdd;
    else
      return bdd;
  }

  literalt to_literal(const mini_bddt &bdd)
  {
    if(bdd.is_constant())
      return const_literal(bdd.is_true());
    std::size_t index=bdd.node_number();
    bdd_map[index]=bdd;
    return literalt(index, false);
  }

  literalt land(literalt a, literalt b) override
  {
    return to_literal(to_bdd(a) & to_bdd(b));
  }

  literalt lor(literalt a, literalt b) override
  {
    UNREACHABLE;
    return {};
  }

  literalt land(const bvt &bv) override
  {
    mini_bddt result=mgr.True();

    for(const auto &l : bv)
      result=result&to_bdd(l);

    return to_literal(result);
  }

  literalt lor(const bvt &bv) override
  {
    mini_bddt result=mgr.False();

    for(const auto &l : bv)
      result=result|to_bdd(l);

    return to_literal(result);
  }

  literalt lxor(literalt a, literalt b) override
  {
    return to_literal(to_bdd(a) ^ to_bdd(b));
  }

  literalt lxor(const bvt &bv) override
  {
    UNREACHABLE;
    return {};
  }

  literalt lnand(literalt a, literalt b) override
  {
    UNREACHABLE;
    return {};
  }

  literalt lnor(literalt a, literalt b) override
  {
    UNREACHABLE;
    return {};
  }

  literalt lequal(literalt a, literalt b) override
  {
    return to_literal(to_bdd(a)==to_bdd(b));
  }

  literalt limplies(literalt a, literalt b) override
  {
    UNREACHABLE;
    return {};
  }

  literalt lselect(literalt a, literalt b, literalt c) override
  {
    UNREACHABLE;
    return {};
  }

  void lcnf(const bvt &bv) override
  {
    UNREACHABLE;
  }

  literalt new_variable() override
  {
    return to_literal(mgr.Var(""));
  }

  size_t no_variables() const override
  {
    return bdd_map.size();
  }

  const std::string solver_text() override
  {
    return "BDDs";
  }

  resultt prop_solve() override
  {
    UNREACHABLE;
    return {};
  }

  tvt l_get(literalt a) const override
  {
    UNREACHABLE;
    return {};
  }

  expanding_vectort<mini_bddt> bdd_map;

  bool has_set_to() const override { return false; }
  bool cnf_handled_well() const override { return false; }

  void set_assignment(literalt, bool) override
  {
    UNIMPLEMENTED;
  }

  bool is_in_conflict(literalt) const override
  {
    UNREACHABLE;
    return false;
  }
};

SCENARIO("miniBDD", "[core][solver][miniBDD]")
{
  GIVEN("A bdd for x&!x")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    mini_bdd_mgrt bdd_mgr;
    bdd_propt bdd_prop(bdd_mgr);
    prop_conv_solvert solver(ns, bdd_prop);

    symbol_exprt var("x", bool_typet());
    literalt result=
      solver.convert(and_exprt(var, not_exprt(var)));

    REQUIRE(result.is_false());
  }

  GIVEN("A bdd for x&!x==0")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    mini_bdd_mgrt bdd_mgr;
    bdd_propt bdd_prop(bdd_mgr);
    boolbvt boolbv(ns, bdd_prop);

    unsignedbv_typet type(2);
    symbol_exprt var("x", type);
    equal_exprt equality(
      bitand_exprt(var, bitnot_exprt(var)),
      from_integer(0, type));

    literalt result=
      boolbv.convert(equality);

    REQUIRE(result.is_true());
  }

  GIVEN("A bdd for x+x==1")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    mini_bdd_mgrt bdd_mgr;
    bdd_propt bdd_prop(bdd_mgr);
    boolbvt boolbv(ns, bdd_prop);

    unsignedbv_typet type(32);
    symbol_exprt var("x", type);
    equal_exprt equality(
      plus_exprt(var, var),
      from_integer(1, type));

    literalt result=
      boolbv.convert(equality);

    REQUIRE(result.is_false());
  }

  GIVEN("A bdd for x*y==y*x")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    mini_bdd_mgrt bdd_mgr;
    bdd_propt bdd_prop(bdd_mgr);
    boolbvt boolbv(ns, bdd_prop);

    unsignedbv_typet type(4);
    symbol_exprt var_x("x", type);
    symbol_exprt var_y("y", type);
    equal_exprt equality(
      mult_exprt(var_x, var_y),
      mult_exprt(var_y, var_x));

    literalt result=
      boolbv.convert(equality);

    REQUIRE(result.is_true());
  }

  GIVEN("A bdd for x*x==2")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    mini_bdd_mgrt bdd_mgr;
    bdd_propt bdd_prop(bdd_mgr);
    boolbvt boolbv(ns, bdd_prop);

    unsignedbv_typet type(8);
    symbol_exprt var_x("x", type);
    equal_exprt equality(
      mult_exprt(var_x, var_x),
      from_integer(2, type));

    literalt result=
      boolbv.convert(equality);

    REQUIRE(result.is_false());
  }

  GIVEN("A bdd for x*x==4")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    mini_bdd_mgrt bdd_mgr;
    bdd_propt bdd_prop(bdd_mgr);
    boolbvt boolbv(ns, bdd_prop);

    unsignedbv_typet type(8);
    symbol_exprt var_x("x", type);
    equal_exprt equality(
      mult_exprt(var_x, var_x),
      from_integer(4, type));

    literalt result=
      boolbv.convert(equality);

    REQUIRE(!result.is_constant());
  }

  GIVEN("A bdd for x&y")
  {
    mini_bdd_mgrt mgr;

    mini_bddt x_bdd = mgr.Var("x");
    mini_bddt y_bdd = mgr.Var("y");
    mini_bddt final_bdd = x_bdd & y_bdd;

    std::ostringstream oss;
    mgr.DumpDot(oss);

    const std::string dot_string =
      "digraph BDD {\n"
      "center = true;\n"
      "{ rank = same; { node [style=invis]; \"T\" };\n"
      "  { node [shape=box,fontsize=24]; \"0\"; }\n"
      "  { node [shape=box,fontsize=24]; \"1\"; }\n"
      "}\n"
      "\n"
      "{ rank=same; { node [shape=plaintext,fontname="
      "\"Times Italic\",fontsize=24] \" x \" }; \"2\"; \"4\"; }\n"
      "{ rank=same; { node [shape=plaintext,fontname="
      "\"Times Italic\",fontsize=24] \" y \" }; \"3\"; }\n"
      "\n"
      "{ edge [style = invis]; \" x \" -> \" y \" -> \"T\"; }\n"
      "\n"
      "\"2\" -> \"1\" [style=solid,arrowsize=\".75\"];\n"
      "\"2\" -> \"0\" [style=dashed,arrowsize=\".75\"];\n"
      "\n"
      "\"3\" -> \"1\" [style=solid,arrowsize=\".75\"];\n"
      "\"3\" -> \"0\" [style=dashed,arrowsize=\".75\"];\n"
      "\n"
      "\"4\" -> \"3\" [style=solid,arrowsize=\".75\"];\n"
      "\"4\" -> \"0\" [style=dashed,arrowsize=\".75\"];\n"
      "\n"
      "}\n";

    REQUIRE(oss.str() == dot_string);
  }

  GIVEN("A bdd for (a&b)|!a")
  {
    symbol_exprt a("a", bool_typet());
    symbol_exprt b("b", bool_typet());

    or_exprt o(and_exprt(a, b), not_exprt(a));

    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    {
      std::ostringstream oss;
      oss << format(o);
      REQUIRE(oss.str() == "(a ∧ b) ∨ ¬a");
    }

    bdd_exprt t(ns);
    t.from_expr(o);

    {
      std::ostringstream oss;
      oss << format(t.as_expr());
      REQUIRE(oss.str() == "¬a ∨ b");
    }
  }
}
