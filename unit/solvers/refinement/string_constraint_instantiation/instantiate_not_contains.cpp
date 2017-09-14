/*******************************************************************\

 Module: Unit tests for `instantiate_not_contains_`.

 Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

#include <catch.hpp>

#include <solvers/refinement/string_constraint_instantiation.h>

#include <solvers/sat/satcheck.h>
#include <solvers/refinement/bv_refinement.h>
#include <java_bytecode/java_types.h>
#include <langapi/mode.h>
#include <java_bytecode/java_bytecode_language.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>

/// \class Types used throughout the test. Currently it is impossible to
/// statically initialize this value, there is a PR to allow this
/// diffblue/cbmc/pull/1213
class tt
{
public:
  tt() {}
  typet char_type() const {return java_char_type();}
  typet length_type() const {return java_int_type();}
  array_typet array_type() const
  {
    return array_typet(char_type(), infinity_exprt(length_type()));
  }
  refined_string_typet string_type() const
  {
    return refined_string_typet(length_type(), char_type());
  }
  array_typet witness_type() const
  {
    return array_typet(length_type(), infinity_exprt(length_type()));
  }
};

// Static variable to get proper types
const tt t;

/// Creates a `constant_exprt` of the proper length type.
/// \param [in] i: integer to convert
/// \return corresponding `constant_exprt`
constant_exprt from_integer(const mp_integer i)
{
  return from_integer(i, t.length_type());
}

/// Creates a `string_exprt` of the proper string type.
/// \param [in] str: string to convert
/// \return corresponding `string_exprt`
string_exprt make_string_exprt(const std::string &str)
{
  const constant_exprt length=from_integer(str.length(), t.length_type());
  array_exprt content(t.array_type());

  for(const char c : str)
    content.copy_to_operands(from_integer(c, t.char_type()));

  return string_exprt(length, content, t.string_type());
}

/// For a constant `string_exprt`, creates a full index set.
/// \param [in] s: `string_exprt` to create index set for
/// \return the corresponding index set
std::set<exprt> full_index_set(const string_exprt &s)
{
  PRECONDITION(s.length().is_constant());
  mp_integer n;
  to_integer(s.length(), n);
  std::set<exprt> ret;
  for(mp_integer i=0; i<n; ++i)
    ret.insert(from_integer(i));
  return ret;
}

/// Simplifies, and returns the conjunction of the lemmas.
/// \param [in] lemmas: lemmas to process
/// \param [in] ns: namespace for simplifying
/// \return conjunction of simplified lemmas
exprt combine_lemmas(const std::vector<exprt> &lemmas, const namespacet &ns)
{
  // Conjunction of new lemmas
  exprt conj=conjunction(lemmas);

  // Simplify
  simplify(conj, ns);

  return conj;
}

/// Creates information string and simplifies lemmas.
/// \param [in,out] lemmas: lemmas to process (which are simplified)
/// \param [in] ns: namespace for printing and simplifying
/// \return information string
std::string create_info(std::vector<exprt> &lemmas, const namespacet &ns)
{
  // Recording new lemmas
  std::string new_lemmas;
  for(auto &lemma : lemmas)
  {
    simplify(lemma, ns);
    new_lemmas+=from_expr(ns, "", lemma)+"\n\n";
  }
  return "Instantiated lemmas:\n"+new_lemmas;
}

/// Checks the satisfiability of the given expression.
/// \param [in] expr: expression to check
/// \param [in] ns: namespace for solver
/// \return SAT solver result
decision_proceduret::resultt check_sat(const exprt &expr, const namespacet &ns)
{
  satcheck_no_simplifiert sat_check;
  bv_refinementt::infot info;
  info.ns=&ns;
  info.prop=&sat_check;
  const auto ui=ui_message_handlert::uit::PLAIN;
  info.ui=ui;
  bv_refinementt solver(info);
  solver << expr;
  return solver();
}

// The [!mayfail] tag allows tests to fail while reporting the failure
SCENARIO("instantiate_not_contains",
  "[!mayfail][core][solvers][refinement][string_constraint_instantiation]")
{
  // For printing expression
  register_language(new_java_bytecode_language);
  symbol_tablet symtbl;
  const namespacet ns(symtbl);

  GIVEN("The not_contains axioms of String.lastIndexOf(String, Int)")
  {
    // Creating strings
    const string_exprt ab=make_string_exprt("ab");
    const string_exprt b=make_string_exprt("b");

    // Creating "ab".lastIndexOf("b", 0)
    function_application_exprt func(
      symbol_exprt(ID_cprover_string_last_index_of_func), t.length_type());
    const exprt::operandst args={ab, b, from_integer(2)};
    func.arguments()=args;

    // Generating the corresponding axioms and simplifying, recording info
    symbol_tablet symtab;
    namespacet empty_ns(symtab);
    string_constraint_generatort::infot info;
    info.ns=&empty_ns;
    string_constraint_generatort generator(info);
    exprt res=generator.add_axioms_for_function_application(func);
    std::string axioms;
    std::vector<string_not_contains_constraintt> nc_axioms;
    for(exprt axiom : generator.get_axioms())
    {
      simplify(axiom, ns);
      if(axiom.id()==ID_string_constraint)
      {
        string_constraintt sc=to_string_constraint(axiom);
        axioms+=from_expr(ns, "", sc);
      }
      else if(axiom.id()==ID_string_not_contains_constraint)
      {
        string_not_contains_constraintt sc=
          to_string_not_contains_constraint(axiom);
        axioms+=from_expr(ns, "", sc);
        generator.witness[sc]=
          generator.fresh_symbol("w", t.witness_type());
        nc_axioms.push_back(sc);
      }
      else
        axioms+=from_expr(ns, "", axiom);

      axioms+="\n\n";
    }
    INFO("Original axioms:\n");
    INFO(axioms);

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_ab=full_index_set(ab);
      const std::set<exprt> index_set_b=full_index_set(b);

      // List of new lemmas to be returned
      std::vector<exprt> lemmas;

      // Instantiate the lemmas
      for(const auto &axiom : nc_axioms)
      {
        const std::vector<exprt> l=instantiate_not_contains(
          axiom, index_set_ab, index_set_b, generator);
        lemmas.insert(lemmas.end(), l.begin(), l.end());
      }

      const exprt conj=combine_lemmas(lemmas, ns);
      const std::string info=create_info(lemmas, ns);
      INFO(info);

      THEN("the conjunction of instantiations is SAT")
      {
        // Check if SAT
        decision_proceduret::resultt result=check_sat(conj, ns);

        // Require SAT
        if(result==decision_proceduret::resultt::D_ERROR)
          INFO("Got an error");

        REQUIRE(result==decision_proceduret::resultt::D_SATISFIABLE);
      }
    }
  }

  GIVEN("A vacuously true not_contains axioms")
  {
    // Creating strings
    const string_exprt a=make_string_exprt("a");

    // Make
    // forall x in [0, 0). true => (exists y in [0, 1).
    //   { .=1, .={ (char)'a' } }[x+y] != { .=1, .={ (char)'b' } }[y]
    // )
    // which is vacuously true.
    string_not_contains_constraintt vacuous(
      from_integer(0),
      from_integer(0),
      true_exprt(),
      from_integer(0),
      from_integer(1),
      a,
      a);

    // Create witness for axiom
    symbol_tablet symtab;
    namespacet empty_ns(symtab);
    string_constraint_generatort::infot info;
    info.ns=&empty_ns;
    string_constraint_generatort generator(info);
    generator.witness[vacuous]=
      generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(from_expr(ns, "", vacuous)+"\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_a=full_index_set(a);

      // Instantiate the lemmas
      std::vector<exprt> lemmas=instantiate_not_contains(
        vacuous, index_set_a, index_set_a, generator);

      const exprt conj=combine_lemmas(lemmas, ns);
      const std::string info=create_info(lemmas, ns);
      INFO(info);

      THEN("the conjunction of instantiations is SAT")
      {
        // Check if SAT
        decision_proceduret::resultt result=check_sat(conj, ns);

        // Require SAT
        if(result==decision_proceduret::resultt::D_ERROR)
          INFO("Got an error");

        REQUIRE(result==decision_proceduret::resultt::D_SATISFIABLE);
      }
    }
  }

  GIVEN("A trivially false (via empty existential) not_contains axioms")
  {
    // Creating strings
    const string_exprt a=make_string_exprt("a");
    const string_exprt b=make_string_exprt("b");

    // Make
    // forall x in [0, 1). true => (exists y in [0, 0).
    //   { .=1, .={ (char)'a' } }[x+y] != { .=1, .={ (char)'b' } }[y]
    // )
    // which is false.
    string_not_contains_constraintt trivial(
      from_integer(0),
      from_integer(1),
      true_exprt(),
      from_integer(0),
      from_integer(0),
      a,
      b);

    // Create witness for axiom
    symbol_tablet symtab;
    namespacet ns(symtab);
    string_constraint_generatort::infot info;
    info.ns=&ns;
    string_constraint_generatort generator(info);
    generator.witness[trivial]=
      generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(from_expr(ns, "", trivial)+"\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_a=full_index_set(a);
      const std::set<exprt> index_set_b=full_index_set(b);

      // Instantiate the lemmas
      std::vector<exprt> lemmas=instantiate_not_contains(
        trivial, index_set_a, index_set_b, generator);

      const exprt conj=combine_lemmas(lemmas, ns);
      const std::string info=create_info(lemmas, ns);
      INFO(info);

      THEN("the conjunction of instantiations is UNSAT")
      {
        // Check if SAT
        decision_proceduret::resultt result=check_sat(conj, ns);

        // Require UNSAT
        if(result==decision_proceduret::resultt::D_ERROR)
          INFO("Got an error");

        REQUIRE(result==decision_proceduret::resultt::D_UNSATISFIABLE);
      }
    }
  }

  GIVEN("A not_contains axioms with an non-empty and empty string")
  {
    // Creating strings
    const string_exprt a=make_string_exprt("a");
    const string_exprt empty=make_string_exprt("");

    // Make
    // forall x in [0, 1). true => (exists y in [0, 0).
    //   { .=1, .={ (char)'a' } }[x+y] != { .=0, .={ } }[y]
    // )
    // which is false.
    string_not_contains_constraintt trivial(
      from_integer(0),
      from_integer(1),
      true_exprt(),
      from_integer(0),
      from_integer(0),
      a,
      empty);

    // Create witness for axiom
    symbol_tablet symtab;
    namespacet empty_ns(symtab);
    string_constraint_generatort::infot info;
    info.ns=&empty_ns;
    string_constraint_generatort generator(info);
    generator.witness[trivial]=
      generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(from_expr(ns, "", trivial)+"\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_a=full_index_set(a);
      const std::set<exprt> index_set_empty=
        {generator.fresh_exist_index("z", t.length_type())};

      // Instantiate the lemmas
      std::vector<exprt> lemmas=instantiate_not_contains(
        trivial, index_set_a, index_set_empty, generator);

      const exprt conj=combine_lemmas(lemmas, ns);
      const std::string info=create_info(lemmas, ns);
      INFO(info);

      THEN("the conjunction of instantiations is UNSAT")
      {
        // Check if SAT
        decision_proceduret::resultt result=check_sat(conj, ns);

        // Require UNSAT
        if(result==decision_proceduret::resultt::D_ERROR)
          INFO("Got an error");

        REQUIRE(result==decision_proceduret::resultt::D_UNSATISFIABLE);
      }
    }
  }

  GIVEN("A not_contains on the same string twice (hence is false)")
  {
    // Creating strings
    const string_exprt ab=make_string_exprt("ab");

    // Make
    // forall x in [0, 2). true => (exists y in [0, 2).
    //   { .=2, .={ (char)'a', (char)'b'} }[x+y] !=
    //   { .=2, .={ (char)'a', (char)'b'}[y]
    // )
    // which is false (for x = 0).
    string_not_contains_constraintt trivial(
      from_integer(0),
      from_integer(2),
      true_exprt(),
      from_integer(0),
      from_integer(2),
      ab,
      ab);

    // Create witness for axiom
    symbol_tablet symtab;
    namespacet empty_ns(symtab);

    string_constraint_generatort::infot info;
    info.ns=&empty_ns;
    string_constraint_generatort generator(info);
    generator.witness[trivial]=
      generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(from_expr(ns, "", trivial)+"\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_ab=full_index_set(ab);

      // Instantiate the lemmas
      std::vector<exprt> lemmas=instantiate_not_contains(
        trivial, index_set_ab, index_set_ab, generator);

      const exprt conj=combine_lemmas(lemmas, ns);
      const std::string info=create_info(lemmas, ns);
      INFO(info);

      THEN("the conjunction of instantiations is UNSAT")
      {
        // Check if SAT
        decision_proceduret::resultt result=check_sat(conj, ns);

        // Require UNSAT
        if(result==decision_proceduret::resultt::D_ERROR)
          INFO("Got an error");

        REQUIRE(result==decision_proceduret::resultt::D_UNSATISFIABLE);
      }
    }
  }

  GIVEN("A not_contains on two string with no chars in common (hence is true)")
  {
    // Creating strings
    const string_exprt ab=make_string_exprt("ab");
    const string_exprt cd=make_string_exprt("cd");

    // Make
    // forall x in [0, 2). true => (exists y in [0, 2).
    //   { .=2, .={ (char)'a', (char)'b'} }[x+y] !=
    //   { .=2, .={ (char)'a', (char)'b'}[y]
    // )
    // which is true.
    string_not_contains_constraintt trivial(
      from_integer(0),
      from_integer(2),
      true_exprt(),
      from_integer(0),
      from_integer(2),
      ab,
      cd);

    // Create witness for axiom
    symbol_tablet symtab;
    namespacet empty_ns(symtab);
    string_constraint_generatort::infot info;
    info.ns=&empty_ns;
    string_constraint_generatort generator(info);
    generator.witness[trivial]=
      generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(from_expr(ns, "", trivial)+"\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_ab=full_index_set(ab);
      const std::set<exprt> index_set_cd=full_index_set(cd);

      // Instantiate the lemmas
      std::vector<exprt> lemmas=instantiate_not_contains(
        trivial, index_set_ab, index_set_cd, generator);

      const exprt conj=combine_lemmas(lemmas, ns);
      const std::string info=create_info(lemmas, ns);
      INFO(info);

      THEN("the conjunction of instantiations is SAT")
      {
        // Check if SAT
        decision_proceduret::resultt result=check_sat(conj, ns);

        // Require UNSAT
        if(result==decision_proceduret::resultt::D_ERROR)
          INFO("Got an error");

        REQUIRE(result==decision_proceduret::resultt::D_SATISFIABLE);
      }
    }
  }
}
