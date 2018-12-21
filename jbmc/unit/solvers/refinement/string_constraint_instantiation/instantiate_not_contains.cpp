/*******************************************************************\

 Module: Unit tests for `instantiate_not_contains_`.

 Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <numeric>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_types.h>

#include <langapi/mode.h>
#include <langapi/language_util.h>

#include <solvers/refinement/string_constraint_instantiation.h>
#include <solvers/sat/satcheck.h>

#include <util/simplify_expr.h>
#include <util/config.h>

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
    return refined_string_typet(length_type(), pointer_type(char_type()));
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
constant_exprt from_integer(const mp_integer &i)
{
  return from_integer(i, t.length_type());
}

/// Creates a `string_exprt` of the proper string type.
/// \param [in] str: string to convert
/// \return corresponding `string_exprt`
array_string_exprt make_string_exprt(const std::string &str)
{
  const constant_exprt length=from_integer(str.length(), t.length_type());
  array_exprt content(array_typet(t.char_type(), length));

  for(const char c : str)
    content.copy_to_operands(from_integer(c, t.char_type()));

  return to_array_string_expr(content);
}

/// Return a pointer to the data array of an array_string_exprt
/// \param arr: char array representing a string
/// \return pointer to the first character of the array
exprt get_data_pointer(const array_string_exprt &arr)
{
  return address_of_exprt(index_exprt(arr, from_integer(0, t.length_type())));
}

/// Creates a `string_exprt` of the proper string type.
/// \param [in] str: string to convert
/// \return corresponding `string_exprt`
refined_string_exprt make_refined_string_exprt(const array_string_exprt &arr)
{
  return refined_string_exprt(arr.length(), get_data_pointer(arr));
}

/// For a constant `string_exprt`, creates a full index set.
/// \param [in] s: `string_exprt` to create index set for
/// \return the corresponding index set
std::set<exprt> full_index_set(const array_string_exprt &s)
{
  const mp_integer n = numeric_cast_v<mp_integer>(s.length());
  std::set<exprt> ret;
  for(mp_integer i=0; i<n; ++i)
    ret.insert(from_integer(i));
  return ret;
}

/// Create the cartesian product of two sets.
template <class X, class Y>
std::set<std::pair<X, Y>> product(const std::set<X> xs, const std::set<Y> ys)
{
  std::set<std::pair<X, Y>> s;
  for(const auto &x : xs)
    for(const auto &y : ys)
      s.insert(std::pair<X, Y>(x, y));
  return s;
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
    std::string lemma_string;
    get_language_from_mode(ID_java)->from_expr(lemma, lemma_string, ns);
    new_lemmas += lemma_string + "\n\n";
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
  info.output_xml = false;
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
  std::unique_ptr<languaget> java_lang = get_language_from_mode(ID_java);
  symbol_tablet symtbl;
  const namespacet ns(symtbl);

  // initialize architecture with sensible default values
  config.set_arch("none");

  // Creating strings
  const auto ab_array = make_string_exprt("ab");
  const auto b_array = make_string_exprt("b");
  const auto a_array = make_string_exprt("a");
  const auto empty_array = make_string_exprt("");
  const auto cd_array = make_string_exprt("cd");
  const auto ab = make_refined_string_exprt(ab_array);
  const auto b = make_refined_string_exprt(b_array);
  const auto a = make_refined_string_exprt(a_array);
  const auto empty = make_refined_string_exprt(empty_array);
  const auto cd = make_refined_string_exprt(cd_array);

  GIVEN("The not_contains axioms of String.lastIndexOf(String, Int)")
  {
    // Creating "ab".lastIndexOf("b", 0)
    const function_application_exprt func(
      symbol_exprt(ID_cprover_string_last_index_of_func),
      {ab, b, from_integer(2)},
      t.length_type());

    // Generating the corresponding axioms and simplifying, recording info
    symbol_tablet symtab;
    const namespacet empty_ns(symtab);
    string_constraint_generatort generator(ns);
    const auto pair = generator.add_axioms_for_function_application(
      generator.fresh_symbol, func);
    const string_constraintst &constraints = pair.second;

    std::string axioms;
    std::vector<string_not_contains_constraintt> nc_axioms;
    std::unordered_map<string_not_contains_constraintt, symbol_exprt> witnesses;

    std::accumulate(
      constraints.universal.begin(),
      constraints.universal.end(),
      axioms,
      [&](const std::string &accu, string_constraintt sc) {
        simplify(sc.body, ns);
        return accu + to_string(sc) + "\n\n";
      });

    axioms = std::accumulate(
      constraints.not_contains.begin(),
      constraints.not_contains.end(),
      axioms,
      [&](const std::string &accu, string_not_contains_constraintt sc) {
        simplify(sc.premise, ns);
        simplify(sc.s0, ns);
        simplify(sc.s1, ns);
        witnesses[sc] = generator.fresh_symbol("w", t.witness_type());
        nc_axioms.push_back(sc);
        return accu + to_string(sc) + "\n\n";
      });

    axioms = std::accumulate(
      constraints.existential.begin(),
      constraints.existential.end(),
      axioms,
      [&](const std::string &accu, exprt axiom) {
        simplify(axiom, ns);
        std::string s;
        java_lang->from_expr(axiom, s, ns);
        return accu + s + "\n\n";
      });

    INFO("Original axioms:\n");
    INFO(axioms);

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_ab = full_index_set(ab_array);
      const std::set<exprt> index_set_b = full_index_set(b_array);

      // List of new lemmas to be returned
      std::vector<exprt> lemmas;

      // Instantiate the lemmas
      for(const auto &axiom : nc_axioms)
      {
        const std::vector<exprt> l = instantiate_not_contains(
          axiom, product(index_set_ab, index_set_b), witnesses);
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
    // Make
    // forall x in [0, 0). true => (exists y in [0, 1).
    //   { .=1, .={ (char)'a' } }[x+y] != { .=1, .={ (char)'b' } }[y]
    // )
    // which is vacuously true.
    const string_not_contains_constraintt vacuous = {from_integer(0),
                                                     from_integer(0),
                                                     true_exprt(),
                                                     from_integer(0),
                                                     from_integer(1),
                                                     a_array,
                                                     a_array};

    // Create witness for axiom
    symbol_tablet symtab;
    const namespacet empty_ns(symtab);
    string_constraint_generatort generator(ns);
    std::unordered_map<string_not_contains_constraintt, symbol_exprt> witnesses;
    witnesses[vacuous] = generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(to_string(vacuous) + "\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_a = full_index_set(a_array);

      // Instantiate the lemmas
      std::vector<exprt> lemmas = instantiate_not_contains(
        vacuous, product(index_set_a, index_set_a), witnesses);

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
    // Make
    // forall x in [0, 1). true => (exists y in [0, 0).
    //   { .=1, .={ (char)'a' } }[x+y] != { .=1, .={ (char)'b' } }[y]
    // )
    // which is false.
    const string_not_contains_constraintt trivial = {from_integer(0),
                                                     from_integer(1),
                                                     true_exprt(),
                                                     from_integer(0),
                                                     from_integer(0),
                                                     a_array,
                                                     b_array};

    // Create witness for axiom
    symbol_tablet symtab;
    const namespacet ns(symtab);
    string_constraint_generatort generator(ns);
    std::unordered_map<string_not_contains_constraintt, symbol_exprt> witnesses;
    witnesses[trivial] = generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(to_string(trivial) + "\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_a = full_index_set(a_array);
      const std::set<exprt> index_set_b = full_index_set(b_array);

      // Instantiate the lemmas
      std::vector<exprt> lemmas = instantiate_not_contains(
        trivial, product(index_set_a, index_set_b), witnesses);

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
    // Make
    // forall x in [0, 1). true => (exists y in [0, 0).
    //   { .=1, .={ (char)'a' } }[x+y] != { .=0, .={ } }[y]
    // )
    // which is false.
    const string_not_contains_constraintt trivial = {from_integer(0),
                                                     from_integer(1),
                                                     true_exprt(),
                                                     from_integer(0),
                                                     from_integer(0),
                                                     a_array,
                                                     empty_array};

    // Create witness for axiom
    symbol_tablet symtab;
    const namespacet empty_ns(symtab);
    string_constraint_generatort generator(ns);
    std::unordered_map<string_not_contains_constraintt, symbol_exprt> witnesses;
    witnesses[trivial] = generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(to_string(trivial) + "\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_a = full_index_set(a_array);
      const std::set<exprt> index_set_empty = {
        generator.fresh_symbol("z", t.length_type())};

      // Instantiate the lemmas
      std::vector<exprt> lemmas = instantiate_not_contains(
        trivial, product(index_set_a, index_set_empty), witnesses);

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
    // Make
    // forall x in [0, 2). true => (exists y in [0, 2).
    //   { .=2, .={ (char)'a', (char)'b'} }[x+y] !=
    //   { .=2, .={ (char)'a', (char)'b'}[y]
    // )
    // which is false (for x = 0).
    const string_not_contains_constraintt trivial = {from_integer(0),
                                                     from_integer(2),
                                                     true_exprt(),
                                                     from_integer(0),
                                                     from_integer(2),
                                                     ab_array,
                                                     ab_array};

    // Create witness for axiom
    symbol_tablet symtab;
    const namespacet empty_ns(symtab);

    string_constraint_generatort generator(ns);
    std::unordered_map<string_not_contains_constraintt, symbol_exprt> witnesses;
    witnesses[trivial] = generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(to_string(trivial) + "\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_ab = full_index_set(ab_array);

      // Instantiate the lemmas
      std::vector<exprt> lemmas = instantiate_not_contains(
        trivial, product(index_set_ab, index_set_ab), witnesses);

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
    // Make
    // forall x in [0, 2). true => (exists y in [0, 2).
    //   { .=2, .={ (char)'a', (char)'b'} }[x+y] !=
    //   { .=2, .={ (char)'a', (char)'b'}[y]
    // )
    // which is true.
    const string_not_contains_constraintt trivial = {from_integer(0),
                                                     from_integer(2),
                                                     true_exprt(),
                                                     from_integer(0),
                                                     from_integer(2),
                                                     ab_array,
                                                     cd_array};

    // Create witness for axiom
    symbol_tablet symtab;
    const namespacet empty_ns(symtab);
    string_constraint_generatort generator(ns);
    std::unordered_map<string_not_contains_constraintt, symbol_exprt> witnesses;
    witnesses[trivial] = generator.fresh_symbol("w", t.witness_type());

    INFO("Original axiom:\n");
    INFO(to_string(trivial) + "\n\n");

    WHEN("we instantiate and simplify")
    {
      // Making index sets
      const std::set<exprt> index_set_ab = full_index_set(ab_array);
      const std::set<exprt> index_set_cd = full_index_set(cd_array);

      // Instantiate the lemmas
      std::vector<exprt> lemmas = instantiate_not_contains(
        trivial, product(index_set_ab, index_set_cd), witnesses);

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
