/*******************************************************************\

Module: Value-set analysis tests

Author: Chris Smowton, chris@smowton.net

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>

#include <goto-programs/goto_inline.h>
#include <goto-programs/initialize_goto_model.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/remove_java_new.h>
#include <langapi/mode.h>
#include <pointer-analysis/value_set_analysis.h>
#include <util/config.h>
#include <util/options.h>

/// An example customised value_sett. It makes a series of small changes
/// to the underlying value_sett logic, which can then be verified by the
/// test below:
/// * Writes to variables with 'ignored' in their name are ignored.
/// * Never propagate values via the field "never_read"
/// * Adds an ID_unknown to the value of variable "maybe_unknown" as it is read
/// * When a variable named `cause` is written, one named `effect` is zeroed.
class test_value_sett:public value_sett
{
public:
  static bool assigns_to_ignored_variable(const code_assignt &assign)
  {
    if(assign.lhs().id()!=ID_symbol)
      return false;
    const irep_idt &id=to_symbol_expr(assign.lhs()).get_identifier();
    return id2string(id).find("ignored")!=std::string::npos;
  }

  void apply_code_rec(const codet &code, const namespacet &ns) override
  {
    // Ignore assignments to the local "ignored"
    if(code.get_statement()==ID_assign &&
       assigns_to_ignored_variable(to_code_assign(code)))
    {
      return;
    }
    else
    {
      value_sett::apply_code_rec(code, ns);
    }
  }

  void assign_rec(
    const exprt &lhs,
    const object_mapt &values_rhs,
    const std::string &suffix,
    const namespacet &ns,
    bool add_to_sets) override
  {
    // Disregard writes against variables containing 'no_write':
    if(lhs.id()==ID_symbol)
    {
      const irep_idt &id=to_symbol_expr(lhs).get_identifier();
      if(id2string(id).find("no_write")!=std::string::npos)
        return;
    }

    value_sett::assign_rec(lhs, values_rhs, suffix, ns, add_to_sets);
  }

  void get_value_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const std::string &suffix,
    const typet &original_type,
    const namespacet &ns) const override
  {
    // Ignore reads from fields named "never_read"
    if(expr.id()==ID_member &&
       to_member_expr(expr).get_component_name()=="never_read")
    {
      return;
    }
    else
    {
      value_sett::get_value_set_rec(
        expr, dest, suffix, original_type, ns);
    }
  }

  void adjust_assign_rhs_values(
    const exprt &expr,
    const namespacet &,
    object_mapt &dest) const override
  {
    // Always add an ID_unknown to reads from variables containing
    // "maybe_unknown":
    exprt read_sym=expr;
    while(read_sym.id()==ID_typecast)
      read_sym=read_sym.op0();
    if(read_sym.id()==ID_symbol)
    {
      const irep_idt &id=to_symbol_expr(read_sym).get_identifier();
      if(id2string(id).find("maybe_unknown")!=std::string::npos)
        insert(dest, exprt(ID_unknown, read_sym.type()));
    }
  }

  void apply_assign_side_effects(
    const exprt &lhs,
    const exprt &,
    const namespacet &ns) override
  {
    // Whenever someone touches the variable "cause", null the
    // variable "effect":
    if(lhs.id()==ID_symbol)
    {
      const irep_idt &id=to_symbol_expr(lhs).get_identifier();
      const auto &id_str=id2string(id);
      auto find_idx=id_str.find("cause");
      if(find_idx!=std::string::npos)
      {
        std::string effect_id=id_str;
        effect_id.replace(find_idx, 5, "effect");
        assign(
          symbol_exprt(effect_id, lhs.type()),
          null_pointer_exprt(to_pointer_type(lhs.type())),
          ns,
          true,
          false);
      }
    }
  }
};

typedef
  value_set_analysis_templatet<value_set_domain_templatet<test_value_sett>>
  test_value_set_analysist;

#define TEST_PREFIX "java::CustomVSATest."
#define TEST_FUNCTION_NAME TEST_PREFIX "test:()V"
#define TEST_LOCAL_PREFIX TEST_FUNCTION_NAME "::"

template<class VST>
static value_setst::valuest
get_values(const VST &value_set, const namespacet &ns, const exprt &expr)
{
  value_setst::valuest vals;
  value_set.get_value_set(expr, vals, ns);
  return vals;
}

static std::size_t exprs_with_id(
  const value_setst::valuest &exprs, const irep_idt &id)
{
  return std::count_if(
    exprs.begin(),
    exprs.end(),
    [&id](const exprt &expr)
    {
      return expr.id()==id ||
        (expr.id()==ID_object_descriptor &&
         to_object_descriptor_expr(expr).object().id()==id);
    });
}

SCENARIO("test_value_set_analysis",
         "[core][pointer-analysis][value_set_analysis]")
{
  GIVEN("Normal and custom value-set analysis of CustomVSATest::test")
  {
    config.set_arch("none");
    config.main = "";

    // This classpath is the default, but the config object
    // is global and previous unit tests may have altered it
    config.java.classpath={"."};

    optionst options;
    options.set_option("java-cp-include-files", "CustomVSATest.class");

    register_language(new_java_bytecode_language);

    goto_modelt goto_model = initialize_goto_model(
      {"pointer-analysis/CustomVSATest.jar"}, null_message_handler, options);

    null_message_handlert message_handler;
    remove_java_new(goto_model, message_handler);

    namespacet ns(goto_model.symbol_table);

    // Fully inline the test program, to avoid VSA conflating
    // constructor callsites confusing the results we're trying to check:
    goto_function_inline(goto_model, TEST_FUNCTION_NAME, null_message_handler);

    const goto_programt &test_function=
      goto_model.goto_functions.function_map.at(TEST_PREFIX "test:()V").body;

    value_set_analysist::locationt test_function_end=
      std::prev(test_function.instructions.end());

    value_set_analysist normal_analysis(ns);
    normal_analysis(goto_model.goto_functions);
    const auto &normal_function_end_vs=
      normal_analysis[test_function_end].value_set;

    test_value_set_analysist test_analysis(ns);
    test_analysis(goto_model.goto_functions);
    const auto &test_function_end_vs=
      test_analysis[test_function_end].value_set;

    reference_typet jlo_ref_type=java_lang_object_type();

    WHEN("Writing to a local named 'ignored'")
    {
      symbol_exprt written_symbol(
        TEST_LOCAL_PREFIX "23::ignored", jlo_ref_type);
      THEN("The normal analysis should write to it")
      {
        auto normal_exprs=
          get_values(normal_function_end_vs, ns, written_symbol);
        REQUIRE(exprs_with_id(normal_exprs, ID_dynamic_object)==1);
        REQUIRE(exprs_with_id(normal_exprs, ID_unknown)==0);
      }
      THEN("The custom analysis should ignore the write to it")
      {
        auto test_exprs=
          get_values(test_function_end_vs, ns, written_symbol);
        REQUIRE(exprs_with_id(test_exprs, ID_dynamic_object)==0);
        REQUIRE(exprs_with_id(test_exprs, ID_unknown)==1);
      }
    }

    WHEN("Writing to a local named 'no_write'")
    {
      symbol_exprt written_symbol(
        TEST_LOCAL_PREFIX "31::no_write", jlo_ref_type);
      THEN("The normal analysis should write to it")
      {
        auto normal_exprs=
          get_values(normal_function_end_vs, ns, written_symbol);
        REQUIRE(exprs_with_id(normal_exprs, ID_dynamic_object)==1);
        REQUIRE(exprs_with_id(normal_exprs, ID_unknown)==0);
      }
      THEN("The custom analysis should ignore the write to it")
      {
        auto test_exprs=
          get_values(test_function_end_vs, ns, written_symbol);
        REQUIRE(exprs_with_id(test_exprs, ID_dynamic_object)==0);
        REQUIRE(exprs_with_id(test_exprs, ID_unknown)==1);
      }
    }

    WHEN("Reading from a field named 'never_read'")
    {
      symbol_exprt written_symbol(
        TEST_LOCAL_PREFIX "55::read", jlo_ref_type);
      THEN("The normal analysis should find a dynamic object")
      {
        auto normal_exprs=
          get_values(normal_function_end_vs, ns, written_symbol);
        REQUIRE(exprs_with_id(normal_exprs, ID_dynamic_object)==1);
        REQUIRE(exprs_with_id(normal_exprs, ID_unknown)==0);
      }
      THEN("The custom analysis should have no information about it")
      {
        auto test_exprs=
          get_values(test_function_end_vs, ns, written_symbol);
        REQUIRE(test_exprs.size()==0);
      }
    }

    WHEN("Reading from a variable named 'maybe_unknown'")
    {
      symbol_exprt written_symbol(
        TEST_PREFIX "maybe_unknown_read", jlo_ref_type);
      THEN("The normal analysis should find a dynamic object")
      {
        auto normal_exprs=
          get_values(normal_function_end_vs, ns, written_symbol);
        REQUIRE(exprs_with_id(normal_exprs, ID_dynamic_object)==1);
        REQUIRE(exprs_with_id(normal_exprs, ID_unknown)==0);
      }
      THEN("The custom analysis should find a dynamic object "
           "*and* an unknown entry")
      {
        auto test_exprs=
          get_values(test_function_end_vs, ns, written_symbol);
        REQUIRE(test_exprs.size()==2);
        REQUIRE(exprs_with_id(test_exprs, ID_unknown)==1);
        REQUIRE(exprs_with_id(test_exprs, ID_dynamic_object)==1);
      }
    }

    WHEN("Writing to a variable named 'cause'")
    {
      symbol_exprt read_before_cause_write(
        TEST_PREFIX "first_effect_read", jlo_ref_type);
        auto normal_exprs_before=
          get_values(normal_function_end_vs, ns, read_before_cause_write);
        auto test_exprs_before=
          get_values(test_function_end_vs, ns, read_before_cause_write);
      symbol_exprt read_after_cause_write(
        TEST_PREFIX "second_effect_read", jlo_ref_type);
        auto normal_exprs_after=
          get_values(normal_function_end_vs, ns, read_after_cause_write);
        auto test_exprs_after=
          get_values(test_function_end_vs, ns, read_after_cause_write);

      THEN("Before writing to 'cause' both analyses should think 'effect' "
           "points to some object")
      {
        REQUIRE(normal_exprs_before.size()==1);
        REQUIRE(exprs_with_id(normal_exprs_before, ID_dynamic_object)==1);

        REQUIRE(test_exprs_before.size()==1);
        REQUIRE(exprs_with_id(test_exprs_before, ID_dynamic_object)==1);
      }

      THEN("After writing to 'cause', the normal analysis should see no change "
           "to 'effect', while the custom analysis should see it changed")
      {
        REQUIRE(normal_exprs_after.size()==1);
        REQUIRE(exprs_with_id(normal_exprs_after, ID_dynamic_object)==1);

        REQUIRE(test_exprs_after.size()==1);
        REQUIRE(exprs_with_id(test_exprs_after, ID_null_object)==1);
      }
    }
  }
}
