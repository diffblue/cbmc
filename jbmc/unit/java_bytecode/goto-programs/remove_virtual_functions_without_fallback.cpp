/*******************************************************************\

Module: Unit tests for remove_virtual_functions pass running in
        assume-false-if-no-match mode.

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <testing-utils/use_catch.h>

#include <util/pointer_expr.h>
#include <util/simplify_expr.h>

#include <goto-programs/remove_virtual_functions.h>

/// Try to resolve a classid comparison `expr`, assuming that any accessed
/// classid has value `actual_class_id`
exprt resolve_classid_test(
  const exprt &expr,
  const irep_idt &actual_class_id,
  const namespacet &ns)
{
  if(expr.id() == ID_or || expr.id() == ID_and)
  {
    exprt resolved = expr;
    for(exprt &op : resolved.operands())
      op = resolve_classid_test(op, actual_class_id, ns);
    simplify(resolved, ns);
    return resolved;
  }

  const auto &expr_binary = to_binary_expr(expr);

  if(expr_binary.op0().is_constant() && !expr_binary.op1().is_constant())
  {
    binary_exprt swapped = expr_binary;
    std::swap(swapped.op0(), swapped.op1());
    return resolve_classid_test(swapped, actual_class_id, ns);
  }

  if(
    expr_binary.op0().id() == ID_member &&
    to_member_expr(expr_binary.op0()).get_component_name() ==
      "@class_identifier" &&
    expr_binary.op1().is_constant() &&
    expr_binary.op1().type().id() == ID_string)
  {
    binary_exprt resolved = expr_binary;
    resolved.op0() = constant_exprt(actual_class_id, expr_binary.op1().type());
    simplify(resolved, ns);
    return std::move(resolved);
  }

  return expr;
}

static bool is_call_to(
  goto_programt::const_targett inst, const irep_idt &callee)
{
  if(!inst->is_function_call())
    return false;
  const exprt &callee_expr = inst->call_function();
  if(callee_expr.id() != ID_symbol)
    return false;
  return to_symbol_expr(callee_expr).get_identifier() == callee;
}

static bool is_assume_false(goto_programt::const_targett inst)
{
  return inst->is_assume() && inst->condition().is_constant() &&
         to_constant_expr(inst->condition()).is_false();
}

/// Interpret `program`, resolving classid comparisons assuming any actual
/// callee has class `actual_class_id`, returning the first instruction we
/// arrive at which is neither a SKIP, nor a GOTO that can be resolved in this
/// way.
static goto_programt::const_targett interpret_classid_comparison(
  const goto_programt &program,
  const irep_idt &actual_class_id,
  const namespacet &ns)
{
  REQUIRE(!program.instructions.empty());
  goto_programt::const_targett pc = program.instructions.begin();

  while(pc != program.instructions.end())
  {
    if(pc->type() == GOTO)
    {
      exprt guard = pc->condition();
      guard = resolve_classid_test(guard, actual_class_id, ns);
      if(!guard.is_constant())
      {
        // Can't resolve the test, so exit here:
        return pc;
      }
      else if(to_constant_expr(guard).is_true())
      {
        REQUIRE(pc->targets.begin() != pc->targets.end());
        pc = *(pc->targets.begin());
      }
      else
      {
        CHECK_RETURN(to_constant_expr(guard).is_false());
        ++pc;
      }
    }
    else if(pc->type() == SKIP)
    {
      ++pc;
    }
    else
    {
      return pc;
    }
  }

  return program.get_end_function();
}

SCENARIO(
  "Remove virtual functions without a fallback function",
  "[core][goto-programs][remove_virtual_functions]")
{
  symbol_tablet symbol_table = load_java_class(
    "VirtualFunctionsTestParent", "./java_bytecode/goto-programs/");
  const irep_idt test_program_id = "java::testProgram:()V";
  symbolt test_program_symbol{};
  test_program_symbol.mode = ID_java;
  test_program_symbol.name = test_program_id;
  test_program_symbol.base_name = test_program_id;
  symbol_table.insert(test_program_symbol);
  namespacet ns(symbol_table);

  const symbolt &callee_symbol =
    symbol_table.lookup_ref("java::VirtualFunctionsTestParent.f:()V");

  class_method_descriptor_exprt callee{
    callee_symbol.type, "f:()V", "java::VirtualFunctionsTestParent", "f"};

  const code_function_callt call(
    callee,
    // Specific argument doesn't matter, so just pass an appropriately typed
    // null pointer:
    {null_pointer_exprt(
      to_pointer_type(to_code_type(callee.type()).parameters()[0].type()))});

  goto_programt test_program;
  auto virtual_call_inst =
    test_program.add(goto_programt::make_function_call(call));

  test_program.add(goto_programt::make_end_function());

  WHEN("Resolving virtual callsite to a single callee")
  {
    dispatch_table_entriest dispatch_table;
    dispatch_table.emplace_back("java::VirtualFunctionsTestParent");
    dispatch_table.back().symbol_expr = callee_symbol.symbol_expr();

    remove_virtual_function(
      symbol_table,
      test_program_id,
      test_program,
      virtual_call_inst,
      dispatch_table,
      virtual_dispatch_fallback_actiont::ASSUME_FALSE);

    THEN("One class should call the target, others should assume false")
    {
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestParent", ns),
          "java::VirtualFunctionsTestParent.f:()V"));
      REQUIRE(
        is_assume_false(
          interpret_classid_comparison(
            test_program, "java::NoSuchClass", ns)));
    }
  }

  WHEN("Resolving virtual callsite with two possible callees")
  {
    dispatch_table_entriest dispatch_table;
    dispatch_table.emplace_back("java::VirtualFunctionsTestParent");
    dispatch_table.back().symbol_expr = callee_symbol.symbol_expr();
    dispatch_table.emplace_back("java::VirtualFunctionsTestChild1");
    dispatch_table.back().symbol_expr =
      symbol_table.lookup_ref("java::VirtualFunctionsTestChild1.f:()V")
      .symbol_expr();

    remove_virtual_function(
      symbol_table,
      test_program_id,
      test_program,
      virtual_call_inst,
      dispatch_table,
      virtual_dispatch_fallback_actiont::ASSUME_FALSE);

    THEN("Each class should call its respective target, "
         "others should assume false")
    {
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestParent", ns),
          "java::VirtualFunctionsTestParent.f:()V"));
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestChild1", ns),
          "java::VirtualFunctionsTestChild1.f:()V"));
      REQUIRE(
        is_assume_false(
          interpret_classid_comparison(
            test_program, "java::NoSuchClass", ns)));
    }
  }

  WHEN("Resolving virtual callsite with three callees, "
       "two of which share a target")
  {
    dispatch_table_entriest dispatch_table;
    dispatch_table.emplace_back("java::VirtualFunctionsTestParent");
    dispatch_table.back().symbol_expr = callee_symbol.symbol_expr();
    dispatch_table.emplace_back("java::VirtualFunctionsTestChild1");
    dispatch_table.back().symbol_expr =
      symbol_table.lookup_ref("java::VirtualFunctionsTestChild1.f:()V")
      .symbol_expr();
    dispatch_table.emplace_back("java::VirtualFunctionsTestGrandchild");
    dispatch_table.back().symbol_expr =
      symbol_table.lookup_ref("java::VirtualFunctionsTestChild1.f:()V")
      .symbol_expr();

    remove_virtual_function(
      symbol_table,
      test_program_id,
      test_program,
      virtual_call_inst,
      dispatch_table,
      virtual_dispatch_fallback_actiont::ASSUME_FALSE);

    THEN("Each class should call its respective target, "
         "others should assume false")
    {
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestParent", ns),
          "java::VirtualFunctionsTestParent.f:()V"));
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestChild1", ns),
          "java::VirtualFunctionsTestChild1.f:()V"));
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestGrandchild", ns),
          "java::VirtualFunctionsTestChild1.f:()V"));
      REQUIRE(
        is_assume_false(
          interpret_classid_comparison(
            test_program, "java::NoSuchClass", ns)));
    }
  }

  WHEN("Resolving virtual callsite with four callees, two sharing a target "
       "with different-targeted callees on either side (i.e. [A, B, B, C])")
  {
    dispatch_table_entriest dispatch_table;
    dispatch_table.emplace_back("java::VirtualFunctionsTestParent");
    dispatch_table.back().symbol_expr = callee_symbol.symbol_expr();
    dispatch_table.emplace_back("java::VirtualFunctionsTestChild1");
    dispatch_table.back().symbol_expr =
      symbol_table.lookup_ref("java::VirtualFunctionsTestChild1.f:()V")
      .symbol_expr();
    dispatch_table.emplace_back("java::VirtualFunctionsTestGrandchild");
    dispatch_table.back().symbol_expr =
      symbol_table.lookup_ref("java::VirtualFunctionsTestChild1.f:()V")
      .symbol_expr();
    dispatch_table.emplace_back("java::VirtualFunctionsTestChild2");
    dispatch_table.back().symbol_expr =
      symbol_table.lookup_ref("java::VirtualFunctionsTestChild2.f:()V")
      .symbol_expr();

    remove_virtual_function(
      symbol_table,
      test_program_id,
      test_program,
      virtual_call_inst,
      dispatch_table,
      virtual_dispatch_fallback_actiont::ASSUME_FALSE);

    THEN("Each class should call its respective target, "
         "others should assume false")
    {
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestParent", ns),
          "java::VirtualFunctionsTestParent.f:()V"));
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestChild1", ns),
          "java::VirtualFunctionsTestChild1.f:()V"));
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestGrandchild", ns),
          "java::VirtualFunctionsTestChild1.f:()V"));
      REQUIRE(
        is_call_to(
          interpret_classid_comparison(
            test_program, "java::VirtualFunctionsTestChild2", ns),
          "java::VirtualFunctionsTestChild2.f:()V"));
      REQUIRE(
        is_assume_false(
          interpret_classid_comparison(
            test_program, "java::NoSuchClass", ns)));
    }
  }
}
