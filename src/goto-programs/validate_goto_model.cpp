/*******************************************************************\

Module: Validate Goto Programs

Author: Diffblue

Date: Oct 2018

\*******************************************************************/
#include "validate_goto_model.h"

#include <set>

#include "goto_functions.h"
#include <util/invariant.h>

namespace
{
class validate_goto_modelt
{
public:
  using function_mapt = goto_functionst::function_mapt;

  validate_goto_modelt(
    const goto_functionst &goto_functions,
    const validation_modet vm)
    : vm{vm}, function_map{goto_functions.function_map}
  {
  }

  void
  do_goto_program_checks(goto_model_validation_optionst validation_options);

private:
  /// Check the goto_program has an entry point
  ///
  /// NB goto-cc -c will generate goto-programs without entry-points
  /// until they are linked.
  void entry_point_exists();

  /// Check that no functions calls via function pointer are present
  void function_pointer_calls_removed();

  /// Check returns have been removed
  ///
  /// NB Calls via function pointer must have been removed already when
  /// removing returns, thus enabling this check also should enable the check
  /// that all calls via function pointer have been removed
  ///
  /// Sub-checks are:
  /// - no return statements in any of the functions
  /// - lhs of every \ref code_function_callt instruction is nil
  /// - all return types are void (of both calls and functions themselves)
  void check_returns_removed();

  /// Check that for all
  /// 1. functions that are called or
  /// 2. functions of which the address is taken,
  /// a corresponding entry exists in the function_map
  void check_called_functions();

  /// Check that goto-programs that have a body end with an END_FUNCTION
  /// instruction.
  ///
  /// NB functions that are only declared, and not used will not appear in the
  /// function map. Functions that are declared only and used to e.g.
  /// initialise a function pointer will have no body.
  void check_last_instruction();

  /// Check both
  /// 1. every instruction \"code\" field, has a non nil source location"
  /// 2. every instruction source_location field is nil
  /// NB this check is not expected to pass until setting these locations is
  /// patched up.
  void check_sourcecode_location();

  const validation_modet vm;
  const function_mapt &function_map;
  const goto_model_validation_optionst validation_options;
};
} // namespace

void validate_goto_modelt::do_goto_program_checks(
  goto_model_validation_optionst validation_options)
{
  if(validation_options.entry_point_exists)
    entry_point_exists();

  if(validation_options.check_last_instruction)
    check_last_instruction();

  /// NB function pointer calls must have been removed before removing
  /// returns - so 'check_returns_removed' also enables
  // 'function_pointer_calls_removed'
  if(
    validation_options.function_pointer_calls_removed ||
    validation_options.check_returns_removed)
    function_pointer_calls_removed();

  if(validation_options.check_returns_removed)
    check_returns_removed();

  if(validation_options.check_called_functions)
    check_called_functions();

  if(validation_options.check_sourcecode_location)
    check_sourcecode_location();
}

void validate_goto_modelt::entry_point_exists()
{
  DATA_CHECK(
    vm,
    function_map.find(goto_functionst::entry_point()) != function_map.end(),
    "an entry point must exist");
}

void validate_goto_modelt::function_pointer_calls_removed()
{
  for(const auto &fun : function_map)
  {
    for(auto &instr : fun.second.body.instructions)
    {
      if(instr.is_function_call())
      {
        const code_function_callt &function_call =
          to_code_function_call(instr.code);
        DATA_CHECK(
          vm,
          function_call.function().id() == ID_symbol,
          "no calls via function pointer should be present");
      }
    }
  }
}

void validate_goto_modelt::check_returns_removed()
{
  for(const auto &fun : function_map)
  {
    const goto_functiont &goto_function = fun.second;
    DATA_CHECK(
      vm,
      goto_function.type.return_type().id() == ID_empty,
      "functions must have empty return type");

    for(const auto &instr : goto_function.body.instructions)
    {
      DATA_CHECK(
        vm, !instr.is_return(), "no return instructions should be present");

      if(instr.is_function_call())
      {
        const auto &function_call = to_code_function_call(instr.code);
        DATA_CHECK(
          vm,
          function_call.lhs().is_nil(),
          "function call return should be nil");

        const auto &callee = to_code_type(function_call.function().type());
        DATA_CHECK(vm, callee.return_type().id() == ID_empty, "");
      }
    }
  }
}

void validate_goto_modelt::check_called_functions()
{
  class test_for_function_addresst : public const_expr_visitort
  {
  public:
    test_for_function_addresst(
      const function_mapt &function_map,
      const validation_modet &vm)
      : function_map{function_map}, vm{vm}
    {
    }
    void operator()(const exprt &expr) override
    {
      if(expr.id() == ID_address_of)
      {
        const auto &pointee = to_address_of_expr(expr).object();
        if(pointee.id() == ID_symbol)
        {
          const auto &identifier = to_symbol_expr(pointee).get_identifier();
          DATA_CHECK(
            vm,
            function_map.find(identifier) != function_map.end(),
            "every function whose address is taken must be in the "
            "function map");
        }
      }
    }

  private:
    const function_mapt &function_map;
    const validation_modet &vm;
  };
  test_for_function_addresst test_for_function_address(function_map, vm);

  for(const auto &fun : function_map)
  {
    for(auto &instr : fun.second.body.instructions)
    {
      // check functions that are called
      if(instr.is_function_call())
      {
        const auto &function_call = to_code_function_call(instr.code);
        const irep_idt &identifier =
          to_symbol_expr(function_call.function()).get_identifier();

        DATA_CHECK(
          vm,
          function_map.find(identifier) != function_map.end(),
          "every function call callee must be in the function map");
      }

      // check functions of which the address is taken
      const exprt &src{instr.code};
      src.visit(test_for_function_address);
    }
  }
}

void validate_goto_modelt::check_last_instruction()
{
  for(const auto &fun : function_map)
  {
    if(fun.second.body_available())
    {
      DATA_CHECK(
        vm,
        fun.second.body.instructions.back().is_end_function(),
        "last instruction should be of end function type");
    }
  }
}

void validate_goto_modelt::check_sourcecode_location()
{
  // Assumption is that if every instruction is checked - then there is no
  // need to check targets.
  for(const auto &fun : function_map)
  {
    for(auto &instr : fun.second.body.instructions)
    {
      DATA_CHECK(
        vm,
        instr.code.source_location().is_not_nil(),
        "each instruction \"code\" field, must have non nil source location");

      DATA_CHECK(
        vm,
        instr.source_location.is_not_nil(),
        "each instruction source location must not be nil");
    }
  }
}

void validate_goto_model(
  const goto_functionst &goto_functions,
  const validation_modet vm,
  const goto_model_validation_optionst validation_options)
{
  validate_goto_modelt{goto_functions, vm}.do_goto_program_checks(
    validation_options);
}
