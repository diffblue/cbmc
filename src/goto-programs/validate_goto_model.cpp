/*******************************************************************\
Module: Validate Goto Programs

Author: Diffblue

Date: Oct 2018

\*******************************************************************/

#include "validate_goto_model.h"

#include <set>

#include <util/pointer_expr.h>

#include "goto_functions.h"

namespace
{
class validate_goto_modelt
{
public:
  using function_mapt = goto_functionst::function_mapt;

  validate_goto_modelt(
    const goto_functionst &goto_functions,
    const validation_modet vm,
    const goto_model_validation_optionst goto_model_validation_options);

private:
  /// Check the goto_program has an entry point
  ///
  /// goto-cc -c will generate goto-programs without entry-points
  /// until they are linked.
  void entry_point_exists();

  /// Check that no function calls via function pointer are present
  void function_pointer_calls_removed();

  /// Check that for all:
  /// -# functions that are called or
  /// -# functions of which the address is taken
  /// .
  /// a corresponding entry exists in the function_map
  ///
  /// Functions that are only declared and not used will not appear in the
  /// function map. Functions that are declared only and used to e.g.
  /// initialise a function pointer will have no body.
  void check_called_functions();

  const validation_modet vm;
  const function_mapt &function_map;
};

validate_goto_modelt::validate_goto_modelt(
  const goto_functionst &goto_functions,
  const validation_modet vm,
  const goto_model_validation_optionst validation_options)
  : vm{vm}, function_map{goto_functions.function_map}
{
  if(validation_options.entry_point_exists)
    entry_point_exists();

  if(validation_options.function_pointer_calls_removed)
  {
    function_pointer_calls_removed();
  }

  if(validation_options.check_called_functions)
    check_called_functions();
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
    for(const auto &instr : fun.second.body.instructions)
    {
      if(instr.is_function_call())
      {
        DATA_CHECK(
          vm,
          instr.call_function().id() == ID_symbol,
          "no calls via function pointer should be present");
      }
    }
  }
}

void validate_goto_modelt::check_called_functions()
{
  auto test_for_function_address =
    [this](const exprt &expr) {
      if(expr.id() == ID_address_of)
      {
        const auto &pointee = to_address_of_expr(expr).object();

        if(pointee.id() == ID_symbol && pointee.type().id() == ID_code)
        {
          const auto &identifier = to_symbol_expr(pointee).get_identifier();

          DATA_CHECK(
            vm,
            function_map.find(identifier) != function_map.end(),
            "every function whose address is taken must be in the "
            "function map");
        }
      }
    };

  for(const auto &fun : function_map)
  {
    for(const auto &instr : fun.second.body.instructions)
    {
      // check functions that are called
      if(instr.is_function_call())
      {
        const irep_idt &identifier =
          to_symbol_expr(instr.call_function()).get_identifier();

        DATA_CHECK(
          vm,
          function_map.find(identifier) != function_map.end(),
          "every function call callee must be in the function map");
      }

      // check functions of which the address is taken
      const auto &src = static_cast<const exprt &>(instr.code());
      src.visit_pre(test_for_function_address);
    }
  }
}

} // namespace

void validate_goto_model(
  const goto_functionst &goto_functions,
  const validation_modet vm,
  const goto_model_validation_optionst validation_options)
{
  validate_goto_modelt{goto_functions, vm, validation_options};
}
