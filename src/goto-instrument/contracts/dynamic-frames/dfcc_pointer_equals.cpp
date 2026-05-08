/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: Jan 2025

\*******************************************************************/

#include "dfcc_pointer_equals.h"

#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_iterator.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/replace_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/suffix.h>
#include <util/symbol.h>

#include "dfcc_cfg_info.h"
#include "dfcc_library.h"

dfcc_pointer_equalst::dfcc_pointer_equalst(
  dfcc_libraryt &library,
  message_handlert &message_handler)
  : library(library), message_handler(message_handler), log(message_handler)
{
}

void dfcc_pointer_equalst::rewrite_calls(
  goto_programt &program,
  dfcc_cfg_infot cfg_info)
{
  rewrite_calls(
    program,
    program.instructions.begin(),
    program.instructions.end(),
    cfg_info);
}

void dfcc_pointer_equalst::rewrite_calls(
  goto_programt &program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  dfcc_cfg_infot cfg_info)
{
  auto &target = first_instruction;
  while(target != last_instruction)
  {
    if(target->is_function_call())
    {
      const auto &function = target->call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &fun_name = to_symbol_expr(function).identifier();

        if(has_prefix(id2string(fun_name), CPROVER_PREFIX "pointer_equals"))
        {
          // add address on first operand
          target->call_arguments()[0] =
            address_of_exprt(target->call_arguments()[0]);

          // fix the function name.
          to_symbol_expr(target->call_function())
            .identifier(
              library.dfcc_fun_symbol[dfcc_funt::POINTER_EQUALS].name);

          // pass the may_fail flag
          if(function.source_location().get_bool("no_fail"))
            target->call_arguments().push_back(false_exprt());
          else
            target->call_arguments().push_back(true_exprt());

          // pass the write_set
          target->call_arguments().push_back(cfg_info.get_write_set(target));
        }
      }
    }
    target++;
  }
}

class pointer_equality_visitort : public expr_visitort
{
private:
  std::vector<exprt *> equality_exprs_to_transform;

public:
  void visit_expr(exprt &expr)
  {
    if(expr.id() == ID_equal)
    {
      const equal_exprt &equal_expr = to_equal_expr(expr);

      // Check if both operands are pointers
      if(
        equal_expr.lhs().type().id() == ID_pointer &&
        equal_expr.rhs().type().id() == ID_pointer)
      {
        equality_exprs_to_transform.push_back(&expr);
      }
    }
  }

  // Apply the transformations after visiting
  void transform()
  {
    const code_typet pointer_equals_type(
      {code_typet::parametert(pointer_type(void_type())),
       code_typet::parametert(pointer_type(void_type()))},
      bool_typet());

    symbol_exprt pointer_equals(
      CPROVER_PREFIX "pointer_equals", pointer_equals_type);

    for(exprt *expr_ptr : equality_exprs_to_transform)
    {
      const equal_exprt &equal_expr = to_equal_expr(*expr_ptr);

      // Create the function call to __CPROVER_pointer_equals
      // Add the original equality operands as arguments
      side_effect_expr_function_callt result(
        pointer_equals,
        {equal_expr.lhs(), equal_expr.rhs()},
        bool_typet(),
        equal_expr.source_location());

      result.arguments().push_back(equal_expr.lhs());
      result.arguments().push_back(equal_expr.rhs());

      // Set the type of the function call
      result.type() = bool_typet();

      // Replace the original expression
      *expr_ptr = result;
    }
  }
};

// Usage function
void rewrite_equal_exprt_to_pointer_equals(exprt &expr)
{
  pointer_equality_visitort visitor;

  // First collect all equality expressions
  expr.visit(visitor);

  // Then transform them
  visitor.transform();
}
