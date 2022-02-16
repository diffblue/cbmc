/*******************************************************************\

Module: Static initializer call lifting

Author: Diffblue Ltd.

\*******************************************************************/

/// file Static initializer call lifting

#include "lift_clinit_calls.h"

#include <java_bytecode/java_static_initializers.h>

#include <goto-programs/goto_instruction_code.h>

#include <util/expr_iterator.h>

#include <algorithm>

codet lift_clinit_calls(codet input)
{
  // 1. Gather any clinit calls present in `input`:
  std::vector<symbol_exprt> clinit_wrappers_called;

  for(auto it = input.depth_begin(), itend = input.depth_end(); it != itend;
      ++it)
  {
    if(const auto code = expr_try_dynamic_cast<codet>(*it))
    {
      if(code->get_statement() == ID_function_call)
      {
        if(
          const auto callee = expr_try_dynamic_cast<symbol_exprt>(
            to_code_function_call(*code).function()))
        {
          if(is_clinit_wrapper_function(callee->get_identifier()))
          {
            clinit_wrappers_called.push_back(*callee);
            // Replace call with skip:
            it.mutate() = code_skipt();
          }
        }
      }
    }
  }

  if(clinit_wrappers_called.empty())
    return input;

  // 2. Unique, such that each clinit method is only called once:
  std::sort(clinit_wrappers_called.begin(), clinit_wrappers_called.end());
  auto delete_after =
    std::unique(clinit_wrappers_called.begin(), clinit_wrappers_called.end());
  clinit_wrappers_called.erase(delete_after, clinit_wrappers_called.end());

  // 3. Lift static init calls to top of function:
  code_blockt result;
  for(const auto &callee : clinit_wrappers_called)
  {
    code_function_callt new_call(callee);
    // Nuke the source location, now that the call doesn't really relate to any
    // one particular line:
    new_call.function().drop_source_location();
    result.add(new_call);
  }

  result.add(std::move(input));

  return std::move(result);
}
