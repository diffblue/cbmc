/*******************************************************************\

Module: Output of the program (SSA) constraints

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Output of the program (SSA) constraints

#include "show_program.h"

#include <iostream>

#include <goto-symex/symex_target_equation.h>

#include <langapi/language_util.h>

void show_program(const namespacet &ns, const symex_target_equationt &equation)
{
  unsigned count = 1;

  std::cout << "\n"
            << "Program constraints:"
            << "\n";

  for(const auto &step : equation.SSA_steps)
  {
    std::cout << "// " << step.source.pc->location_number << " ";
    std::cout << step.source.pc->source_location.as_string() << "\n";
    const irep_idt &function = step.source.function;

    if(step.is_assignment())
    {
      std::string string_value = from_expr(ns, function, step.cond_expr);
      std::cout << "(" << count << ") " << string_value << "\n";

      if(!step.guard.is_true())
      {
        std::string string_value = from_expr(ns, function, step.guard);
        std::cout << std::string(std::to_string(count).size() + 3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
    else if(step.is_assert())
    {
      std::string string_value = from_expr(ns, function, step.cond_expr);
      std::cout << "(" << count << ") ASSERT(" << string_value << ") "
                << "\n";

      if(!step.guard.is_true())
      {
        std::string string_value = from_expr(ns, function, step.guard);
        std::cout << std::string(std::to_string(count).size() + 3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
    else if(step.is_assume())
    {
      std::string string_value = from_expr(ns, function, step.cond_expr);
      std::cout << "(" << count << ") ASSUME(" << string_value << ") "
                << "\n";

      if(!step.guard.is_true())
      {
        std::string string_value = from_expr(ns, function, step.guard);
        std::cout << std::string(std::to_string(count).size() + 3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
    else if(step.is_constraint())
    {
      std::string string_value = from_expr(ns, function, step.cond_expr);
      std::cout << "(" << count << ") CONSTRAINT(" << string_value << ") "
                << "\n";

      count++;
    }
    else if(step.is_shared_read() || step.is_shared_write())
    {
      std::string string_value = from_expr(ns, function, step.ssa_lhs);
      std::cout << "(" << count << ") SHARED_"
                << (step.is_shared_write() ? "WRITE" : "READ") << "("
                << string_value << ")\n";

      if(!step.guard.is_true())
      {
        std::string string_value = from_expr(ns, function, step.guard);
        std::cout << std::string(std::to_string(count).size() + 3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
  }
}
