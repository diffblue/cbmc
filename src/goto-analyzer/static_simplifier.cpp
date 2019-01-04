/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include "static_simplifier.h"

#include <util/message.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>
#include <goto-programs/write_goto_binary.h>

#include <analyses/ai.h>

/// Simplifies the program using the information in the abstract domain.
/// \param goto_model: the program analyzed
/// \param ai: the abstract interpreter after it has been run to fix point
/// \param options: the parsed user options
/// \param message_handler: the system message handler
/// \param out: output stream for the simplified program
/// \return false on success with the domain printed to out
bool static_simplifier(
  goto_modelt &goto_model,
  const ai_baset &ai,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  struct counterst
  {
    counterst() :
      asserts(0),
      assumes(0),
      gotos(0),
      assigns(0),
      function_calls(0) {}

    std::size_t asserts;
    std::size_t assumes;
    std::size_t gotos;
    std::size_t assigns;
    std::size_t function_calls;
  };

  counterst simplified;
  counterst unmodified;

  namespacet ns(goto_model.symbol_table);

  messaget m(message_handler);
  m.status() << "Simplifying program" << messaget::eom;

  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      m.progress() << "Simplifying " << f_it->first << messaget::eom;

      if(i_it->is_assert())
      {
        bool unchanged =
          ai.abstract_state_before(i_it)->ai_simplify(i_it->guard, ns);

        if(unchanged)
          unmodified.asserts++;
        else
          simplified.asserts++;
      }
      else if(i_it->is_assume())
      {
        bool unchanged =
          ai.abstract_state_before(i_it)->ai_simplify(i_it->guard, ns);

        if(unchanged)
          unmodified.assumes++;
        else
          simplified.assumes++;
      }
      else if(i_it->is_goto())
      {
        bool unchanged =
          ai.abstract_state_before(i_it)->ai_simplify(i_it->guard, ns);

        if(unchanged)
          unmodified.gotos++;
        else
          simplified.gotos++;
      }
      else if(i_it->is_assign())
      {
        code_assignt &assign=to_code_assign(i_it->code);

        // Simplification needs to be aware of which side of the
        // expression it is handling as:
        // <i=0, j=1>  i=j
        // should simplify to i=1, not to 0=1.

        bool unchanged_lhs =
          ai.abstract_state_before(i_it)->ai_simplify_lhs(assign.lhs(), ns);

        bool unchanged_rhs =
          ai.abstract_state_before(i_it)->ai_simplify(assign.rhs(), ns);

        if(unchanged_lhs && unchanged_rhs)
          unmodified.assigns++;
        else
          simplified.assigns++;
      }
      else if(i_it->is_function_call())
      {
        code_function_callt &fcall=to_code_function_call(i_it->code);

        bool unchanged =
          ai.abstract_state_before(i_it)->ai_simplify(fcall.function(), ns);

        exprt::operandst &args=fcall.arguments();

        for(auto &o : args)
          unchanged &= ai.abstract_state_before(i_it)->ai_simplify(o, ns);

        if(unchanged)
          unmodified.function_calls++;
        else
          simplified.function_calls++;
      }
    }
  }

  // Make sure the references are correct.
  goto_model.goto_functions.update();

  m.status() << "Simplified: "
             << " assert: " << simplified.asserts
             << ", assume: " << simplified.assumes
             << ", goto: " << simplified.gotos
             << ", assigns: " << simplified.assigns
             << ", function calls: " << simplified.function_calls
             << "\n"
             << "Unmodified: "
             << " assert: " << unmodified.asserts
             << ", assume: " << unmodified.assumes
             << ", goto: " << unmodified.gotos
             << ", assigns: " << unmodified.assigns
             << ", function calls: " << unmodified.function_calls
             << messaget::eom;


  // Remove obviously unreachable things and (now) unconditional branches
  if(options.get_bool_option("simplify-slicing"))
  {
    m.status() << "Removing unreachable instructions" << messaget::eom;

    // Removes goto false
    remove_skip(goto_model);

    // Convert unreachable to skips
    remove_unreachable(goto_model.goto_functions);

    // Remove all of the new skips
    remove_skip(goto_model);
  }

  // restore return types before writing the binary
  restore_returns(goto_model);
  goto_model.goto_functions.update();

  m.status() << "Writing goto binary" << messaget::eom;
  return write_goto_binary(out,
                           ns.get_symbol_table(),
                           goto_model.goto_functions);
}
