/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <fstream>

#include <analyses/interval_domain.h>
#include <analyses/constant_propagator.h>

#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>
#include <goto-programs/write_goto_binary.h>

#include "static_simplifier.h"

template<class analyzerT>
class static_simplifiert:public messaget
{
public:
  static_simplifiert(
    goto_modelt &_goto_model,
    const optionst &_options,
    message_handlert &_message_handler,
    std::ostream &_out):
    messaget(_message_handler),
    goto_functions(_goto_model.goto_functions),
    ns(_goto_model.symbol_table),
    options(_options),
    out(_out)
  {
  }

  bool operator()(void);

protected:
  goto_functionst &goto_functions;
  const namespacet ns;
  const optionst &options;
  std::ostream &out;

  // analyses
  analyzerT domain;

  void simplify_program(void);
  bool simplify_guard(goto_programt::instructionst::iterator &i_it);
};

/*******************************************************************\

Function: static_simplifiert<analyzerT>::operator()

  Inputs: None.

 Outputs: false on success, true on failure.

 Purpose: Run the analysis, check the assertions and report in the
          correct format.

\*******************************************************************/

template<class analyzerT>
bool static_simplifiert<analyzerT>::operator()(void)
{
  status() << "Computing abstract states" << eom;
  domain(goto_functions, ns);

  status() << "Simplifying program" << eom;
  simplify_program();

  // Remove obviously unreachable things and (now) unconditional branches
  if(options.get_bool_option("simplify-slicing"))
  {
    status() << "Removing unreachable instructions" << eom;

    remove_skip(goto_functions);  // Removes goto false
    goto_functions.update();

    remove_unreachable(goto_functions);  // Convert unreachable to skips
    goto_functions.update();

    remove_skip(goto_functions);  // Remove all of the new skips
    goto_functions.update();
  }

  status() << "Writing goto binary" << eom;
  return write_goto_binary(out, ns.get_symbol_table(), goto_functions);
}

/*******************************************************************\

Function: static_simplifiert<analyzerT>::simplify_program

  Inputs: None.

 Outputs: None.

 Purpose: Simplifies the program using the information in the abstract
          domain.

\*******************************************************************/

template<class analyzerT>
void static_simplifiert<analyzerT>::simplify_program()
{
  struct counterst
  {
    counterst() :
      asserts(0),
      assumes(0),
      gotos(0),
      assigns(0),
      function_calls(0) {}

    unsigned asserts;
    unsigned assumes;
    unsigned gotos;
    unsigned assigns;
    unsigned function_calls;
  };

  counterst simplified;
  counterst unmodified;

  Forall_goto_functions(f_it, goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert())
      {
        bool unchanged=domain[i_it].ai_simplify(i_it->guard, ns);

        if(unchanged)
          unmodified.asserts++;
        else
          simplified.asserts++;
      }
      else if(i_it->is_assume())
      {
        bool unchanged=domain[i_it].ai_simplify(i_it->guard, ns);

        if(unchanged)
          unmodified.assumes++;
        else
          simplified.assumes++;
      }
      else if(i_it->is_goto())
      {
        bool unchanged=domain[i_it].ai_simplify(i_it->guard, ns);

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

        bool unchanged_lhs=
          domain[i_it].ai_simplify_lhs(assign.lhs(), ns);

        bool unchanged_rhs=
          domain[i_it].ai_simplify(assign.rhs(), ns);

        if(unchanged_lhs && unchanged_rhs)
          unmodified.assigns++;
        else
          simplified.assigns++;
      }
      else if(i_it->is_function_call())
      {
        code_function_callt &fcall=to_code_function_call(i_it->code);

        bool unchanged=domain[i_it].ai_simplify(fcall.function(), ns);

        exprt::operandst &args=fcall.arguments();

        for(auto &o : args)
          unchanged&=domain[i_it].ai_simplify(o, ns);

        if(unchanged)
          unmodified.function_calls++;
        else
          simplified.function_calls++;
      }
    }
  }

  // Make sure the references are correct.
  goto_functions.update();

  status() << "Simplified: "
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
           << eom;

  return;
}

/*******************************************************************\

Function: static_simplifier

  Inputs: The goto_model to analyze and simplify, options giving the
          domain, the message handler and output stream.

 Outputs: The simplified goto binary via out.

 Purpose: Runs the analyzer, simplifies and then outputs.

\*******************************************************************/

bool static_simplifier(
  goto_modelt &goto_model,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  messaget m(message_handler);
  m.status() << "Selecting abstract domain" << messaget::eom;

  if(options.get_bool_option("flow-sensitive"))
  {
    if(options.get_bool_option("constants"))
      return static_simplifiert<ait<constant_propagator_domaint>>
        (goto_model, options, message_handler, out)();

    else if(options.get_bool_option("intervals"))
      return static_simplifiert<ait<interval_domaint>>
        (goto_model, options, message_handler, out)();

    // else if(options.get_bool_option("non-null"))
    //   return static_simplifiert<ait<non_null_domaint> >
    //     (goto_model, options, message_handler, out)();
  }
  else if(options.get_bool_option("concurrent"))
  {
    // Constant and interval don't have merge_shared yet
#if 0
    if(options.get_bool_option("constants"))
      return static_simplifiert<
        concurrency_aware_ait<constant_propagator_domaint>>
          (goto_model, options, message_handler, out)();

    else if(options.get_bool_option("intervals"))
      return static_simplifiert<concurrency_aware_ait<interval_domaint> >
        (goto_model, options, message_handler, out)();

    // else if(options.get_bool_option("non-null"))
    //   return static_simplifiert<concurrency_aware_ait<non_null_domaint> >
    //     (goto_model, options, message_handler, out)();
#endif
  }

  m.status() << "Task / Interpreter / Domain combination not supported"
             << messaget::eom;

  return true;
}
