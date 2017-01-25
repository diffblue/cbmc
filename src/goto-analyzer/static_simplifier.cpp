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
  unsigned simplify_guard(goto_programt::instructionst::iterator &i_it);
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
  status() << "Performing analysis" << eom;
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

Function: static_simplifiert<analyzerT>::simplify_guard

  Inputs: An iterator pointing to an instruction.

 Outputs: 1 if simplified, 0 if not.

 Purpose: Simplifies the instruction's guard using the information in
          the abstract domain.

\*******************************************************************/

template<class analyzerT>
unsigned static_simplifiert<analyzerT>::simplify_guard(
  goto_programt::instructionst::iterator &i_it)
{
  exprt simplified=domain[i_it].domain_simplify(i_it->guard, ns);
  unsigned return_value=(simplified==i_it->guard)?0:1;
  i_it->guard=simplified;
  return return_value;
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
    unsigned asserts;
    unsigned assumes;
    unsigned gotos;
    unsigned assigns;
    unsigned function_calls;
  };

  counterst simplified={0, 0, 0, 0, 0};
  counterst unmodified={0, 0, 0, 0, 0};

  Forall_goto_functions(f_it, goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert())
      {
        unsigned result=simplify_guard(i_it);
        simplified.asserts+=result;
        unmodified.asserts+=(1-result);
      }
      else if(i_it->is_assume())
      {
        unsigned result=simplify_guard(i_it);
        simplified.assumes+=result;
        unmodified.assumes+=(1-result);
      }
      else if(i_it->is_goto())
      {
        unsigned result=simplify_guard(i_it);
        simplified.gotos+=result;
        unmodified.gotos+=(1-result);
      }
      else if(i_it->is_assign())
      {
        code_assignt assign(to_code_assign(i_it->code));

        /*
        Simplification needs to be aware of which side of the
        expression it is handling as:
        <i=0, j=1>  i=j
        should simplify to i=1, not to 0=1.
        */

        exprt simp_lhs=domain[i_it].domain_simplify(assign.lhs(), ns, true);
        exprt simp_rhs=domain[i_it].domain_simplify(assign.rhs(), ns, false);

        unsigned result=(simp_lhs==assign.lhs() &&
                         simp_rhs==assign.rhs())?0:1;

        simplified.assigns+=result;
        unmodified.assigns+=(1-result);

        assign.lhs()=simp_lhs;
        assign.rhs()=simp_rhs;
        i_it->code=assign;
      }
      else if(i_it->is_function_call())
      {
        unsigned result=0;
        code_function_callt fcall(to_code_function_call(i_it->code));

        exprt new_function=domain[i_it].domain_simplify(fcall.function(), ns);
        result|=(new_function==fcall.function()) ? 0 : 1;
        fcall.function()=new_function;

        exprt::operandst &args=fcall.arguments();

        for(exprt::operandst::iterator o_it=args.begin();
            o_it!=args.end();
            ++o_it)
        {
          exprt new_arg=domain[i_it].domain_simplify(*o_it, ns);
          result|=(new_arg==*o_it) ? 0 : 1;
          *o_it=new_arg;
        }

        i_it->code=fcall;

        simplified.function_calls+=result;
        unmodified.function_calls+=(1-result);
      }
    }
  }

  // Make sure the references are correct.
  goto_functions.update();

  status() << "SIMPLIFIED: "
           << " assert: " << simplified.asserts
           << ", assume: " << simplified.assumes
           << ", goto: " << simplified.gotos
           << ", assigns: " << simplified.assigns
           << ", function calls: " << simplified.function_calls
           << "\n"
           << "UNMODIFIED: "
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

  messaget m(message_handler);
  m.status() << "Task / Interpreter / Domain combination not supported"
             << messaget::eom;

  return true;
}
