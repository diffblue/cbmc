/*******************************************************************\

Module: Interval Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interval Analysis -- implements the functionality necessary for performing
/// abstract interpretation over interval domain for goto programs. The result
/// of the analysis is an instrumented program.

#include "interval_analysis.h"

#include <util/find_symbols.h>

#include "interval_domain.h"

/// Instruments all "post-branch" instructions with assumptions about variable
/// intervals. For each such instruction, the function evaluates all variables
/// referenced within the input goto_function as intervals, transforms these
/// intervals into expressions and instruments the instruction with their
/// conjunction.
/// Example: interval [5,10] (for variable "x") translates into conjunction
/// 5 <= x && x <= 10.
/// \param interval_analysis Interval domain to be used for variable evaluation.
/// \param [out] goto_function: Goto function to be analysed and instrumented.
void instrument_intervals(
  const ait<interval_domaint> &interval_analysis,
  goto_functionst::goto_functiont &goto_function)
{
  std::set<symbol_exprt> symbols;

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    find_symbols(i_it->code, symbols);
    find_symbols(i_it->guard, symbols);
  }

  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it==goto_function.body.instructions.begin())
    {
      // first instruction, we instrument
    }
    else
    {
      goto_programt::const_targett previous=i_it;
      previous--;
      if(previous->is_goto() && !previous->guard.is_true())
      {
        // we follow a branch, instrument
      }
      else if(previous->is_function_call() && !previous->guard.is_true())
      {
        // we follow a function call, instrument
      }
      else if(i_it->is_target() || i_it->is_function_call())
      {
        // we are a target or a function call, instrument
      }
      else
        continue; // don't instrument
    }

    const interval_domaint &d=interval_analysis[i_it];

    exprt::operandst assertion;

    for(const auto &symbol_expr : symbols)
    {
      exprt tmp=d.make_expression(symbol_expr);
      if(!tmp.is_true())
        assertion.push_back(tmp);
    }

    if(!assertion.empty())
    {
      goto_programt::targett t=i_it;
      goto_function.body.insert_before_swap(i_it);
      t->make_assumption(conjunction(assertion));
      i_it++; // goes to original instruction
      t->source_location=i_it->source_location;
      t->function=i_it->function;
    }
  }
}

/// Initialises the abstract interpretation over interval domain and
/// instruments instructions using interval assumptions.
/// \param [out] goto_model: Input code as goto_model.
void interval_analysis(goto_modelt &goto_model)
{
  ait<interval_domaint> interval_analysis;

  const namespacet ns(goto_model.symbol_table);
  interval_analysis(goto_model.goto_functions, ns);

  Forall_goto_functions(f_it, goto_model.goto_functions)
    instrument_intervals(interval_analysis, f_it->second);
}
