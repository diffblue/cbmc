/*******************************************************************\

Module: goto_statistics.h

Author: Marek Trtik

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_STATISTICS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_STATISTICS_H

/// \file goto-programs/goto_statistics.h
/// \brief Computation of statistical properties of a GOTO program.

#include <cstddef>
#include <util/json.h>
#include "goto_model.h"

class goto_statisticst
{
public:
  goto_statisticst():
    num_functions(0UL),
    num_instructions(0UL),
    num_user_variables(0UL),
    num_auxiliary_variables(0UL),
    num_function_calls(0UL),
    num_unconditional_gotos(0UL),
    num_conditional_gotos(0UL),
    num_assumptions(0UL),
    num_assertions(0UL),
    num_loops(0UL)
  {}

  void extend(
    const goto_functionst &functions,
    const symbol_tablet &table);

  void extend(const goto_modelt &model)
  {
    extend(model.goto_functions, model.symbol_table);
  }

  void clear() { *this=goto_statisticst(); }

  std::size_t get_num_functions() const
  {
    return num_functions;
  }

  std::size_t get_num_instructions() const
  {
    return num_instructions;
  }

  std::size_t get_num_user_variables() const
  {
    return num_user_variables;
  }

  std::size_t get_num_auxiliary_variables() const
  {
    return num_auxiliary_variables;
  }

  std::size_t get_num_function_calls() const
  {
    return num_function_calls;
  }

  std::size_t get_num_unconditional_gotos() const
  {
    return num_unconditional_gotos;
  }

  std::size_t get_num_conditional_gotos() const
  {
    return num_conditional_gotos;
  }

  std::size_t get_num_loops() const
  {
    return num_loops;
  }

private:
  std::size_t num_functions;
  std::size_t num_instructions;
  std::size_t num_user_variables;
  std::size_t num_auxiliary_variables;
  std::size_t num_function_calls;
  std::size_t num_unconditional_gotos;
  std::size_t num_conditional_gotos;
  std::size_t num_assumptions;
  std::size_t num_assertions;
  std::size_t num_loops;
};

jsont to_json(const goto_statisticst &stats);

#endif

