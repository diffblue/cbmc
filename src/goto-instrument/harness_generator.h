/*******************************************************************\

Module: Harness generator

Author: elizabeth.polgreen@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// harness generator

#ifndef CPROVER_GOTO_INSTRUMENT_HARNESS_GENERATOR_H
#define CPROVER_GOTO_INSTRUMENT_HARNESS_GENERATOR_H

#include <pointer-analysis/show_value_sets.h>
#include <pointer-analysis/value_set_analysis.h>
#include <goto-programs/goto_model.h>

/// \brief The harness generator command line option takes
/// as argument the name of a function. We read the function
/// arguments and output the possible assignments to the
/// function arguments when the function is called.
///
/// This is created with future work in mind: eventually we
/// wish to generate C code or goto-programs that initialise the
/// arguments of the function, allowing CBMC to be run starting
/// from functions that take pointers as arguments
class harness_generatort
{
public:
  explicit harness_generatort(
      const goto_modelt & _goto_model,
      irep_idt _harness_location,
      message_handlert &_msg)
  {
    build_harness(_goto_model, _harness_location, _msg);
  }

  void build_harness(const goto_modelt &,
      irep_idt function_to_harness,
      message_handlert &);
};

#endif /* CPROVER_GOTO_INSTRUMENT_HARNESS_GENERATOR_H */
