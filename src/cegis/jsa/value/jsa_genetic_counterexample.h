/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_GENETIC_COUNTEREXAMPLE_H_
#define CEGIS_JSA_GENETIC_COUNTEREXAMPLE_H_

#include <deque>
#include <map>

#include <cegis/jsa/value/jsa_genetic_synthesis.h>

/**
 * @brief
 *
 * @details
 */
class jsa_genetic_counterexamplet
{
public:
  __CPROVER_jsa_abstract_heapt init_org;
  __CPROVER_jsa_abstract_heapt inductive_org;
  __CPROVER_jsa_abstract_heapt inductive_body_result;

  typedef std::map<const irep_idt, __CPROVER_jsa_word_t> assignments_per_program_locationt;
  assignments_per_program_locationt assignments_per_program_location;
};

#endif /* CEGIS_JSA_GENETIC_COUNTEREXAMPLE_H_ */
