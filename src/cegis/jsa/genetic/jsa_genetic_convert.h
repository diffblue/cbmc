/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_GENETIC_JSA_GENETIC_CONVERT_H
#define CPROVER_CEGIS_JSA_GENETIC_JSA_GENETIC_CONVERT_H

#include <util/message.h>

/**
 * @brief
 *
 * @details
 */
class jsa_genetic_convertt
{
  const class jsa_symex_learnt &learn;
public:
  typedef class jsa_solutiont candidatet;
  typedef class jsa_genetic_solutiont individualt;

  /**
   * @brief
   *
   * @details
   *
   * @param learn
   */
  explicit jsa_genetic_convertt(const jsa_symex_learnt &learn);

  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   * @param individual
   */
  void convert(candidatet &candidate, const individualt &individual) const;

  /**
   * @brief
   *
   * @details
   *
   * @param candidate
   * @param os
   */
  void show(messaget::mstreamt &os, const candidatet &candidate) const;
};

#endif // CPROVER_CEGIS_JSA_GENETIC_JSA_GENETIC_CONVERT_H
