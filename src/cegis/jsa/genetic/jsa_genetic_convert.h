/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_GENETIC_CONVERT_H_
#define CEGIS_JSA_GENETIC_CONVERT_H_

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
  jsa_genetic_convertt(const jsa_symex_learnt &learn);

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

#endif /* CEGIS_JSA_GENETIC_CONVERT_H_ */
