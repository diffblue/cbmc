/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_JSA_SOURCE_PROVIDER_H_
#define CEGIS_GENETIC_JSA_SOURCE_PROVIDER_H_

#include <string>

/**
 * @brief
 *
 * @details
 */
class jsa_source_providert
{
  const class optionst &options;
  class jsa_symex_learnt &lcfg;
  std::string source;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param lcfg
   */
  jsa_source_providert(const optionst &options, jsa_symex_learnt &lcfg);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const std::string &operator()();
};

#endif /* CEGIS_GENETIC_JSA_SOURCE_PROVIDER_H_ */
