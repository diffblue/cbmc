/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_INVARIANT_BODY_PROVIDER_H
#define CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_INVARIANT_BODY_PROVIDER_H

#include <cegis/invariant/options/invariant_program.h>

/**
 * @brief
 *
 * @details
 */
template<class inv_progt>
class invariant_exec_body_providert
{
  const std::string exec_func_name;
  const inv_progt &original_prog;
  inv_progt prog;
  bool initialised;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param exec_func_name
   * @param prog
   */
  invariant_exec_body_providert(const std::string &exec_func_name,
      const inv_progt &prog);

  /**
   * @brief
   *
   * @details
   */
  ~invariant_exec_body_providert();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const class goto_programt &operator()();
};

#include "invariant_body_provider.inc"

#endif // CPROVER_CEGIS_INVARIANT_SYMEX_LEARN_INVARIANT_BODY_PROVIDER_H
