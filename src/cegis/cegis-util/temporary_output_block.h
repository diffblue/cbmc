/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_TEMPORARY_OUTPUT_BLOCK_H
#define CPROVER_CEGIS_CEGIS_UTIL_TEMPORARY_OUTPUT_BLOCK_H

/**
 * @brief
 *
 * @details
 */
class temporary_output_blockt
{
public:
  /**
   * @brief
   *
   * @details
   */
  temporary_output_blockt();

  /**
   * @brief
   *
   * @details
   */
  ~temporary_output_blockt();

  /**
   * @brief
   *
   * @details
   */
  void release() const;
};

#endif // CPROVER_CEGIS_CEGIS_UTIL_TEMPORARY_OUTPUT_BLOCK_H
