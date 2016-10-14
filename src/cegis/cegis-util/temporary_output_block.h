/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_UTIL_TEMPORARY_OUTPUT_BLOCK_H_
#define CEGIS_UTIL_TEMPORARY_OUTPUT_BLOCK_H_

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

#endif /* CEGIS_UTIL_TEMPORARY_OUTPUT_BLOCK_H_ */
