/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_SOLUTION_H_
#define CEGIS_CONTROL_SOLUTION_H_

#include <vector>

/**
 * @brief
 *
 * @details
 */
class control_solutiont
{
public:
  /**
   * @brief
   *
   * @details
   */
  std::vector<double> a;

  /**
   * @brief
   *
   * @details
   */
  std::vector<double> b;
};

#endif /* CEGIS_CONTROL_SOLUTION_H_ */
