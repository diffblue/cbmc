/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_GENETIC_INDIVIDUAL_H_
#define CEGIS_GENETIC_INDIVIDUAL_H_

#include <cstddef>
#include <deque>
#include <vector>

/**
 * @brief
 *
 * @details
 */
class program_individualt
{
public:
  /**
   * @brief
   *
   * @details
   */
  class instructiont
  {
  public:
    typedef unsigned char opcodet;
    typedef unsigned char opt;
    typedef std::vector<opt> opst;

    opcodet opcode;
    opst ops;
  };

  typedef std::vector<instructiont> programt;
  typedef std::vector<programt> programst;
  typedef std::vector<unsigned int> x0t;
  typedef size_t fitnesst;

  programst programs;
  x0t x0;
  fitnesst fitness;
};

typedef std::vector<program_individualt> program_populationt;

#endif /* CEGIS_GENETIC_INDIVIDUAL_H_ */
