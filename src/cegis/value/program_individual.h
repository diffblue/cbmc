/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_VALUE_PROGRAM_INDIVIDUAL_H
#define CPROVER_CEGIS_VALUE_PROGRAM_INDIVIDUAL_H

#include <cstddef>
#include <deque>
#include <vector>

#include <cegis/genetic/family_selection.h>

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

/**
 * @brief
 *
 * @details
 */
typedef std::vector<program_individualt> program_populationt;

/**
 * @brief
 *
 * @details
 */
typedef family_selectiont<program_populationt> program_individual_selectiont;

#endif // CPROVER_CEGIS_VALUE_PROGRAM_INDIVIDUAL_H
