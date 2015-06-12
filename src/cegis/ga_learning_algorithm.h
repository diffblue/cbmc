/*******************************************************************
 Module:  JAVA Bytecode Language Conversion

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_GA_LEARNING_ALGORITHM_H_
#define CEGIS_GA_LEARNING_ALGORITHM_H_

#include <iosfwd>

/**
 * @brief Genetic Algorithms implementation of a CEGIS learning algorithm.
 *
 * @details Implements a CEGIS learning algorithm using an evolutionary
 * strateegy.
 */
class ga_learning_algorithmt
{
public:
  // TODO: Use BMC counterexample type.
  typedef int counterexamplet;
  // TODO: Use map of goto function names to code_blockt bodies.
  typedef int candidatet;

  /**
   * @brief Provides the next candidate.
   *
   * @details Provides the last candidate generated using learn.
   *
   * @return The next candidate.
   */
  candidatet next_candidate() const;

  /**
   * @brief Generates a candidate solution.
   *
   * @details Receives a counterexample from the verification oracle
   * and adds it to its information base. Generates a new candidate
   * based on received counterexamples.
   *
   * @param counterexample The counterexample from the oracle.
   *
   * @return <code>true</code> if learning was successful, <code>false</code>
   * if no new candidate could be generated.
   */
  bool learn(const counterexamplet &counterexample);

  /**
   * @brief Displays the last candidate.
   *
   * @details Prints the last candidate generated using learn.
   *
   * @param os The stream to output the candidate.
   */
  void show_candidate(std::ostream &os) const;
};

#endif /* CEGIS_GA_LEARNING_ALGORITHM_H_ */
