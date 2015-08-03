/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CANDIDATE_FACTORY_H_
#define CEGIS_CANDIDATE_FACTORY_H_

#include <goto-programs/goto_program.h>

/**
 * @brief Transforms a CBMC counterexample from a SYMEX learner.
 *
 * @details Transforms a CBMC counterexample from a SYMEX learner, which
 * contains assignments to synthesised program variables. The instruction
 * set of these synthesised programs needs to be translated back to a
 * CBMC GOTO function implementation. This class implements this functionality.
 */
class candidate_factoryt
{
public:
  /**
   * @brief Counterexample type for SYMEX CEGIS components.
   *
   * @details Counterexamples give a set of assignments (variable names and
   * corresponding assignments) for which the previous solution violates the
   * safety property.
   */
  typedef std::map<const irep_idt, goto_programt::instructionst> candidatet;
private:
  candidatet &result;
  const class goto_functionst &gf;
  const class goto_tracet &goto_trace;
public:
  /**
   * @brief Creates a candidate factory.
   *
   * @details Creates a factory which, when executed, stores the candidate solution
   * contained in the given GOTO trace into the provided candidate variable.
   *
   * @param result The result variable for the created candidate solution.
   * @param gf
   * @param goto_trace The trace which contains the assignment to the synthesised
   * program variables.
   */
  candidate_factoryt(candidatet &result, const goto_functionst &gf,
      const goto_tracet &goto_trace);

  /**
   * @brief Default destructor.
   *
   * @details No cleanup tasks performed.
   */
  ~candidate_factoryt();

  /**
   * @brief Single main operation.
   *
   * @details Effectively executes the implemented operation.
   *
   * @returns <code>true</code> if the conversion was successful, <code>false</code> otherwise.
   */
  bool operator()() const;
};

#endif /* CEGIS_CANDIDATE_FACTORY_H_ */
