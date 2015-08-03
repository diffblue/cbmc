/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_GA_LEARNING_ALGORITHM_H_
#define CEGIS_GA_LEARNING_ALGORITHM_H_

#include <deque>
#include <util/message.h>
#include <goto-programs/goto_functions.h>

/**
 * @brief Symbolic execution implementation of a CEGIS learning algorithm.
 *
 * @details Implements a CEGIS learning algorithm using CBMC symbolic exeuction.
 */
class symex_learnt
{
public:
  /**
   * @brief Counterexample type for this CEGIS component.
   *
   * @details Counterexamples give a set of assignments (variable names and
   * corresponding assignments) for which the previous solution violates the
   * safety property.
   */
  typedef std::map<const irep_idt, exprt> counterexamplet;

  /**
   * @brief Candidate solution type for this CEGIS component.
   *
   * @details Solutions are provided as a set of GOTO function bodies
   * (goto_programt::instructionst) for function names.
   */
  typedef std::map<const irep_idt, goto_programt::instructionst> candidatet;
private:
  const class cegis_optionst &options;
  const symbol_tablet &symbol_table;
  const goto_functionst &goto_functions;
  ui_message_handlert &ui_message_handler;
  std::deque<counterexamplet> counterexamples;
  candidatet candidate;
public:
  /**
   * @brief Creates a symbolic execution CEGIS learner.
   *
   * @details Creates a symbolic execution CEGIS learner which creates and adapts
   * copies of the given symbol table and GOTO functions in order to challenge
   * CBMC into providing a candidate solution program.
   *
   * Uses the DEFAULT_SYNTHESIS_FUNCTION as function to be synthesised.
   *
   * @param options All existing CBMC options.
   * @param symbol_table The symbol table of the input problem.
   * @param goto_functions The GOTO functions of the input problem.
   * @param ui_message_handler The message handler to log to.
   */
  symex_learnt(const cegis_optionst &options,
      const symbol_tablet &symbol_table, const goto_functionst &goto_functions,
      ui_message_handlert &ui_message_handler);

  /**
   * @brief Default destructor.
   *
   * @details No cleanup tasks performed.
   */
  ~symex_learnt();

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
  void show_candidate(messaget::mstreamt &os) const;
};

#endif /* CEGIS_GA_LEARNING_ALGORITHM_H_ */
