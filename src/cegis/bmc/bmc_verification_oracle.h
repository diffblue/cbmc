/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_BMC_VERIFICATION_ORACLE_H_
#define CEGIS_BMC_VERIFICATION_ORACLE_H_

#include <util/options.h>
#include <goto-programs/goto_program.h>

/**
 * @brief BMC-based CEGIS verification oracle.
 *
 * @details Uses bounded model checking to verify a CEGIS candidate solution.
 */
class bmc_verification_oraclet
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
private:
  bool is_failure;
  const optionst &options;
  const symbol_tablet &symbol_table;
  const class goto_functionst &goto_functions;
  ui_message_handlert &ui_message_handler;
  counterexamplet current_counterexample;
public:
  /**
   * @brief Candidate solution type for this CEGIS component.
   *
   * @details Solutions are provided as a set of GOTO function bodies
   * (goto_programt::instructionst) for function names.
   */
  typedef std::map<const irep_idt, goto_programt::instructionst> candidatet;

  /**
   * @brief Creates a BMC-based CEGIS verification oracle.
   *
   * @details This oracle invokes CBMC to verify whether a candidate solution
   * holds for all inputs.
   *
   * @param options All existing CBMC options.
   * @param symbol_table The symbol table of the input problem.
   * @param goto_functions The GOTO functions of the input problem.
   * @param ui_message_handler The message handler to log to.
   */
  bmc_verification_oraclet(const optionst &options,
      const symbol_tablet &symbol_table, const goto_functionst &goto_functions,
      ui_message_handlert &ui_message_handler);

  /**
   * @brief Default destructor.
   *
   * @details No cleanup tasks performed.
   */
  ~bmc_verification_oraclet();

  /**
   * @brief Verifies a given candidate solution.
   *
   * @details Effectively invokes CBMC using the given function bodies.
   *
   * @param candidate The candidate implementation provided by the learner.
   */
  void verify(const candidatet &candidate);

  /**
   * @brief Provides the last counterexample.
   *
   * @details If the verification fails, this operation provides the corresponding
   * counterexample.
   *
   * @return The last counterexample.
   */
  counterexamplet get_counterexample() const;

  /**
   * @brief Indicates whether a counterexample could be produced.
   *
   * @details If the verification fails, but the oracle is unable to provide a
   * counterexample, this marks an error in the CBMC execution.
   *
   * @return <code>true</code> if a counterexample was created, <code>false</code> otherwise.
   */
  bool has_counterexample() const;

  /**
   * @brief Indicates whether the provided solution holds.
   *
   * @details Provides the result of the last "verify()" operation.
   *
   * @return <code>true</code> if the last solution holds, <code>false</code> otherwise.
   */
  bool success() const;
};

#endif /* CEGIS_BMC_VERIFICATION_ORACLE_H_ */
