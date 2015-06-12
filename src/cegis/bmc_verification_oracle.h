/*******************************************************************
 Module:  JAVA Bytecode Language Conversion

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_BMC_VERIFICATION_ORACLE_H_
#define CEGIS_BMC_VERIFICATION_ORACLE_H_

/**
 * @brief BMC-based CEGIS verification oracle.
 *
 * @details Uses bounded model checking to verify a CEGIS candidate solution.
 */
class bmc_verification_oraclet
{
public:
  // TODO: Use BMC counterexample type.
  typedef int counterexamplet;
private:
  const class bmct &bmc;
  const class goto_functionst &goto_functions;
  counterexamplet current_counterexample;
public:
  // TODO: Use map of goto function names to code_blockt bodies.
  typedef int candidatet;

  bmc_verification_oraclet(const bmct &bmc,
      const goto_functionst &goto_functions);

  void verify(const candidatet &candidate);

  counterexamplet get_counterexample() const;

  bool has_counterexample() const;

  bool success() const;
};

#endif /* CEGIS_BMC_VERIFICATION_ORACLE_H_ */
