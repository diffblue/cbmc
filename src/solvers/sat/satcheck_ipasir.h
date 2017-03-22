/*******************************************************************\

Module:

Author: Norbert Manthey, nmanthey@amazon.com

Sample compilation command:
(to be executed from base directory of project)

make clean
make ipasir-build
CXXFLAGS=-g IPASIR=../../ipasir LIBSOLVER=$(pwd)/ipasir/libipasir.a \
  CFLAGS="-Wall -O2 -DSATCHECK_IPSAIR" LINKFLAGS="-static" \
  make -j 7 -C $(pwd)/src/;

Note: Make sure, the LIBSOLVER variable is set in the environment!
      The variable should point to the solver you actually want to
      link against.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
#define CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H

#include "cnf.h"

// Interface for generic SAT solver interface IPASIR
class satcheck_ipasirt:public cnf_solvert
{
public:
  satcheck_ipasirt();
  virtual ~satcheck_ipasirt();

  virtual const std::string solver_text();

  virtual resultt prop_solve() override;
  virtual tvt l_get(literalt a) const override final;

  virtual void lcnf(const bvt &bv) override final;

  /* this method is not supported, and currently not called anywhere in CBMC */
  virtual void set_assignment(literalt a, bool value) override;

  virtual void set_assumptions(const bvt &_assumptions) override;

  virtual bool is_in_conflict(literalt a) const override;
  virtual bool has_set_assumptions() const override final { return true; }
  virtual bool has_is_in_conflict() const override final { return true; }

protected:
  void *solver;

  bvt assumptions;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
