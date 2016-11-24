/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATCHECK_SMVSAT_H
#define CPROVER_SATCHECK_SMVSAT_H

#include <vector>
#include <set>

#include <util/expr.h>

#include "cnf.h"

class satcheck_smvsatt:public cnf_solvert
{
public:
  satcheck_smvsatt();
  virtual ~satcheck_smvsatt();
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;
  virtual void lcnf(const bvt &bv);

protected:
  struct sat_instance *satsolver;
};

class satcheck_smvsat_coret:public satcheck_smvsatt
{
public:
  satcheck_smvsat_coret();
  
  virtual resultt prop_solve();

  bool is_in_core(literalt l) const
  {
    assert(l.var_no()<in_core.size());
    return in_core[l.var_no()];
  }
  
protected:
  std::vector<bool> in_core;
};

class satcheck_smvsat_interpolatort:public satcheck_smvsatt
{
public:
  satcheck_smvsat_interpolatort():partition_no(0)
  {
  }

  void set_partition_no(short p)
  {
    partition_no=p;
  }  
  
  void interpolate(exprt &dest);
  
protected:
  virtual void lcnf(const bvt &bv);
  short partition_no;

  std::vector<short> partition_numbers;
  
  void build_aig(
    struct interpolator &interpolator_satsolver,
    int output,
    exprt &dest);  

  struct entry
  {
    int g;
    exprt *e;
    
    entry(int _g, exprt *_e):g(_g), e(_e)
    {
    }
  };
  
};

#endif
