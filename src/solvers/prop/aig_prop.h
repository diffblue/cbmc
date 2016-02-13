/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROPSOLVE_AIG_PROP_H
#define CPROVER_PROPSOLVE_AIG_PROP_H

#include <cassert>

#include <util/threeval.h>
#include <solvers/prop/prop.h>

#include "aig.h"

class aig_prop_baset:public propt
{
public:
  explicit inline aig_prop_baset(aigt &_dest):dest(_dest)
  {
  }

  virtual bool has_set_to() const { return false; }
  virtual bool cnf_handled_well() const { return false; }
 
  virtual literalt land(literalt a, literalt b);
  virtual literalt lor(literalt a, literalt b);
  virtual literalt land(const bvt &bv);
  virtual literalt lor(const bvt &bv);
  virtual void lcnf(const bvt &clause) { assert(false); }
  virtual literalt lxor(literalt a, literalt b);
  virtual literalt lxor(const bvt &bv);
  virtual literalt lnand(literalt a, literalt b);
  virtual literalt lnor(literalt a, literalt b);
  virtual literalt lequal(literalt a, literalt b);
  virtual literalt limplies(literalt a, literalt b);
  virtual literalt lselect(literalt a, literalt b, literalt c); // a?b:c
  virtual void set_equal(literalt a, literalt b);

  virtual void l_set_to(literalt a, bool value) { assert(false); }

  virtual literalt new_variable()
  {
    return dest.new_node();
  }
  
  virtual size_t no_variables() const
  { return dest.number_of_nodes(); }

  virtual const std::string solver_text()
  { return "conversion into and-inverter graph"; }

  virtual tvt l_get(literalt a) const
  { assert(0); return tvt::unknown(); }
  
  virtual resultt prop_solve()
  { assert(0); return P_ERROR; }

protected:
  aigt &dest;
};

class aig_prop_constraintt:public aig_prop_baset
{
public:
  inline explicit aig_prop_constraintt(aig_plus_constraintst &_dest):
    aig_prop_baset(_dest),
    dest(_dest)
  {
  }

  aig_plus_constraintst &dest;
  virtual bool has_set_to() const { return true; }
 
  virtual void lcnf(const bvt &clause)
  {
    l_set_to_true(lor(clause));
  }
  
  virtual void l_set_to(literalt a, bool value)
  {
    dest.constraints.push_back(a^!value);
  }
};

class aig_prop_solvert:public aig_prop_constraintt
{
public:
  explicit inline aig_prop_solvert(propt &_solver):
    aig_prop_constraintt(aig),
    solver(_solver)
  {
  }
  
  aig_plus_constraintst aig;

  virtual const std::string solver_text()
  { return "conversion into and-inverter graph followed by "+
           solver.solver_text(); }

  virtual tvt l_get(literalt a) const;
  virtual resultt prop_solve();
  
  virtual void set_message_handler(message_handlert &m)
  {
    aig_prop_constraintt::set_message_handler(m);
    solver.set_message_handler(m);
  }
  
protected:
  propt &solver;
  
  void convert_aig();
  void usage_count(std::vector<unsigned> &p_usage_count, std::vector<unsigned> &n_usage_count);
  void compute_phase(std::vector<bool> &n_pos, std::vector<bool> &n_neg);
  void convert_node(unsigned n, const aigt::nodet &node, bool n_pos, bool n_neg, std::vector<unsigned> &p_usage_count, std::vector<unsigned> &n_usage_count);
};

#endif
