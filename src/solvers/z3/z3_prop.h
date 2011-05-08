/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#ifndef CPROVER_SOLVERS_Z3_PROP_H
#define CPROVER_SOLVERS_Z3_PROP_H

#include <solvers/prop/prop.h>

#include "z3_capi.h"

class z3_propt:public propt
{
public:
  z3_propt();
  virtual ~z3_propt();

  virtual literalt land(literalt a, literalt b);
  virtual literalt lor(literalt a, literalt b);
  virtual literalt land(const bvt &bv);
  virtual literalt lor(const bvt &bv);
  virtual literalt lxor(const bvt &bv);
  virtual literalt lnot(literalt a);
  virtual literalt lxor(literalt a, literalt b);
  virtual literalt lnand(literalt a, literalt b);
  virtual literalt lnor(literalt a, literalt b);
  virtual literalt lequal(literalt a, literalt b);
  virtual literalt limplies(literalt a, literalt b);
  virtual literalt lselect(literalt a, literalt b, literalt c); // a?b:c
  virtual literalt new_variable();
  virtual unsigned no_variables() const { return literal_map.size(); }
  virtual void lcnf(const bvt &bv);

  virtual const std::string solver_text()
  { return "Z3"; }

  virtual tvt l_get(literalt a) const;
  virtual propt::resultt prop_solve();

  virtual void clear()
  {
    literal_map.clear();
  }

  void reset_assignment();

  z3_capi z3_api;

protected:
  struct map_entryt
  {
    class Z3_ast *ast;
    bool value;
  };

  typedef std::vector<map_entryt> literal_mapt;
  literal_mapt literal_map;
};

#endif
