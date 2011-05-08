/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#ifndef CPROVER_PROP_BOOLECTOR_PROP_H
#define CPROVER_PROP_BOOLECTOR_PROP_H

#include <vector>

#include <solvers/prop/prop.h>

class boolector_propt:public propt
{
public:
  boolector_propt();
  virtual ~boolector_propt();

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
  virtual unsigned no_variables() const { return _no_variables; }
  virtual void set_no_variables(unsigned no) { assert(false); }

  virtual void lcnf(const bvt &bv);

  class BtorExp *convert_literal(unsigned l);

  virtual const std::string solver_text()
  { return "Boolector"; }

  virtual tvt l_get(literalt a) const;
  virtual propt::resultt prop_solve();

  virtual void clear()
  {
    literal_map.clear();
  }

  virtual void reset_assignment()
  {
	literal_map.clear();
  }


  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  void gate_xor(literalt a, literalt b, literalt o);
  void gate_nand(literalt a, literalt b, literalt o);
  void gate_nor(literalt a, literalt b, literalt o);
  void gate_equal(literalt a, literalt b, literalt o);
  void gate_implies(literalt a, literalt b, literalt o);

  static void eliminate_duplicates(const bvt &bv, bvt &dest);

  friend class boolector_dect;

  class Btor *boolector_ctx;

protected:
  unsigned _no_variables;

  bool process_clause(const bvt &bv, bvt &dest);
  BtorExp* boolector_literal(literalt l);

  static bool is_all(const bvt &bv, literalt l)
  {
    for(unsigned i=0; i<bv.size(); i++)
      if(bv[i]!=l) return false;
    return true;
  }

  typedef hash_map_cont<unsigned, BtorExp*> literal_cachet;
  literal_cachet literal_cache;

  struct map_entryt
  {
    class BTorExp *exp;
    bool value;
  };

  typedef std::vector<map_entryt> literal_mapt;
  literal_mapt literal_map;
};

#endif
