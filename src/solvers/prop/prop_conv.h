/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CONV_H
#define CPROVER_PROP_CONV_H

#include <string>
#include <map>

#include <util/hash_cont.h>
#include <util/decision_procedure.h>
#include <util/expr.h>
#include <util/std_expr.h>

#include "literal.h"
#include "prop.h"

class prop_conv_baset:public decision_proceduret
{
public:
  explicit prop_conv_baset(
    const namespacet &_ns, propt &_prop):
    decision_proceduret(_ns), prop(_prop) { }
  virtual ~prop_conv_baset() { }

  // overloading from decision_proceduret
  virtual std::string decision_procedure_text() const
  { return "propositional reduction"; }

  // conversion
  virtual literalt convert(const exprt &expr)=0;
  
  inline literalt operator()(const exprt &expr)
  {
    return convert(expr);
  }

  // selected methods from the lower propt API are passed up
  virtual tvt l_get(literalt a) const { return prop.l_get(a); }
  virtual void set_frozen(literalt a) { prop.set_frozen(a); }
  virtual void set_frozen(const bvt &);
  virtual void set_assumptions(const bvt &_assumptions) { prop.set_assumptions(_assumptions); }
  virtual bool has_set_assumptions() const { return prop.has_set_assumptions(); }

  // this will become protected
  //protected:
  propt &prop;
};

//
// converts the propositional skeleton
//

/*! \brief TO_BE_DOCUMENTED
*/
class prop_convt:public prop_conv_baset
{
public:
  prop_convt(const namespacet &_ns, propt &_prop):
    prop_conv_baset(_ns, _prop),
    use_cache(true),
    equality_propagation(true),
    post_processing_done(false) { }

  virtual ~prop_convt() { }

  // overloading from decision_proceduret
  virtual void set_to(const exprt &expr, bool value);
  virtual decision_proceduret::resultt dec_solve();
  virtual void print_assignment(std::ostream &out) const;

  virtual exprt get(const exprt &expr) const;

  // conversion
  virtual literalt convert(const exprt &expr);

  // get literal for expression, if available
  virtual bool literal(const exprt &expr, literalt &literal) const;
  
  bool use_cache;
  bool equality_propagation;
  
  friend struct prop_conv_store_constraintt;

  virtual void clear_cache()
  {
    cache.clear();
  }

  typedef std::map<irep_idt, literalt> symbolst;
  typedef hash_map_cont<exprt, literalt, irep_hash> cachet;

  const cachet &get_cache() const { return cache; }
  const symbolst &get_symbols() const { return symbols; }
  
protected:
  virtual void post_process();
  
  bool post_processing_done;

  // get a _boolean_ value from counterexample if not valid
  virtual bool get_bool(const exprt &expr, tvt &value) const;
  
  virtual literalt convert_rest(const exprt &expr);
  virtual literalt convert_bool(const exprt &expr);
  
  virtual bool set_equality_to_true(const equal_exprt &expr);

  // symbols
  symbolst symbols;

  virtual literalt get_literal(const irep_idt &symbol);

  // cache
  cachet cache;
  
  virtual void ignoring(const exprt &expr);
};

#endif
