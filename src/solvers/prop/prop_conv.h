/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//
// converts the propositional skeleton
//

#ifndef CPROVER_PROP_CONV_H
#define CPROVER_PROP_CONV_H

#include <string>
#include <map>

#include <hash_cont.h>
#include <decision_procedure.h>
#include <expr.h>

#include "literal.h"

class propt;
class tvt;

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

  propt &prop;
};

/*! \brief TO_BE_DOCUMENTED
*/
class prop_convt:public prop_conv_baset
{
public:
  prop_convt(const namespacet &_ns, propt &_prop):
    prop_conv_baset(_ns, _prop),
    use_cache(true),
    equality_propagation(true) { }
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
  
  friend class prop_conv_store_constraintt;

  virtual void post_process();
  
  virtual void clear_cache()
  {
    cache.clear();
  }

  typedef std::map<irep_idt, literalt> symbolst;
  typedef hash_map_cont<exprt, literalt, irep_hash> cachet;

  const cachet &get_cache() const { return cache; }
  const symbolst &get_symbols() const { return symbols; }
  
protected:
  // get a _boolean_ value from counterexample if not valid
  virtual bool get_bool(const exprt &expr, tvt &value) const;
  
  virtual literalt convert_rest(const exprt &expr);
  virtual literalt convert_bool(const exprt &expr);
  
  virtual bool set_equality_to_true(const exprt &expr);

  // symbols
  symbolst symbols;

  virtual literalt get_literal(const irep_idt &symbol);

  // cache
  cachet cache;
  
  virtual void ignoring(const exprt &expr);
};

#endif
