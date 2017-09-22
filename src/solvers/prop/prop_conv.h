/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_PROP_CONV_H
#define CPROVER_SOLVERS_PROP_PROP_CONV_H

#include <string>
#include <map>

#include <util/decision_procedure.h>
#include <util/expr.h>
#include <util/std_expr.h>

#include "literal.h"
#include "literal_expr.h"
#include "prop.h"

// API that provides a "handle" in the form of a literalt
// for expressions.

class prop_convt:public decision_proceduret
{
public:
  explicit prop_convt(
    const namespacet &_ns):
    decision_proceduret(_ns) { }
  virtual ~prop_convt() { }

  // conversion to handle
  virtual literalt convert(const exprt &expr)=0;

  literalt operator()(const exprt &expr)
  {
    return convert(expr);
  }

  using decision_proceduret::operator();

  // specialised variant of get
  virtual tvt l_get(literalt a) const=0;

  // incremental solving
  virtual void set_frozen(literalt a);
  virtual void set_frozen(const bvt &);
  virtual void set_assumptions(const bvt &_assumptions);
  virtual bool has_set_assumptions() const { return false; }
  virtual void set_all_frozen() {}

  // returns true if an assumption is in the final conflict
  virtual bool is_in_conflict(literalt l) const;
  virtual bool has_is_in_conflict() const { return false; }

  // Resource limits:
  virtual void set_time_limit_seconds(uint32_t) {}
};

//
// an instance of the above that converts the
// propositional skeleton by passing it to a propt
//

/*! \brief TO_BE_DOCUMENTED
*/
class prop_conv_solvert:public prop_convt
{
public:
  prop_conv_solvert(const namespacet &_ns, propt &_prop):
    prop_convt(_ns),
    use_cache(true),
    equality_propagation(true),
    freeze_all(false),
    post_processing_done(false),
    prop(_prop) { }

  virtual ~prop_conv_solvert() { }

  // overloading from decision_proceduret
  virtual void set_to(const exprt &expr, bool value) override;
  virtual decision_proceduret::resultt dec_solve() override;
  virtual void print_assignment(std::ostream &out) const override;
  virtual std::string decision_procedure_text() const override
  { return "propositional reduction"; }
  virtual exprt get(const exprt &expr) const override;

  // overloading from prop_convt
  using prop_convt::set_frozen;
  virtual tvt l_get(literalt a) const override { return prop.l_get(a); }
  virtual void set_frozen(literalt a) override { prop.set_frozen(a); }
  virtual void set_assumptions(const bvt &_assumptions) override
  { prop.set_assumptions(_assumptions); }
  virtual bool has_set_assumptions() const override
  { return prop.has_set_assumptions(); }
  virtual void set_all_frozen() override { freeze_all = true; }
  virtual literalt convert(const exprt &expr) override;
  virtual bool is_in_conflict(literalt l) const override
  { return prop.is_in_conflict(l); }
  virtual bool has_is_in_conflict() const override
  { return prop.has_is_in_conflict(); }

  // get literal for expression, if available
  virtual bool literal(const exprt &expr, literalt &literal) const;

  bool use_cache;
  bool equality_propagation;
  bool freeze_all; // freezing variables (for incremental solving)

  virtual void clear_cache() { cache.clear();}

  typedef std::map<irep_idt, literalt> symbolst;
  typedef std::unordered_map<exprt, literalt, irep_hash> cachet;

  const cachet &get_cache() const { return cache; }
  const symbolst &get_symbols() const { return symbols; }

  void set_time_limit_seconds(uint32_t lim) override
  {
    prop.set_time_limit_seconds(lim);
  }

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

  // deliberately protected now to protect lower-level API
  propt &prop;
};

#endif // CPROVER_SOLVERS_PROP_PROP_CONV_H
