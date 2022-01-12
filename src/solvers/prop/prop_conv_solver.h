/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_PROP_PROP_CONV_SOLVER_H
#define CPROVER_SOLVERS_PROP_PROP_CONV_SOLVER_H

#include <map>
#include <string>

#include <util/expr.h>
#include <util/message.h>

#include <solvers/conflict_provider.h>
#include <solvers/hardness_collector.h>

#include "prop.h"
#include "prop_conv.h"
#include "solver_resource_limits.h"

class equal_exprt;

class prop_conv_solvert : public conflict_providert,
                          public prop_convt,
                          public solver_resource_limitst
{
public:
  prop_conv_solvert(propt &_prop, message_handlert &message_handler)
    : prop(_prop), log(message_handler)
  {
  }

  virtual ~prop_conv_solvert() = default;

  // overloading from decision_proceduret
  decision_proceduret::resultt dec_solve() override;
  void print_assignment(std::ostream &out) const override;
  std::string decision_procedure_text() const override;
  exprt get(const exprt &expr) const override;

  tvt l_get(literalt a) const override
  {
    return prop.l_get(a);
  }

  exprt handle(const exprt &expr) override;

  void set_frozen(literalt);
  void set_frozen(const bvt &);
  void set_all_frozen();

  literalt convert(const exprt &expr) override;
  bool is_in_conflict(const exprt &expr) const override;

  /// For a Boolean expression \p expr, add the constraint
  /// 'current_context => expr' if \p value is `true`,
  /// otherwise add 'current_context => not expr'
  void set_to(const exprt &expr, bool value) override;

  void push() override;

  /// Push \p assumptions in form of `literal_exprt`
  void push(const std::vector<exprt> &assumptions) override;

  void pop() override;

  bool use_cache = true;
  bool equality_propagation = true;
  bool freeze_all = false; // freezing variables (for incremental solving)

  virtual void clear_cache()
  {
    cache.clear();
  }

  typedef std::map<irep_idt, literalt> symbolst;
  typedef std::unordered_map<exprt, literalt, irep_hash> cachet;

  const cachet &get_cache() const
  {
    return cache;
  }
  const symbolst &get_symbols() const
  {
    return symbols;
  }

  void set_time_limit_seconds(uint32_t lim) override
  {
    prop.set_time_limit_seconds(lim);
  }

  std::size_t get_number_of_solver_calls() const override;

  hardness_collectort *get_hardness_collector()
  {
    return dynamic_cast<hardness_collectort *>(&prop);
  }

protected:
  virtual void post_process();

  bool post_processing_done = false;

  /// Get a _boolean_ value from the model if the formula is satisfiable.
  /// If the argument is not a boolean expression from the formula,
  /// {} is returned.
  virtual optionalt<bool> get_bool(const exprt &expr) const;

  virtual literalt convert_rest(const exprt &expr);
  virtual literalt convert_bool(const exprt &expr);

  virtual bool set_equality_to_true(const equal_exprt &expr);

  // symbols
  symbolst symbols;

  virtual literalt get_literal(const irep_idt &symbol);

  // cache
  cachet cache;

  virtual void ignoring(const exprt &expr);

  propt &prop;

  messaget log;

  static const char *context_prefix;

  /// Assumptions on the stack
  bvt assumption_stack;

  /// To generate unique literal names for contexts
  std::size_t context_literal_counter = 0;

  /// `assumption_stack` is segmented in contexts;
  /// Number of assumptions in each context on the stack
  std::vector<size_t> context_size_stack;

private:
  /// Helper method used by `set_to` for adding the constraints to `prop`.
  /// This method is private because it must not be used by derived classes.
  void add_constraints_to_prop(const exprt &expr, bool value);
};

#endif // CPROVER_SOLVERS_PROP_PROP_CONV_SOLVER_H
