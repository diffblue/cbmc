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
#include <util/std_expr.h>

#include "decision_procedure_contexts.h"
#include "literal.h"
#include "literal_expr.h"
#include "prop.h"
#include "solver_conflicts.h"
#include "solver_resource_limits.h"

class prop_conv_solvert : public decision_procedure_contextst,
                          public solver_conflictst,
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
  std::string decision_procedure_text() const override
  {
    return "propositional reduction";
  }
  exprt get(const exprt &expr) const override;

  // overloading from decision_proceduret
  using decision_procedure_incrementalt::set_frozen;
  tvt l_get(literalt a) const override
  {
    return prop.l_get(a);
  }
  void set_frozen(literalt a) override
  {
    prop.set_frozen(a);
  }

  void set_all_frozen() override
  {
    freeze_all = true;
  }
  literalt convert(const exprt &expr) override;
  bool is_in_conflict(literalt l) const override
  {
    return prop.is_in_conflict(l);
  }

  /// For a Boolean expression \p expr, add the constraint
  /// 'current_context => expr' if \p value is `true`,
  /// otherwise add 'current_context => not expr'
  void set_to(const exprt &expr, bool value) override;

  /// Set \p assumptions within current context.
  /// These assumptions can be removed by passing empty \p assumptions.
  /// These assumptions will also be dropped in the course of any context
  /// operation (`push_context` or `pop_context`).
  void set_assumptions(const bvt &assumptions) override;

  /// Push a new context on the stack
  /// This context becomes a child context nested in the current context.
  void push_context() override;

  /// Pop the current context
  void pop_context() override;

  static const char *context_prefix;

  // get literal for expression, if available
  bool literal(const symbol_exprt &expr, literalt &literal) const;

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

protected:
  virtual void post_process();

  bool post_processing_done = false;

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

  /// Actually adds the constraints to `prop`
  void do_set_to(const exprt &expr, bool value);

  propt &prop;

  messaget log;

  /// Context literals used as assumptions
  bvt context_literals;

  /// Unique context literal names
  std::size_t context_literal_counter = 0;
};

#endif // CPROVER_SOLVERS_PROP_PROP_CONV_SOLVER_H
