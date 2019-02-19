/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_PROP_H
#define CPROVER_SOLVERS_PROP_PROP_H

// decision procedure wrapper for boolean propositional logics

#include <cstdint>

#include <util/message.h>
#include <util/threeval.h>

#include "literal.h"

/*! \brief TO_BE_DOCUMENTED
*/
class propt
{
public:
  explicit propt(message_handlert &message_handler) : log(message_handler)
  {
  }

  virtual ~propt() { }

  // boolean operators
  virtual literalt land(literalt a, literalt b)=0;
  virtual literalt lor(literalt a, literalt b)=0;
  virtual literalt land(const bvt &bv)=0;
  virtual literalt lor(const bvt &bv)=0;
  virtual literalt lxor(literalt a, literalt b)=0;
  virtual literalt lxor(const bvt &bv)=0;
  virtual literalt lnand(literalt a, literalt b)=0;
  virtual literalt lnor(literalt a, literalt b)=0;
  virtual literalt lequal(literalt a, literalt b)=0;
  virtual literalt limplies(literalt a, literalt b)=0;
  virtual literalt lselect(literalt a, literalt b, literalt c)=0; // a?b:c
  virtual void set_equal(literalt a, literalt b);

  virtual void l_set_to(literalt a, bool value)
  {
    set_equal(a, const_literal(value));
  }

  void l_set_to_true(literalt a)
  { l_set_to(a, true); }
  void l_set_to_false(literalt a)
  { l_set_to(a, false); }

  // constraints
  void lcnf(literalt l0, literalt l1)
  { lcnf_bv.resize(2); lcnf_bv[0]=l0; lcnf_bv[1]=l1; lcnf(lcnf_bv); }

  void lcnf(literalt l0, literalt l1, literalt l2)
  {
    lcnf_bv.resize(3);
    lcnf_bv[0]=l0;
    lcnf_bv[1]=l1;
    lcnf_bv[2]=l2;
    lcnf(lcnf_bv);
  }

  void lcnf(literalt l0, literalt l1, literalt l2, literalt l3)
  {
    lcnf_bv.resize(4);
    lcnf_bv[0]=l0;
    lcnf_bv[1]=l1;
    lcnf_bv[2]=l2;
    lcnf_bv[3]=l3;
    lcnf(lcnf_bv);
  }

  virtual void lcnf(const bvt &bv)=0;
  virtual bool has_set_to() const { return true; }

  // Some solvers (notably aig) prefer encodings that avoid raw CNF
  // They overload this to return false and thus avoid some optimisations
  virtual bool cnf_handled_well() const { return true; }

  // assumptions
  virtual void set_assumptions(const bvt &) { }
  virtual bool has_set_assumptions() const { return false; }

  // variables
  virtual literalt new_variable()=0;
  virtual void set_variable_name(literalt, const irep_idt &) { }
  virtual size_t no_variables() const=0;
  bvt new_variables(std::size_t width);

  // solving
  virtual const std::string solver_text()=0;
  enum class resultt { P_SATISFIABLE, P_UNSATISFIABLE, P_ERROR };
  resultt prop_solve();

  // satisfying assignment
  virtual tvt l_get(literalt a) const=0;
  virtual void set_assignment(literalt a, bool value) = 0;

  /// Returns true if an assumption is in the final conflict.
  /// Note that only literals that are assumptions (see set_assumptions)
  /// may be queried.
  /// \return true iff the given literal is part of the final conflict
  virtual bool is_in_conflict(literalt l) const = 0;
  virtual bool has_is_in_conflict() const { return false; }

  // an incremental solver may remove any variables that aren't frozen
  virtual void set_frozen(literalt) { }

  // Resource limits:
  virtual void set_time_limit_seconds(uint32_t)
  {
    log.warning() << "CPU limit ignored (not implemented)" << messaget::eom;
  }

  std::size_t get_number_of_solver_calls() const;

protected:
  virtual resultt do_prop_solve() = 0;

  // to avoid a temporary for lcnf(...)
  bvt lcnf_bv;

  messaget log;
  std::size_t number_of_solver_calls = 0;
};

#endif // CPROVER_SOLVERS_PROP_PROP_H
