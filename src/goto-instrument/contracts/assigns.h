/*******************************************************************\

Module: Specify write set in code contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H

#include <unordered_set>

#include <util/message.h>

#include "utils.h"

typedef std::pair<const exprt, const exprt> slicet;

/// \brief A class for representing assigns clauses in code contracts
class assigns_clauset
{
public:
  /// \brief A class for representing Conditional Address Ranges
  class conditional_address_ranget
  {
  public:
    conditional_address_ranget(const assigns_clauset &, const exprt &);

    goto_programt generate_snapshot_instructions() const;

    bool operator==(const conditional_address_ranget &other) const
    {
      return source_expr == other.source_expr;
    }

    struct hasht
    {
      std::size_t operator()(const conditional_address_ranget &target) const
      {
        return irep_hash{}(target.source_expr);
      }
    };

    const exprt source_expr;
    const source_locationt &location;
    const assigns_clauset &parent;

    const slicet slice;
    const symbol_exprt validity_condition_var;
    const symbol_exprt lower_bound_address_var;
    const symbol_exprt upper_bound_address_var;

  protected:
    const exprt
    generate_unsafe_inclusion_check(const conditional_address_ranget &) const;

    const symbolt
    generate_new_symbol(const typet &, const source_locationt &) const;

    friend class assigns_clauset;
  };

  typedef std::
    unordered_set<conditional_address_ranget, conditional_address_ranget::hasht>
      write_sett;

  assigns_clauset(
    const exprt::operandst &,
    const messaget &,
    const namespacet &,
    const irep_idt &,
    symbol_tablet &);

  write_sett::const_iterator add_to_write_set(const exprt &);
  void remove_from_write_set(const exprt &);

  exprt generate_inclusion_check(const conditional_address_ranget &) const;

  const write_sett &get_write_set() const
  {
    return write_set;
  }

  /// \brief Finds symbols declared with a static lifetime in the given
  /// `root_function` or one of the functions it calls,
  /// and adds them to the write set of this assigns clause.
  ///
  /// @param functions all functions of the goto_model
  /// @param root_function the root function under which to search statics
  ///
  /// A symbol is considered a static local symbol iff:
  /// - it has a static lifetime annotation
  /// - its source location has a non-empty function attribute
  /// - this function attribute is found in the call graph of the root_function
  void add_static_locals_to_write_set(
    const goto_functionst &functions,
    const irep_idt &root_function);

  const messaget &log;
  const namespacet &ns;
  const irep_idt &function_name;

protected:
  symbol_tablet &symbol_table;
  write_sett write_set;
};

/// \brief A class that further overrides the "safe" havoc utilities,
///        and adds support for havocing pointer_object expressions.
class havoc_assigns_targetst : public havoc_if_validt
{
public:
  havoc_assigns_targetst(const modifiest &mod, const namespacet &ns)
    : havoc_if_validt(mod, ns)
  {
  }

  void append_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const override;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
