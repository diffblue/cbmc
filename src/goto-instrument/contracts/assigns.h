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

#include <goto-programs/goto_model.h>

#include <util/message.h>
#include <util/pointer_expr.h>

/// \brief A class for representing assigns clauses in code contracts
class assigns_clauset
{
public:
  /// \brief A class for representing targets for assigns clauses
  class targett
  {
  public:
    targett(const assigns_clauset &, const exprt &);

    static exprt normalize(const exprt &);

    exprt generate_containment_check(const address_of_exprt &) const;

    bool operator==(const targett &other) const
    {
      return address == other.address;
    }

    struct hasht
    {
      std::size_t operator()(const targett &target) const
      {
        return irep_hash{}(target.address);
      }
    };

    const address_of_exprt address;
    const irep_idt &id;
    const assigns_clauset &parent;
  };

  assigns_clauset(
    const exprt::operandst &,
    const messaget &,
    const namespacet &);

  void add_to_global_write_set(const exprt &);
  void remove_from_global_write_set(const exprt &);
  void add_to_local_write_set(const exprt &);
  void remove_from_local_write_set(const exprt &);

  goto_programt generate_havoc_code(const source_locationt &) const;
  exprt generate_containment_check(const exprt &) const;
  exprt generate_subset_check(const assigns_clauset &) const;

  const messaget &log;
  const namespacet &ns;

protected:
  std::unordered_set<targett, targett::hasht> global_write_set;
  std::unordered_set<targett, targett::hasht> local_write_set;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
