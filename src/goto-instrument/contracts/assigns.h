/*******************************************************************\

Module: Specify write set in code contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H

#include "contracts.h"

#include <util/pointer_offset_size.h>

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
      return expr == other.expr;
    }

    struct hasht
    {
      std::size_t operator()(const targett &target) const
      {
        return irep_hash{}(target.expr);
      }
    };

    const address_of_exprt address;
    const exprt &expr;
    const irep_idt &id;
    const assigns_clauset &parent;
  };

  assigns_clauset(const exprt &, const messaget &, const namespacet &);

  void add_target(const exprt &);
  void remove_target(const exprt &);

  goto_programt generate_havoc_code() const;
  exprt generate_containment_check(const exprt &) const;
  exprt generate_subset_check(const assigns_clauset &) const;

  const exprt &expr;
  const messaget &log;
  const namespacet &ns;

protected:
  std::unordered_set<targett, targett::hasht> targets;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
