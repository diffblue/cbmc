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

    exprt generate_alias_check(const exprt &) const;
    exprt generate_compatibility_check(const targett &) const;

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

    const exprt expr;
    const irep_idt &id;
    const assigns_clauset &parent;
  };

  assigns_clauset(const exprt &, const messaget &, const namespacet &);

  void add_target(const exprt &);

  goto_programt generate_havoc_code() const;
  exprt generate_alias_check(const exprt &) const;
  exprt generate_compatibility_check(const assigns_clauset &) const;

  const exprt &expr;
  const messaget &log;
  const namespacet &ns;

protected:
  std::unordered_set<targett, targett::hasht> targets;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_ASSIGNS_H
