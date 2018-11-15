/*******************************************************************\

Module: Field-insensitive, location-sensitive, over-approximative
        escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive, over-approximative escape analysis

#ifndef CPROVER_ANALYSES_GLOBAL_MAY_ALIAS_H
#define CPROVER_ANALYSES_GLOBAL_MAY_ALIAS_H

#include <util/numbering.h>
#include <util/threeval.h>
#include <util/union_find.h>

#include "ai.h"

class global_may_alias_analysist;

class global_may_alias_domaint:public ai_domain_baset
{
public:
  global_may_alias_domaint():has_values(false)
  {
  }

  /// Abstract Interpretation domain transform function.
  void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final override;

  /// Abstract Interpretation domain output function.
  /// \param out: A stream to dump domain state on.
  /// \param ai: A reference to the currently active
  ///   abstract interpreter.
  /// \param ns: A namespace to resolve symbols during output.
  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final override;

  /// Abstract Interpretation domain merge function.
  bool merge(
    const global_may_alias_domaint &b,
    locationt from,
    locationt to);

  /// Clear list of aliases, and mark domain as bottom.
  void make_bottom() final override
  {
    aliases.clear();
    has_values=tvt(false);
  }

  /// Clear list of aliases, and mark domain as top.
  void make_top() final override
  {
    aliases.clear();
    has_values=tvt(true);
  }

  void make_entry() final override
  {
    make_top();
  }

  /// Returns true if domain is bottom.
  bool is_bottom() const final override
  {
    DATA_INVARIANT(!has_values.is_false() || (aliases.size()==0),
                   "If the domain is bottom, there must be no aliases");
    return has_values.is_false();
  }

  /// Returns false if domain is top.
  bool is_top() const final override
  {
    DATA_INVARIANT(!has_values.is_true() || (aliases.size()==0),
                   "If the domain is top, there must be no aliases");
    return has_values.is_true();
  }

  typedef union_find<irep_idt> aliasest;
  aliasest aliases;

private:
  tvt has_values;

  void assign_lhs_aliases(const exprt &, const std::set<irep_idt> &);
  void get_rhs_aliases(const exprt &, std::set<irep_idt> &);
  void get_rhs_aliases_address_of(const exprt &, std::set<irep_idt> &);
};

/// This is a may analysis (i.e. aliasing that may occur during execution,
/// but is not a given), for global variables. Implemented as a
/// Steensgaard-style analysis, with the Union-find algorithm, for
/// efficiency reasons.
class global_may_alias_analysist:public ait<global_may_alias_domaint>
{
protected:
  virtual void initialize(const goto_functionst &)
  {
  }
};

#endif // CPROVER_ANALYSES_GLOBAL_MAY_ALIAS_H
