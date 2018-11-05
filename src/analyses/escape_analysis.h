/*******************************************************************\

Module: Field-insensitive, location-sensitive, over-approximative
        escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive, over-approximative escape analysis

#ifndef CPROVER_ANALYSES_ESCAPE_ANALYSIS_H
#define CPROVER_ANALYSES_ESCAPE_ANALYSIS_H

#include <util/numbering.h>
#include <util/threeval.h>
#include <util/union_find.h>

#include "ai.h"

class escape_analysist;

class escape_domaint:public ai_domain_baset
{
public:
  escape_domaint():has_values(false)
  {
  }

  void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final override;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final override;

  bool merge(
    const escape_domaint &b,
    locationt from,
    locationt to);

  void make_bottom() final override
  {
    cleanup_map.clear();
    aliases.clear();
    has_values=tvt(false);
  }

  void make_top() final override
  {
    cleanup_map.clear();
    aliases.clear();
    has_values=tvt(true);
  }

  bool is_bottom() const override final
  {
    DATA_INVARIANT(!has_values.is_false() ||
                   (cleanup_map.empty() && (aliases.size()==0)),
                   "If the domain is bottom, all maps must be empty");
    return has_values.is_false();
  }

  bool is_top() const override final
  {
    DATA_INVARIANT(!has_values.is_true() ||
                   (cleanup_map.empty() && (aliases.size()==0)),
                   "If the domain is top, all maps must be empty");
    return has_values.is_true();
  }

  void make_entry() override final
  {
    make_top();
  }

  typedef union_find<irep_idt> aliasest;
  aliasest aliases;

  struct cleanupt
  {
    std::set<irep_idt> cleanup_functions;
  };

  // We track a set of 'cleanup functions' for specific
  // identifiers. The cleanup functions are executed
  // once the last pointer to an object is lost.
  typedef std::map<irep_idt, cleanupt> cleanup_mapt;
  cleanup_mapt cleanup_map;

private:
  tvt has_values;
  void assign_lhs_cleanup(const exprt &, const std::set<irep_idt> &);
  void get_rhs_cleanup(const exprt &, std::set<irep_idt> &);
  void assign_lhs_aliases(const exprt &, const std::set<irep_idt> &);
  void get_rhs_aliases(const exprt &, std::set<irep_idt> &);
  void get_rhs_aliases_address_of(const exprt &, std::set<irep_idt> &);
  irep_idt get_function(const exprt &);
  void check_lhs(const exprt &, std::set<irep_idt> &);

  friend class escape_analysist;

  bool is_tracked(const symbol_exprt &);
};

class escape_analysist:public ait<escape_domaint>
{
public:
  void instrument(goto_modelt &);

protected:
  virtual void initialize(const goto_functionst &)
  {
  }

  numbering<irep_idt> bits;

  void insert_cleanup(
    goto_functionst::goto_functiont &,
    goto_programt::targett,
    const exprt &,
    const std::set<irep_idt> &,
    bool is_object,
    const namespacet &);
};

#endif // CPROVER_ANALYSES_ESCAPE_ANALYSIS_H
