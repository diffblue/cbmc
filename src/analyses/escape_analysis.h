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
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final;

  bool merge(
    const escape_domaint &b,
    locationt from,
    locationt to);

  void make_bottom() final
  {
    cleanup_map.clear();
    aliases.clear();
    has_values=tvt(false);
  }

  void make_top() final
  {
    cleanup_map.clear();
    aliases.clear();
    has_values=tvt(true);
  }

  void make_entry() final
  {
    make_top();
  }

  using aliasest = union_find<irep_idt>;
  aliasest aliases;

  struct cleanupt
  {
    std::set<irep_idt> cleanup_functions;
  };

  // We track a set of 'cleanup functions' for specific
  // identifiers. The cleanup functions are executed
  // once the last pointer to an object is lost.
  using cleanup_mapt = std::map<irep_idt, cleanupt>;
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
  virtual void initialize(const goto_functionst &_goto_functions)
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
