/*******************************************************************\

Module: Field-insensitive, location-sensitive, over-approximative
        escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ESCAPE_ANALYSIS_H
#define CPROVER_ESCAPE_ANALYSIS_H

#include <util/numbering.h>
#include <util/union_find.h>

#include "ai.h"

/*******************************************************************\

   Class: escape_domaint
   
 Purpose:

\*******************************************************************/

class escape_analysist;

class escape_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  bool merge(
    const escape_domaint &b,
    locationt from,
    locationt to);
    
  void make_bottom()
  {
    cleanup_map.clear();
  }
  
  void make_top()
  {
    cleanup_map.clear();
  }
  
  typedef union_find<irep_idt> aliasest;
  aliasest aliases;
  
  struct cleanupt
  {
    std::set<irep_idt> cleanup_functions;
  };
  
  typedef std::map<irep_idt, cleanupt > cleanup_mapt;
  cleanup_mapt cleanup_map;

protected:  
  void assign_lhs(const exprt &, const std::set<irep_idt> &);
  void get_rhs(const exprt &, std::set<irep_idt> &);
  void set_cleanup(const exprt &, const irep_idt &);
  irep_idt get_function(const exprt &);
};

class escape_analysist:public ait<escape_domaint> 
{
public:
  void instrument(
    goto_functionst &,
    const namespacet &);

protected:
  virtual void initialize(const goto_functionst &_goto_functions)
  {
  }

  friend class escape_domaint;

  numbering<irep_idt> bits;
  
  void check_lhs(locationt, const exprt &, std::set<irep_idt> &);

  void insert_cleanup(
    goto_functionst::goto_functiont &,
    goto_programt::targett,
    const exprt &,
    const std::set<irep_idt> &,
    const namespacet &);
};

#endif
