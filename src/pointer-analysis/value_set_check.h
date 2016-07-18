/*******************************************************************\

Module: Value-Set-Based Assertion Checking

Author: Bjoern Wachter <bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_CHECK_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_CHECK_H

#include <util/ui_message.h>  

#include <analyses/ai.h>

#include "value_set_domain.h"
#include "value_sets.h"

class xmlt;

class value_set_checkt
{
public:
  value_set_checkt(value_set_analysist &_value_set_analysis,
                    const namespacet &_ns):
     value_set_analysis(_value_set_analysis),
     ns(_ns)
  {
  }

  // perform the checks
  void operator()(const goto_functionst&);
  void operator()(const goto_programt&);

  /* diagnostics */
  enum statust { INCONCLUSIVE, PASS, FAIL };

  struct property_entryt
  {
    statust status;
    irep_idt description;
  };
  
  typedef std::map<irep_idt, property_entryt> property_mapt;

  property_mapt property_map;

  // stream output
  void output(std::ostream &out) const;
  
  // XML output
  void convert(xmlt &dest) const;
  
protected:
  value_set_analysist &value_set_analysis;
  const namespacet &ns;

  exprt eval(
    const exprt &src,
    const value_sett &value_set,
    bool& inconclusive);
    
  exprt eval_rec(
    const exprt &src,
    const value_sett &value_set,
    bool negated,
    bool& inconclusive);

  bool is_null(const exprt &src);

  bool contains_null(const value_setst::valuest&);
  bool contains_invalid(const value_setst::valuest&);
};


void show_value_set_check(
  ui_message_handlert::uit ui,
  const value_set_checkt &value_set_check);


#endif
