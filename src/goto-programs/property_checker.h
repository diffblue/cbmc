/*******************************************************************\

Module: Property Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROPERTY_CHECKER_H
#define CPROVER_PROPERTY_CHECKER_H

// this is just an interface -- it won't actually do any checking!

#include <util/message.h>

#include "goto_trace.h"
#include "goto_model.h"

class property_checkert:public messaget
{
public:
  property_checkert()
  {
  }

  explicit property_checkert(
    message_handlert &_message_handler);

  typedef enum { PASS, FAIL, ERROR, UNKNOWN } resultt;
  
  static std::string as_string(resultt);

  // Check whether all properties in goto_functions hold.
  virtual resultt operator()(const goto_modelt &)=0;

  struct property_statust
  {
    // this is the counterexample  
    goto_tracet error_trace;
    resultt result;
    goto_programt::const_targett location;
  };
  
  // the irep_idt is the property id
  typedef std::map<irep_idt, property_statust> property_mapt;
  property_mapt property_map;

protected:
  void initialize_property_map(const goto_functionst &);
};

#endif
