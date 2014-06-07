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
  property_checkert();

  explicit property_checkert(
    message_handlert &_message_handler);

  typedef enum { PASS, FAIL, ERROR } resultt;

  // Check whether all properties in goto_functions hold.

  virtual resultt operator()(
    const goto_modelt &goto_model)=0;

  struct property_statust
  {
    // this is the counterexample  
    goto_tracet error_trace;
    resultt result;
  };
  
  typedef goto_programt::const_targett loct;
  typedef std::map<loct, property_statust> property_mapt;
  property_mapt property_map;
};

#endif
