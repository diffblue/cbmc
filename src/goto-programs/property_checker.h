/*******************************************************************\

Module: Property Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Property Checker Interface

#ifndef CPROVER_GOTO_PROGRAMS_PROPERTY_CHECKER_H
#define CPROVER_GOTO_PROGRAMS_PROPERTY_CHECKER_H

// this is just an interface -- it won't actually do any checking!

#include <util/message.h>

#include "goto_trace.h"
#include "goto_model.h"

class property_resultst
{
public:
  enum class resultt { PASS, FAIL, ERROR, UNKNOWN };

  static std::string as_string(resultt);

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

  /// return the overall result; this is
  /// ERROR if any of the results is ERROR, otherwise
  /// FAIL if any of the results is FAIL, otherwise
  /// UNKNOWN if any of the results is UNKNOWN, otherwise
  /// PASS.
  resultt operatort() const;

  void initialize(const goto_functionst &);
};

class property_checkert : public messaget
{
public:
  property_checkert()
  {
  }

  explicit property_checkert(message_handlert &_message_handler);

  // Check whether all properties in goto_functions hold.
  virtual property_resultst operator()(const goto_modelt &) = 0;

protected:
  void initialize_property_map(const goto_functionst &);
};

#endif // CPROVER_GOTO_PROGRAMS_PROPERTY_CHECKER_H
