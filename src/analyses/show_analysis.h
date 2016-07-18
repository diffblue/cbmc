/*******************************************************************\

Module: Show Analysis

Author: Daniel Kroening, kroening@kroening.com
        Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_ANALYSIS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_ANALYSIS_H

#include <util/ui_message.h>
#include <util/xml.h>
#include <util/namespace.h>

class goto_functionst;
class goto_programt;

// Interface for Analysis output

class show_analysist
{
public:
  virtual void output(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    std::ostream &out) const
    { return; }

  inline void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    std::ostream &out) const
    { return; }
  
  virtual void convert(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    xmlt &dest)
    { return; }

  virtual void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    xmlt &dest)
    { return; }

  virtual void show(
    const namespacet &ns,
    ui_message_handlert::uit ui,
    const goto_functionst &goto_functions);

  virtual void show(
    const namespacet &ns,
    ui_message_handlert::uit ui,
    const goto_programt &goto_program);  
};

#endif
