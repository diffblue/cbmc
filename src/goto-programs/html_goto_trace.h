/*******************************************************************\

Module: HTML Traces of GOTO Programs

Author: elizabeth.polgreen@cs.ox.ac.uk

  Date: October 2017

\*******************************************************************/

/// \file
/// HTML races of GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_HTML_GOTO_TRACE_H_
#define CPROVER_GOTO_PROGRAMS_HTML_GOTO_TRACE_H_

#include <util/config.h>

void show_html_goto_trace(
  std::ostream &,
  const namespacet &,
  const goto_tracet &);



#endif /* CPROVER_GOTO_PROGRAMS_HTML_GOTO_TRACE_H_ */
