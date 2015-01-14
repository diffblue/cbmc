/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: November 2005

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_XML_GOTO_TRACE_H
#define CPROVER_GOTO_SYMEX_XML_GOTO_TRACE_H

#include <util/xml.h>

#include <xmllang/graphml.h>

#include "goto_trace.h"
#include "cfg.h"

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  xmlt &xml);

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
#if 0
  const cfg_baset<empty_cfg_nodet> &cfg,
#endif
  graphmlt &graphml);

#endif
