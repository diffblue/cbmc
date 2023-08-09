/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Weak Memory Instrumentation for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H
#define CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H

#include "wmm.h"

#include <util/irep.h>

class symbol_tablet;
class value_setst;
class goto_modelt;
class message_handlert;
class goto_programt;
class messaget;

void weak_memory(
  memory_modelt model,
  value_setst &,
  goto_modelt &,
  bool SCC,
  instrumentation_strategyt event_stategy,
  bool no_cfg_kill,
  bool no_dependencies,
  loop_strategyt duplicate_body,
  unsigned max_var,
  unsigned max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool cav11_option,
  bool hide_internals,
  message_handlert &,
  bool ignore_arrays);

void introduce_temporaries(
  value_setst &,
  symbol_tablet &,
  const irep_idt &function,
  goto_programt &,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  messaget &message);

#define OPT_WMM_MEMORY_MODEL  "(mm):"

#define OPT_WMM_INSTRUMENTATION_STRATEGIES                                     \
  "(one-event-per-cycle)"                                                      \
  "(minimum-interference)"                                                     \
  "(read-first)"                                                               \
  "(write-first)"                                                              \
  "(my-events)"

#define OPT_WMM_LIMITS                                                         \
  "(max-var):"                                                                 \
  "(max-po-trans):"

#define OPT_WMM_LOOPS                                                          \
  "(force-loop-duplication)"                                                   \
  "(no-loop-duplication)"

#define OPT_WMM_MISC                                                           \
  "(scc)"                                                                      \
  "(cfg-kill)"                                                                 \
  "(no-dependencies)"                                                          \
  "(no-po-rendering)"                                                          \
  "(render-cluster-file)"                                                      \
  "(render-cluster-function)"                                                  \
  "(cav11)"                                                                    \
  "(hide-internals)"                                                           \
  "(ignore-arrays)"

#define OPT_WMM                                                                \
  OPT_WMM_MEMORY_MODEL                                                         \
  OPT_WMM_INSTRUMENTATION_STRATEGIES                                           \
  OPT_WMM_LIMITS                                                               \
  OPT_WMM_LOOPS                                                                \
  OPT_WMM_MISC

#define HELP_WMM_FULL                                                          \
  " {y--mm} [{ytso}|{ypso}|{yrmo}|{ypower}] \t "                               \
  "instruments a weak memory model\n"                                          \
  " {y--scc} \t detects critical cycles per SCC (one thread per SCC)\n"        \
  " {y--one-event-per-cycle} \t only instruments one event per cycle\n"        \
  " {y--minimum-interference} \t instruments an optimal number of events\n"    \
  " {y--my-events} \t only instruments events whose ids appear in inst.evt\n"  \
  " {y--read-first}, {y--write-first} \t "                                     \
  "only instrument cycles where a read or write occurs as first event, "       \
  "respectively\n"                                                             \
  " {y--max-var} {uN} \t limit cycles to {uN} variables read/written\n"        \
  " {y--max-po-trans} {uN} \t limit cycles to {uN} program-order edges\n"      \
  " {y--ignore-arrays} \t instrument arrays as a single object\n"              \
  " {y--cav11} \t "                                                            \
  "always instrument shared variables, even when they are not part of "        \
  "any cycle\n"                                                                \
  " {y--force-loop-duplication}, {y--no-loop-duplication} \t "                 \
  "optional program transformation to construct cycles in program loops\n"     \
  " {y--cfg-kill} \t enables symbolic execution used to reduce spurious "      \
  "cycles\n"                                                                   \
  " {y--no-dependencies} \t no dependency analysis\n"                          \
  " {y--no-po-rendering} \t no representation of the threads in the dot\n"     \
  " {y--hide-internals} \t do not include thread-internal (Rfi) events in "    \
  "dot output\n"                                                               \
  " {y--render-cluster-file} \t clusterises the dot by files\n"                \
  " {y--render-cluster-function} \t clusterises the dot by functions\n"

#endif // CPROVER_GOTO_INSTRUMENT_WMM_WEAK_MEMORY_H
