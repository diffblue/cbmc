/*******************************************************************\

Module: Goto Checker using Bounded Model Checking for Java

Author: Jeannie Moulton

 \*******************************************************************/

#include "java_multi_path_symex_checker.h"
#include "java_trace_validation.h"

goto_tracet java_multi_path_symex_checkert::build_full_trace() const
{
  goto_tracet goto_trace = multi_path_symex_checkert::build_full_trace();
  check_trace_assumptions(
    goto_trace, ns, log, options.get_bool_option("validate-trace"));
  return goto_trace;
}

goto_tracet
java_multi_path_symex_checkert::build_trace(const irep_idt &property_id) const
{
  goto_tracet goto_trace = multi_path_symex_checkert::build_trace(property_id);
  check_trace_assumptions(
    goto_trace, ns, log, options.get_bool_option("validate-trace"));
  return goto_trace;
}

goto_tracet java_multi_path_symex_checkert::build_shortest_trace() const
{
  goto_tracet goto_trace = multi_path_symex_checkert::build_shortest_trace();
  check_trace_assumptions(
    goto_trace, ns, log, options.get_bool_option("validate-trace"));
  return goto_trace;
}
