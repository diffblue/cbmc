/*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <limits>
#include <iostream>

#include <util/source_location.h>
#include <util/i2string.h>
#include <util/xml.h>

#include "symex_bmc_incremental_one_loop.h"

/*******************************************************************\

Function: symex_bmct::get_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmc_incremental_one_loopt::get_unwind(
  const symex_targett::sourcet &source,
  unsigned unwind)
{
  const irep_idt id=goto_programt::loop_id(source.pc);

  // We use the most specific limit we have,
  // and 'infinity' when we have none.

  unsigned this_loop_limit=std::numeric_limits<unsigned>::max();
  
  loop_limitst &this_thread_limits=
    thread_loop_limits[source.thread_nr];
    
  loop_limitst::const_iterator l_it=this_thread_limits.find(id);
  if(l_it!=this_thread_limits.end())
    this_loop_limit=l_it->second;
  else
  {
    l_it=loop_limits.find(id);
    if(l_it!=loop_limits.end())
      this_loop_limit=l_it->second;
    else if(max_unwind_is_set)
      this_loop_limit=max_unwind;
  }

  // use the incremental limits if 
  // it is the specified incremental loop or
  // there was no non-incremental limit
  if(id==incr_loop_id)
  {
    this_loop_limit = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
  }

  bool abort=unwind>=this_loop_limit;

  // report where we are  
  if(ui==ui_message_handlert::XML_UI)
  {
    xmlt xml("current-unwinding");
    xml.data=i2string(unwind);
    std::cout << xml << "\n";
  }

  statistics() << (abort?"Not unwinding":"Unwinding")
               << " loop " << id << " iteration "
               << unwind;

  if(this_loop_limit!=std::numeric_limits<unsigned>::max())
    statistics() << " (" << this_loop_limit << " max)";

  statistics() << " " << source.pc->source_location
               << " thread " << source.thread_nr << eom;

  return abort;
}

 /*******************************************************************\
 
Function: symex_bmct::check_break

 Inputs: source of the current symbolic execution state

 Outputs: true if the back edge encountered during symbolic execution 
            corresponds to the given loop (incr_loop_id)

 Purpose: defines condition for interrupting symbolic execution 
            for incremental BMC

\*******************************************************************/

bool symex_bmc_incremental_one_loopt::check_break(const irep_idt &id,
                             bool is_function, 
                             statet& state, 
                             const exprt &cond, 
                             unsigned unwind) 
{
  if(unwind < incr_min_unwind) return false;

#if 0
  std::cout << "loop limit for " << id 
            << (loop_limits.find(id)!=loop_limits.end() ? 
               " exists" : " does not exist") << std::endl;
#endif

#if 0
  loop_limitst &this_thread_limits=
    thread_loop_limits[state.source.thread_nr];
  if(incr_loop_id=="" && 
     this_thread_limits.find(id)==this_thread_limits.end() &&
     loop_limits.find(id)==loop_limits.end()) 
  {
    std::cout << "not statically unwound" << std::endl;
    //not a statically unwound loop when incremental
  }
#endif

  //loop specified by incrementalcheck
  return (id == incr_loop_id);
}
