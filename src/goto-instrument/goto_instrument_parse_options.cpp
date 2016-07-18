/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/expr_util.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/time_stopping.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>
#include <goto-programs/interpreter.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/parameter_assignments.h>
#include <goto-programs/goto_functions.h>

#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/value_set_analysis_cs.h>
#include <pointer-analysis/value_set_analysis_fics.h>
#include <pointer-analysis/value_set_check.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/sharing_analysis.h>

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>
#include <analyses/local_bitvector_analysis.h>
#include <analyses/goto_check.h>

#include <analyses/call_graph.h>
#include <analyses/interval_analysis.h>
#include <analyses/interval_domain.h>
#include <analyses/reaching_definitions.h>
#include <analyses/which_threads.h>
#include <analyses/lock_set_analysis.h>
#include <analyses/lock_set_analysis_cs.h>
#include <analyses/lock_graph_analysis.h>
#include <analyses/lock_graph_analysis_cs.h>
#include <analyses/escape_analysis.h>
#include <analyses/global_may_alias.h>
#include <analyses/custom_bitvector_analysis.h>
#include <analyses/dependence_graph.h>
#include <analyses/constant_propagator.h>
#include <analyses/ai_cs.h>
#include <analyses/cfg_dominators.h>
#include <analyses/in_loop.h>
#include <analyses/non_concurrent.h>
#include <analyses/print_locks_analysis_cs.h>
#include <analyses/get_target.h>
#include <analyses/simple_dependency_analysis.h>
#include <analyses/global_dependency_analysis.h>

#include <cbmc/version.h>

#include "goto_instrument_parse_options.h"
#include "document_properties.h"
#include "uninitialized.h"
#include "full_slicer.h"
#include "reachability_slicer.h"
#include "show_locations.h"
#include "points_to.h"
#include "alignment_checks.h"
#include "race_check.h"
#include "nondet_volatile.h"
#include "interrupt.h"
#include "mmio.h"
#include "stack_depth.h"
#include "nondet_static.h"
#include "rw_set.h"
#include "concurrency.h"
#include "dump_c.h"
#include "dot.h"
#include "havoc_loops.h"
#include "k_induction.h"
#include "function.h"
#include "branch.h"
#include "wmm/weak_memory.h"
#include "call_sequences.h"
#include "accelerate/accelerate.h"
#include "count_eloc.h"
#include "horn_encoding.h"
#include "thread_instrumentation.h"
#include "skip_loops.h"

#define CONTEXT_SENSITIVE

void goto_instrument_parse_optionst::sanitize_location_tags()
{
  status() << "Checking location tags" << eom;

  bool done_something=false;

  Forall_goto_functions(f_it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    goto_programt &goto_program=goto_function.body;

    Forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->function!=f_it->first)
      {
        done_something=true;
        i_it->function=f_it->first;
      }
    }
  }

  if(done_something)
  {
    status() << "Sanitized location tag(s)" << eom;
  }
  else
  {
    status() << "Sanitization was not necessary" << eom;
  }
}


/*******************************************************************\

Function: goto_instrument_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_instrument_parse_optionst::eval_verbosity()
{
  unsigned int v=8;
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10) v=10;
  }
  
  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int goto_instrument_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }
  
  if(cmdline.args.size()!=1 && cmdline.args.size()!=2)
  {
    help();
    return 0;
  }
  
  eval_verbosity();

  try
  {
    register_languages();

    get_goto_program();
    instrument_goto_program();

    bool debug;
    debug=ui_message_handler.get_verbosity()>=message_clientt::M_DEBUG;

#if 0
    bool stats;
    stats=ui_message_handler.get_verbosity()>=message_clientt::M_STATISTICS;
#endif

    typedef get_targett::rest rest;
    typedef ai_cs_stackt::locationt locationt;

    if(cmdline.isset("check-instructions"))
    {
      namespacet ns(symbol_table);

      if(cmdline.isset("remove-function-pointers"))
      {
        do_function_pointer_removal();
      }

      forall_goto_functions(f_it, goto_functions)
      {
        typedef goto_functionst::goto_functiont goto_functiont;

        const goto_functiont &goto_function=f_it->second;

        if(!goto_function.body_available())
          continue;

        std::cout << f_it->first << std::endl;
        std::cout << goto_function.type.pretty() << std::endl;
        std::cout << "========" << std::endl;

        const goto_programt &goto_program=goto_function.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          const goto_programt::instructiont &ins=*i_it;

          std::cout << ins.type << std::endl;
          if(ins.is_function_call())
          {
            const code_function_callt &code=to_code_function_call(ins.code);
            std::cout << code.pretty() << std::endl;
          }

          goto_program.output_instruction(ns, f_it->first, std::cout, i_it);
        }
      }

      return 0;
    }


    // to check arguments passed in from regression tests
    if(cmdline.isset("print-option"))
    {
      std::string s=cmdline.get_value("print-option");
      std::cout << "Option: " << s << std::endl;
      return 0;
    }


    if(cmdline.isset("print-code"))
    {
      namespacet ns(symbol_table);

      do_function_pointer_removal();
      do_remove_returns();

      get_targett get_target(goto_functions,  ns);
      std::string spec=cmdline.get_value("print-code");
      get_targett::rest res=get_target.from_spec(spec);
      chk(res.first, "");
      goto_programt::const_targett l=res.second;
      assert(!l->function.empty());

      std::ostringstream sstream;
      const goto_programt &goto_program
        =goto_functions.function_map.at(l->function).body;

      goto_program.output_instruction(ns, l->function, sstream, l);

      const codet &code=l->code;

      std::cout << code.pretty() << std::endl;

      return 0;
    }


    if(cmdline.isset("show-lock-dependencies-global"))
    {
      namespacet ns(symbol_table);

      do_function_pointer_removal();
      do_remove_returns();

      typedef goto_functionst::goto_functiont goto_functiont;
      typedef global_dependency_analysist::location_sett location_sett;

      std::vector<exprt> lock_exprs;
      location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(lock_exprs.empty())
      {
        std::cout << "No lock functions found" << std::endl;
        return 0;
      }

      location_sett result_locations;
      global_dependency_analysist gda(goto_functions, ns);
      gda(lock_exprs, result_locations);

      unsigned num_assignments=0;
      unsigned num_locations=0;

      forall_goto_functions(f_it, goto_functions)
      {
        const goto_functiont &goto_function=f_it->second;

        if(!goto_function.body_available())
          continue;

        const goto_programt &goto_program=goto_function.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          if(i_it->is_assign())
            num_assignments++;

          num_locations++;
        }
      }

      std::cout << "Number of lock expressions: " << lock_exprs.size()
        << std::endl;

      std::cout << "Number of assignments: " << num_assignments << std::endl;

      global_dependency_analysist::location_sett assignment_locations;
      for(location_sett::const_iterator it=result_locations.begin();
        it!=result_locations.end(); it++)
      {
        if((*it)->is_assign())
          assignment_locations.insert(*it);
      }

      std::cout << "Number of significant assignments: " <<
        assignment_locations.size() << std::endl;

      std::cout << "Number of locations: " << num_locations << std::endl;

      std::cout << "Number of significant locations: " <<
        result_locations.size() << std::endl;

      std::cout << "Lock statements: " << std::endl;
      for(location_sett::const_iterator it=lock_locations.begin();
          it!=lock_locations.end(); it++)
      {
        misc::output_goto_instruction(goto_functions, ns, std::cout, *it);
        std::cout << std::endl;
      }

#if 0
      std::cout << "Lock expressions: " << std::endl;
      for(std::vector<exprt>::const_iterator it=lock_exprs.begin();
          it!=lock_exprs.end(); it++)
      {
        std::cout << it->pretty() << std::endl;
      }
#endif

      std::cout << "Significant locations: " << std::endl;
      for(location_sett::const_iterator it=result_locations.begin();
          it!=result_locations.end(); it++)
      {
        misc::output_goto_instruction(goto_functions, ns, std::cout, *it);
        std::cout << std::endl;
      }

      return 0;
    }


    if(cmdline.isset("show-branch-dependencies-global"))
    {
      namespacet ns(symbol_table);

      do_function_pointer_removal();
      do_remove_returns();

      typedef goto_functionst::goto_functiont goto_functiont;
      typedef global_dependency_analysist::location_sett location_sett;

      // collect branch expressions
      std::vector<exprt> branch_exprs;
      forall_goto_functions(f_it, goto_functions)
      {
        const goto_functiont &goto_function=f_it->second;

        if(!goto_function.body_available())
          continue;

        const goto_programt &goto_program=goto_function.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          if(i_it->is_goto())
          {
            const exprt &guard=i_it->guard;
            branch_exprs.push_back(guard);
          }
        }
      }
      if(branch_exprs.empty())
      {
        std::cout << "No gotos found" << std::endl;
        return 0;
      }

      // do dependency analysis
      location_sett result_locations;
      global_dependency_analysist gda(goto_functions, ns);
      gda(branch_exprs, result_locations);

      unsigned num_assignments=0;
      unsigned num_locations=0;

      // count assignment locations and other locations
      forall_goto_functions(f_it, goto_functions)
      {
        const goto_functiont &goto_function=f_it->second;

        if(!goto_function.body_available())
          continue;

        const goto_programt &goto_program=goto_function.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          if(i_it->is_assign())
            num_assignments++;

          num_locations++;
        }
      }

      std::cout << "Number of branch expressions: " << branch_exprs.size()
        << std::endl;

      std::cout << "Number of assignments: " << num_assignments << std::endl;

      location_sett assignment_locations;
      for(location_sett::const_iterator it=result_locations.begin();
        it!=result_locations.end(); it++)
      {
        if((*it)->is_assign())
          assignment_locations.insert(*it);
      }

      std::cout << "Number of significant assignments: " <<
        assignment_locations.size() << std::endl;

      std::cout << "Number of locations: " << num_locations << std::endl;

      std::cout << "Number of significant locations: " <<
        result_locations.size() << std::endl;

      return 0;
    }


    // show assignments that could affect a lock operation
    if(cmdline.isset("show-lock-dependencies-simple"))
    {
      namespacet ns(symbol_table);

      do_function_pointer_removal();
      do_remove_returns();

      typedef goto_functionst::goto_functiont goto_functiont;

      // lock expressions
      typedef std::vector<exprt> expr_vect;
      expr_vect expr_vec;

      // locations of lock expressions
      typedef std::set<goto_programt::const_targett> location_sett;
      location_sett lock_location_set;

      unsigned num_assignments=0;
      unsigned num_locations=0;

      // Gather expressions used in lock operations, count number of
      // assignment statements
      forall_goto_functions(f_it, goto_functions)
      {
        const goto_functiont &goto_function=f_it->second;

        if(!goto_function.body_available())
          continue;

        const goto_programt &goto_program=goto_function.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          if(i_it->is_function_call())
          {
            irep_idt id=misc::get_function_name(i_it);
            if(id.empty())
              continue;

            std::string name=id2string(id);
            if(name==config.ansi_c.lock_function ||
               name==config.ansi_c.unlock_function)
            {
              const code_function_callt &code=to_code_function_call(i_it->code);
              const exprt &expr=code.op2();
              expr_vec.push_back(expr);
              lock_location_set.insert(i_it);
            }
          }
          else if(i_it->is_assign())
          {
#if 0
            if(id2string(f_it->first)=="main")
            {
              const code_assignt &assignment=to_code_assign(i_it->code);
              std::cout << assignment.pretty() << std::endl;
            }
#endif

            num_assignments++;
          }

          num_locations++;
        }
      }

      location_sett location_set;
      std::set<irep_idt> id_set;

      simple_dependency_analysist sda(goto_functions);
      if(!expr_vec.empty())
        sda(expr_vec, location_set, id_set);

      std::cout << "Number of lock expressions: " << expr_vec.size()
        << std::endl;

      std::cout << "Number of assignments: " << num_assignments << std::endl;

      location_sett assignment_locations;
      for(location_sett::const_iterator it=location_set.begin();
          it!=location_set.end(); it++)
      {
        if((*it)->is_assign())
          assignment_locations.insert(*it);
      }

      std::cout << "Number of significant assignments: " <<
        assignment_locations.size() << std::endl;

      std::cout << "Number of locations: " << num_locations << std::endl;

      std::cout << "Number of significant locations: " << location_set.size()
        << std::endl;

      std::cout << "Lock statements: " << std::endl;
      for(location_sett::const_iterator it=lock_location_set.begin();
          it!=lock_location_set.end(); it++)
      {
        misc::output_goto_instruction(goto_functions, ns, std::cout, *it);
        std::cout << std::endl;
      }

      std::cout << "Significant locations: " << std::endl;
      for(location_sett::const_iterator it=location_set.begin();
          it!=location_set.end(); it++)
      {
        misc::output_goto_instruction(goto_functions, ns, std::cout, *it);
        std::cout << std::endl;
      }

      return 0;
    }


    // Show lock operations in the code (including stacks, locations,
    // and abstract thread ids)
    if(cmdline.isset("print-locks"))
    {
      namespacet ns(symbol_table);

      do_function_pointer_removal();
      do_remove_returns();

      in_loopt in_loop(goto_functions);
      ai_cst<print_locks_domain_cst> print_locks_analysis(in_loop);
      print_locks_analysis(goto_functions, ns);
      print_locks_analysis.output(ns, goto_functions, std::cout);

      return 0;
    }


    if(cmdline.isset("non-concurrent") ||
       cmdline.isset("is-lock-protected") ||
       cmdline.isset("is-non-concurrent"))
    {
      namespacet ns(symbol_table);
      get_targett get_target(goto_functions, ns);

      chk(cmdline.isset("stack1"), "");
      chk(cmdline.isset("stack2"), "");
      chk(cmdline.isset("loc1"), "");
      chk(cmdline.isset("loc2"), "");

      std::string ss1=cmdline.get_value("stack1");
      std::string ss2=cmdline.get_value("stack2");
      std::string sl1=cmdline.get_value("loc1");
      std::string sl2=cmdline.get_value("loc2");

      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);
      value_set_analysis(goto_functions, ns);

      must_lock_set_analysis_cst must_lock_set_analysis(
        in_loop, value_set_analysis);
      must_lock_set_analysis(goto_functions, ns);

      if(debug)
      {
        must_lock_set_analysis.show(ns, get_ui(), goto_functions);
      }

      non_concurrentt non_concurrent(
        goto_functions,
        in_loop,
        value_set_analysis,
        must_lock_set_analysis,
        ns);

      ai_cs_stackt stack1;
      stack1.parse_stack(goto_functions, ns, ss1);
      ai_cs_stackt stack2;
      stack2.parse_stack(goto_functions, ns, ss2);

      rest res;

      res=get_target.from_spec(sl1);
      chk(res.first, "");
      locationt loc1=res.second;

      res=get_target.from_spec(sl2);
      chk(res.first, "");
      locationt loc2=res.second;

      typedef ai_cs_baset::placet placet;

      placet place1(stack1, loc1);
      placet place2(stack2, loc2);

      bool nc=false;
      if(cmdline.isset("non-concurrent"))
      {
        status() << "Full non concurrency check" << eom;
        nc=non_concurrent.non_concurrent(place1, place2);
      }
      else if(cmdline.isset("is-lock-protected"))
      {
        status() << "Lock protected check" << eom;
        nc=non_concurrent.is_lock_protected(place1, place2);
      }
      else if(cmdline.isset("is-non-concurrent"))
      {
        status() << "Non concurrency check" << eom;
        nc=non_concurrent.is_non_concurrent(place1, place2);
      }
      else
      {
        assert(false);
      }

#if 0
      std::cout << "Stack 1:" << std::endl;
      std::cout << stack1 << "\n" << std::endl;

      std::cout << "Stack 2" << std::endl;
      std::cout << stack2 << "\n" << std::endl;

      std::cout << "Location 1: " << loc1->location_number << std::endl;
      std::cout << "Location 2: " << loc2->location_number << std::endl;
#endif

      std::cout << "Result: ";
      std::cout << (nc ? "true" : "false") << std::endl;

      return 0;
    }


    if(cmdline.isset("has-path"))
    {
      status() << "Checking path" << eom;

      namespacet ns(symbol_table);

      std::string opt=cmdline.get_value("has-path");

      std::vector<std::string> svec;
      misc::split_string(opt, ':', svec, true);
      chk(svec.size()==2, "wrong argument");

      get_targett get_target(goto_functions, ns);
      get_targett::rest res;

      res=get_target.from_spec(svec[0]);
      chk(res.first, "");
      goto_programt::const_targett l1=res.second;

      res=get_target.from_spec(svec[1]);
      chk(res.first, "");
      goto_programt::const_targett l2=res.second;

      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);
      must_lock_set_analysis_cst must_lock_set_analysis(
        in_loop, value_set_analysis);
      must_lock_set_analysis(goto_functions, ns);

      non_concurrentt non_concurrent(
        goto_functions,
        in_loop,
        value_set_analysis,
        must_lock_set_analysis,
        ns);

      bool hp=non_concurrent.has_path(l1, l2);
      std::cout << "Has path: ";
      std::cout << (hp ? "true" : "false") << std::endl;

      return 0;
    }


    if(cmdline.isset("on-all-paths"))
    {
      status() << "Checking if loc is on all paths" << eom;

      namespacet ns(symbol_table);

      std::string opt=cmdline.get_value("on-all-paths");

      std::vector<std::string> svec;
      misc::split_string(opt, ':', svec, true);
      chk(svec.size()==3, "wrong argument");

      get_targett get_target(goto_functions, ns);
      get_targett::rest res;

      res=get_target.from_spec(svec[0]);
      chk(res.first, "");
      goto_programt::const_targett l1=res.second;

      res=get_target.from_spec(svec[1]);
      chk(res.first, "");
      goto_programt::const_targett l2=res.second;

      res=get_target.from_spec(svec[2]);
      chk(res.first, "");
      goto_programt::const_targett l3=res.second;

      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);
      must_lock_set_analysis_cst must_lock_set_analysis(
        in_loop, value_set_analysis);
      must_lock_set_analysis(goto_functions, ns);

      non_concurrentt non_concurrent(
        goto_functions,
        in_loop,
        value_set_analysis,
        must_lock_set_analysis,
        ns);

      bool oap=non_concurrent.on_all_paths(l1, l2, l3);
      std::cout << "On all paths: ";
      std::cout << (oap ? "true" : "false") << std::endl;

      return 0;
    }


    if (cmdline.isset("in-loop"))
    {
      status() << "Checking if loc is in loop" << eom;

      namespacet ns(symbol_table);

      std::string opt=cmdline.get_value("in-loop");

      get_targett get_target(goto_functions, ns);
      get_targett::rest res;

      res=get_target.from_spec(opt);
      chk(res.first, "");
      goto_programt::const_targett loc=res.second;

      in_loopt in_loop(goto_functions);

      bool il=in_loop.is_in_loop(loc);
      std::cout << "Is in loop: ";
      std::cout << (il ? "true" : "false") << std::endl;

      return 0;
    }


    if(cmdline.isset("print-reachable"))
    {
      status() << "Printing reachable locations with context" << eom;

      namespacet ns(symbol_table);

      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);

      in_loopt in_loop(goto_functions);

      ai_cst<ai_cs_domain_empty> ai_cs(in_loop);
      ai_cs(goto_functions, ns);
      ai_cs.output(ns, goto_functions, std::cout);

      std::cout << "Statistics" << std::endl;
      ai_cs.output_stats(std::cout);
      std::cout << std::endl;

      return 0;
    }


    if (cmdline.isset("check-stack"))
    {
      namespacet ns(symbol_table);

      status() << "Checking stack" << eom;

      std::string ss=cmdline.get_value("check-stack");

      ai_cs_stackt stack;
      stack.parse_stack(goto_functions, ns, ss);

      bool ivs=stack.is_valid_stack(goto_functions);
      std::cout << "Valid stack: ";
      std::cout << (ivs ? "true" : "false") << std::endl;

      return 0;
    }


    if (cmdline.isset("check-reachable"))
    {
      namespacet ns(symbol_table);

      status() << "Checking reachable locations with context" << eom;

      chk(cmdline.isset("loc"), "");

      std::string ss=cmdline.get_value_with_default("stack", "");
      std::string sl=cmdline.get_value("loc");

      ai_cs_stackt stack;
      stack.parse_stack(goto_functions, ns, ss);
      chk(stack.is_valid_stack(goto_functions), "invalid stack");

      get_targett get_target(goto_functions, ns);
      get_targett::rest res;

      res=get_target.from_spec(sl);
      chk(res.first, "");
      goto_programt::const_targett loc=res.second;

      in_loopt in_loop(goto_functions);

      ai_cst<ai_cs_domain_empty> ai_cs(in_loop);
      ai_cs(goto_functions, ns);

      ai_cs_baset::placet place(stack, loc);
      bool h=ai_cs.has(place);
      std::cout << "Is reachable: ";
      std::cout << (h ? "true" : "false") << std::endl;

      return 0;
    }


    if(cmdline.isset("show-dominators"))
    {
      status() << "Printing dominators" << eom;

      irep_idt id(cmdline.get_value("show-dominators"));

      goto_functionst::function_mapt::const_iterator it
        =goto_functions.function_map.find(id);
      if (it==goto_functions.function_map.end())
      {
        error() << "Function not found" << eom;
        return 0;
      }
      const goto_functionst::goto_functiont &goto_function=it->second;
      const goto_programt &goto_program=goto_function.body;

      cfg_dominatorst dominators;

      if(cmdline.isset("dominator-start"))
      {
        unsigned location_number;
        location_number=unsafe_string2unsigned(
          cmdline.get_value("dominator-start"));

        goto_programt::instructiont::const_targett target;
        forall_goto_program_instructions(it, goto_program)
        {
          if(it->location_number==location_number)
          {
            target=it;
            break;
          }
        }

        dominators(it->second.body, target);
      }
      else
      {
        dominators(it->second.body);
      }

      dominators.output(std::cout);
      return 0;
    }


    if(cmdline.isset("show-post-dominators"))
    {
      status() << "Printing post-dominators" << eom;

      irep_idt id(cmdline.get_value("show-post-dominators"));

      goto_functionst::function_mapt::const_iterator it
        =goto_functions.function_map.find(id);
      if (it==goto_functions.function_map.end())
      {
        error() << "Function not found" << eom;
        return 0;
      }
      const goto_functionst::goto_functiont &goto_function=it->second;
      const goto_programt &goto_program=goto_function.body;

      cfg_post_dominatorst post_dominators;

      if(cmdline.isset("dominator-start"))
      {
        unsigned location_number;
        location_number=unsafe_string2unsigned(
          cmdline.get_value("dominator-start"));

        goto_programt::instructiont::const_targett target;
        forall_goto_program_instructions(it, goto_program)
        {
          if(it->location_number==location_number)
          {
            target=it;
            break;
          }
        }

        post_dominators(it->second.body, target);
      }
      else
      {
        post_dominators(it->second.body);
      }

      post_dominators.output(std::cout);
      return 0;
    }


    if(cmdline.isset("which-threads"))
    {
      namespacet ns(symbol_table);

      status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, false);

      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);
    
      status() << "Which-Thread Analysis" << eom;
      which_threadst which_threads(goto_functions);

      which_threads.output(std::cout);
      return 0;
    }

    if(cmdline.isset("show-value-sets"))
    {
      namespacet ns(symbol_table);

      /*status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, false);

      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);*/
    
      status() << "Pointer Analysis" << eom;
#ifdef CONTEXT_SENSITIVE
      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);

#else
      value_set_analysist value_set_analysis;
#endif
      value_set_analysis(goto_functions, ns);

      status() << "Value Set Output" << eom;

      value_set_analysis.show(ns, get_ui(), goto_functions);

      return 0;
    }


    if(cmdline.isset("show-value-sets-fi"))
    {
      namespacet ns(symbol_table);

      status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, false);

      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);

      status() << "Pointer Analysis" << eom;
      in_loopt in_loop(goto_functions);
      value_set_analysis_ficst value_set_analysis(goto_functions, in_loop);
      value_set_analysis(goto_functions, ns);
      
#if 0
      status() << "Value Set Output" << eom;
      value_set_analysis.show(ns, get_ui(), goto_functions);
#endif
      
      return 0;
    }


    if(cmdline.isset("static-pointer-check"))
    {
      namespacet ns(symbol_table);

      status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, false);

      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);

      status() << "Pointer Analysis" << eom;
      value_set_analysist value_set_analysis;
      value_set_analysis(goto_functions, ns);

      status() << "Pointer Checks" << eom;
      value_set_checkt value_set_check(value_set_analysis, ns);
      value_set_check(goto_functions);

      show_value_set_check(get_ui(), value_set_check);

      return 0;
    }


    if(cmdline.isset("show-sharing"))
    {
      namespacet ns(symbol_table);

      status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, false);

      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);

      status() << "Pointer Analysis" << eom;
      value_set_analysist value_set_analysis;
      value_set_analysis(goto_functions, ns);

      status() << "Lock set Analysis" << eom;
      lock_set_analysist lock_set_analysis(value_set_analysis);
      lock_set_analysis(goto_functions, ns);

      status() << "Sharing Analysis" << eom;
      sharing_analysist sharing_analysis(
        ns,
        goto_functions,
        value_set_analysis,
        lock_set_analysis);

      show_sharing_analysis(get_ui(), sharing_analysis);

      return 0;
    }


    if(cmdline.isset("show-non-concurrency-stats"))
    {
      status() << "Non-concurrency stats" << eom;

      sanitize_location_tags();

      do_function_pointer_removal();
      do_remove_returns();

      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);

      in_loopt in_loop(goto_functions);

#if 0
      goto_functions.output(ns, status());
      status() << eom;
#endif

      typedef ai_cs_domain_empty edt;

      // find all places
      ai_cst<edt> ai_cs(in_loop);
      ai_cs(goto_functions, ns);

      // pointer information for non-concurrency analysis
      status() << "Pointer analysis" << eom;
      value_set_analysis_ficst vsa(goto_functions, in_loop);
      vsa(goto_functions, ns);

      // must lockset information for non-concurrency analysis
      status() << "Must lockset analysis" << eom;
      must_lock_set_analysis_cst must_lock_set_analysis(
        in_loop, vsa);
      must_lock_set_analysis(goto_functions, ns);

      non_concurrentt non_concurrent(
        goto_functions,
        in_loop,
        vsa,
        must_lock_set_analysis,
        ns);

      const ai_cst<edt>::state_mapt &state_map=ai_cs.get_state_map();

      const unsigned num_stacks=ai_cs.num_stacks();

      const unsigned num_pairs=1000; // pairs to collect
      const unsigned same_thread_threshold=50000;

      // pairs of places to collect
      typedef std::list<std::pair<ai_cst<edt>::placet, ai_cst<edt>::placet>>
        tmpt;
      tmpt places;

      srand(time(NULL));

      unsigned same_thread=0;
      unsigned i; // pairs collected so far

      status() << "Collecting all pairs" << eom;

      for(i=0; i<num_pairs && same_thread<same_thread_threshold;)
{
        unsigned stack_idx1=rand()%num_stacks;
        unsigned stack_idx2=rand()%num_stacks;
  
        ai_cst<edt>::state_mapt::const_iterator it1=state_map.begin();
        ai_cst<edt>::state_mapt::const_iterator it2=state_map.begin();

        std::advance(it1, stack_idx1);
        std::advance(it2, stack_idx2);
        assert(it1!=state_map.end());
        assert(it2!=state_map.end());

        // get stacks of places
        ai_cs_stackt stack1=ai_cs.get_stack(it1->first);
        ai_cs_stackt stack2=ai_cs.get_stack(it2->first);

        // copy
        ai_cs_stackt tid1=stack1;
        ai_cs_stackt tid2=stack2;

        // get thread ids associated with stacks
        tid1.remove_top_calls();
        tid2.remove_top_calls();

        if(tid1==tid2)
  {
          same_thread++;
          continue; // ignore same thread pairs
  }
  
        const ai_cst<edt>::location_mapt &lm1=it1->second;
        const ai_cst<edt>::location_mapt &lm2=it2->second;

        unsigned location_idx1=rand()%lm1.size();
        unsigned location_idx2=rand()%lm2.size();

        ai_cst<edt>::location_mapt::const_iterator l_it1=lm1.begin();
        ai_cst<edt>::location_mapt::const_iterator l_it2=lm2.begin();

        std::advance(l_it1, location_idx1);
        std::advance(l_it2, location_idx2);
        assert(l_it1!=lm1.end());
        assert(l_it2!=lm2.end());

        // get locations of places
        locationt l1=l_it1->first;
        locationt l2=l_it2->first;

        ai_cst<edt>::placet p1(stack1, l1);
        ai_cst<edt>::placet p2(stack2, l2);

        places.push_back(std::make_pair(p1, p2));
        i++;
}

      if(i<num_pairs)
      {
        result() << "Not enough places" << eom;
        return 0;
      }

      unsigned num_lock_protected=0;
      unsigned num_non_concurrent=0;
      unsigned num_create_join=0;

      absolute_timet time_start;
      time_periodt time_period;

      status() << "Non-concurrency check all" << eom;

      time_start=current_time();

      for(tmpt::const_iterator it=places.begin(); it!=places.end(); it++)
      {
        bool b1=non_concurrent.is_non_concurrent(it->first, it->second);
        bool b2=non_concurrent.is_lock_protected(it->first, it->second);

        if(b1)
          num_create_join++;

        if(b2)
          num_lock_protected++;

        if(b1 || b2)
          num_non_concurrent++;
      }

      time_period=current_time()-time_start;

      statistics() << "*** Statistics all" << eom;
      statistics() << "Non-concurrency runtime all: " << time_period << eom;
      statistics() << "Trials all: " << i << eom;
      statistics() << "Lock protected all: " << num_lock_protected << eom;
      statistics() << "Create join all: " << num_create_join << eom;
      statistics() << "Non concurrent all: " << num_non_concurrent << eom;

      status() << "Collecting lock places" << eom;

      // find lock places
      typedef list<ai_cst<edt>::placet> lock_placest;
      lock_placest lock_places;

      for(ai_cst<edt>::state_mapt::const_iterator it=state_map.begin();
          it!=state_map.end(); it++)
{
        const ai_cst<edt>::location_mapt &lm=it->second;

        for(ai_cst<edt>::location_mapt::const_iterator l_it=lm.begin();
            l_it!=lm.end(); l_it++)
  {
          if(l_it->first->is_function_call())
          {
            irep_idt id=misc::get_function_name(l_it->first);
            if(id.empty())
              continue;

            std::string name=id2string(id);
            if(name==config.ansi_c.lock_function ||
               name==config.ansi_c.unlock_function)
            {
              ai_cs_stackt stack=ai_cs.get_stack(it->first);
              ai_cst<edt>::placet p(stack, l_it->first);
              lock_places.push_back(p);
            }
          }
        }
  }
  
      unsigned num_lock_trials=0;
      unsigned num_lock_lock_protected=0;
      unsigned num_lock_non_concurrent=0;
      unsigned num_lock_create_join=0;

      status() << "Non-concurrency check locks" << eom;

      for(lock_placest::const_iterator it1=lock_places.begin();
          it1!=lock_places.end(); it1++)
  {
        for(lock_placest::const_iterator it2=lock_places.begin();
            it2!=lock_places.end(); it2++)
        {
          ai_cs_stackt stack1=it1->first;
          ai_cs_stackt stack2=it2->first;
          stack1.remove_top_calls();
          stack2.remove_top_calls();

          if(stack1==stack2)
            continue;

          num_lock_trials++;

          bool b1=non_concurrent.is_non_concurrent(*it1, *it2);
          bool b2=non_concurrent.is_lock_protected(*it1, *it2);

          if(b1)
            num_lock_create_join++;

          if(b2)
            num_lock_lock_protected++;

          if(b1 || b2)
            num_lock_non_concurrent++;
        }

        if(num_lock_trials>=10*num_pairs)
        {
          break;
        }
      }

      statistics() << "*** Statistics locks" << eom;
      statistics() << "Trials locks: " << num_lock_trials << eom;
      statistics() << "Lock protected locks: " << num_lock_lock_protected <<
        eom;
      statistics() << "Create join locks: " << num_lock_create_join << eom;
      statistics() << "Non concurrent locks: " << num_lock_non_concurrent <<
        eom;

    return 0;
  }
  

    if(cmdline.isset("show-framework-stats"))
  {
      status() << "Framework stats" << eom;

      sanitize_location_tags();

      do_function_pointer_removal();
      do_remove_returns();
      goto_functions.update();

      namespacet ns(symbol_table);

      in_loopt in_loop(goto_functions);

      stack_numberingt stack_numbering;
      trie_stack_numberingt trie_stack_numbering;

      ai_cst<ai_cs_domain_empty> *ai_cs;

      if(cmdline.isset("use-trie-numbering"))
        ai_cs=new ai_cst<ai_cs_domain_empty>(in_loop, trie_stack_numbering);
      else
        ai_cs=new ai_cst<ai_cs_domain_empty>(in_loop, stack_numbering);

      (*ai_cs)(goto_functions, ns);
      ai_cs->output_stats(statistics());
      statistics() << eom;

      delete ai_cs;

      return 0;
    }


    if(cmdline.isset("show-simple-dependency-analysis-stats"))
    {
      status() << "Simple dependency analysis stats" << eom;

      sanitize_location_tags();

      do_function_pointer_removal();
      do_remove_returns();
      goto_functions.update();
    
      namespacet ns(symbol_table);

      // collect lock operations
      std::vector<exprt> lock_exprs;
      simple_dependency_analysist::location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(lock_exprs.empty())
      {
        result() << "No lock operations" << eom;
        return 0;
      }

      assert(!lock_exprs.empty());

      simple_dependency_analysist::id_sett id_set;
      simple_dependency_analysist::location_sett location_set;
      simple_dependency_analysist sda(goto_functions, true);

      absolute_timet time_start;
      time_periodt time_period;

      time_start=current_time();

      sda(lock_exprs, location_set, id_set);

      time_period=current_time()-time_start;
      statistics() << " (" << time_period << "s)" << eom;

      sda.output_stats(statistics());
      statistics() << eom;

      return 0;
    }


    if(cmdline.isset("show-deadlocks"))
    {
#if 0
      //sanitize missing function names in goto program
      Forall_goto_functions(f_it, goto_functions)
      {
        if(!f_it->second.body_available())
          continue;
#if 0
        if(f_it->first != f_it->second.body.instructions.begin()->function)
          status() << "FUN!=BEGIN: " << f_it->first << " != " << f_it->second.body.instructions.begin()->function << eom;
        if(f_it->first != (--f_it->second.body.instructions.end())->function)
          status() << "FUN!=END:   " << f_it->first << " != " << (--f_it->second.body.instructions.end())->function << eom;
        if(f_it->second.body.instructions.begin()->function != (--f_it->second.body.instructions.end())->function)
          status() << "BEGIN!=END: " << f_it->second.body.instructions.begin()->function  << " != " << (--f_it->second.body.instructions.end())->function << eom;
#endif  
        f_it->second.body.instructions.begin()->function=f_it->first;
        (--f_it->second.body.instructions.end())->function=f_it->first;
        assert(f_it->second.body.instructions.begin()->function==f_it->first);
        assert(f_it->second.body.instructions.begin()->function==(--f_it->second.body.instructions.end())->function);
      }
#endif 

      sanitize_location_tags();

      absolute_timet time_start;
      time_periodt time_period;
#if 1
      do_function_pointer_removal();
      do_remove_returns();
      goto_functions.update();
#endif

      namespacet ns(symbol_table);

      // collect lock operations
      std::vector<exprt> lock_exprs;
      simple_dependency_analysist::location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(lock_exprs.empty())
      {
        result() << "No lock operations" << eom;
        result() << "* potential deadlocks 0" << eom;
        return 0;
      }

#ifdef CONTEXT_SENSITIVE
      in_loopt in_loop(goto_functions);

#if 0
      status() << "Gathering statistics" << eom;
      ai_cst<ai_cs_domain_empty> ai_cs(in_loop);
      ai_cs(goto_functions, ns);
      ai_cs.output_stats(statistics());
      statistics() << eom;
      ai_cs.clear(); // free memory
#endif

      // stack numbering used by all analyses
      stack_numberingt stack_numbering;

      value_set_analysis_cst *vsa;
      if(cmdline.isset("flow-insensitive-value-set-analysis"))
        vsa=new value_set_analysis_ficst(
          goto_functions,
          in_loop,
          stack_numbering);
      else
        vsa=new value_set_analysis_cst(
          in_loop,
          stack_numbering);
      value_set_analysis_cst &value_set_analysis=*vsa;

      bool sda_ii=cmdline.isset("simple-dependency-analysis-ii");
      bool sda_is=cmdline.isset("simple-dependency-analysis-is");
      assert(!(sda_ii && sda_is));

      if(sda_ii || sda_is)
      {
        status() << "Simple Dependency Analysis";

        assert(!lock_exprs.empty());

        time_start=current_time();

        simple_dependency_analysist::id_sett id_set;
        simple_dependency_analysist sda(goto_functions, sda_ii);
        sda(lock_exprs, value_set_analysis.get_slice(), id_set);

        time_period=current_time()-time_start;
        statistics() << " (" << time_period << "s)" << eom;

        sda.output_stats(statistics());
        statistics() << eom;
      }

#if 0
      std::vector<exprt> lock_exprs;
      global_dependency_analysist::location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(!lock_exprs.empty())
      {
        global_dependency_analysist gda(goto_functions, ns);
        gda(lock_exprs, value_set_analysis.get_slice());
      }
#endif

      status() << "Pointer Analysis";

      time_start=current_time();
      value_set_analysis(goto_functions, ns);
      time_period=current_time()-time_start;
      statistics() << " (" << time_period << "s)" << eom;
#if defined(USE_MAP_ONE) && !(defined(FLOW_INSENSITIVE))
      const value_set_analysis_cst::state_map_onet &smo
        =value_set_analysis.get_state_map_one();
      statistics() << "Number of stacks/states: " << smo.size() << eom;;
      statistics() << "Number of unique states: " << smo.size_unique() << eom;
#endif

#if 0
      goto_functions.output(ns, status());
#endif

      time_start=current_time();
      status() << "May Lock Set Analysis";
      may_lock_set_analysis_cst lock_set_analysis(
        in_loop,
        value_set_analysis,
        stack_numbering);
      lock_set_analysis(goto_functions, ns);
      time_period=current_time()-time_start;
      statistics() << " (" << time_period << "s)" << eom;
      
      time_start=current_time();
      status() << "Must Lock Set Analysis";
      must_lock_set_analysis_cst must_lock_set_analysis(
        in_loop, value_set_analysis, stack_numbering);
      must_lock_set_analysis(goto_functions, ns);
      time_period=current_time()-time_start;
      statistics() << " (" << time_period << "s)" << eom;
      must_lock_set_analysis.output_stats(statistics());

      time_start = current_time();
      status() << "Construct Lock Graph";
      non_concurrentt non_concurrent(
        goto_functions,
        in_loop,
        value_set_analysis,
        must_lock_set_analysis,
        ns);
      lock_graph_analysis_cst lock_graph_analysis(
        in_loop,
        non_concurrent,
        lock_set_analysis,
        stack_numbering);
      lock_graph_analysis(goto_functions, ns);
      time_period=current_time()-time_start;
      statistics() << " (" << time_period << "s)" << eom;
      lock_graph_analysis.show(ns, get_ui(), goto_functions);

      time_start=current_time();
      status() << "Check Cycles";
      lock_graph_analysis.detect_deadlocks();
      time_period=current_time()-time_start;
      statistics() << " (" << time_period << "s)" << eom;
      lock_graph_analysis.show_deadlocks(ns, get_ui());

      delete vsa; // value set analysis

#else
      status() << "Pointer Analysis" << eom;
      value_set_analysist value_set_analysis;
      value_set_analysis(goto_functions, ns);

      status() << "Which-Thread Analysis" << eom;
      which_threads_internalt which_threads(goto_functions);

      status() << "Lock Set Analysis" << eom;
      lock_set_analysist lock_set_analysis(value_set_analysis);
      lock_set_analysis(goto_functions, ns);

      status() << "Construct Lock Graph" << eom;
      lock_graph_analysist lock_graph_analysis(lock_set_analysis, which_threads);
      lock_graph_analysis(goto_functions, ns);
      lock_graph_analysis.show(ns, get_ui(), goto_functions);

      lock_graph_analysis.detect_deadlocks();
      show_deadlocks(ns, get_ui(), goto_functions, lock_graph_analysis);
#endif

      return 0;
    }


    if(cmdline.isset("show-may-lock-sets"))
    {
      namespacet ns(symbol_table);

      status() << "Pointer Analysis" << eom;
      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);

      std::vector<exprt> lock_exprs;
      simple_dependency_analysist::location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(!lock_exprs.empty())
      {
	simple_dependency_analysist::id_sett id_set;
        simple_dependency_analysist sda(goto_functions);
        sda(lock_exprs, value_set_analysis.get_slice(), id_set);
      }

      value_set_analysis(goto_functions, ns);

      status() << "Lock set Analysis" << eom;
      may_lock_set_analysis_cst lock_set_analysis(in_loop, value_set_analysis);
      lock_set_analysis(goto_functions, ns);
      lock_set_analysis.show(ns, get_ui(), goto_functions);

      return 0;
    }


    if(cmdline.isset("show-must-lock-sets"))
    {
      namespacet ns(symbol_table);

      status() << "Pointer Analysis" << eom;
      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);

      std::vector<exprt> lock_exprs;
      simple_dependency_analysist::location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(!lock_exprs.empty())
      {
	simple_dependency_analysist::id_sett id_set;
        simple_dependency_analysist sda(goto_functions);
        sda(lock_exprs, value_set_analysis.get_slice(), id_set);
      }

      value_set_analysis(goto_functions, ns);

      status() << "Lock set Analysis" << eom;
      must_lock_set_analysis_cst lock_set_analysis(in_loop, value_set_analysis);
      lock_set_analysis(goto_functions, ns);
      lock_set_analysis.show(ns, get_ui(), goto_functions);

      return 0;
    }


    if(cmdline.isset("show-lock-sets"))
    {
      namespacet ns(symbol_table);

#ifndef CONTEXT_SENSITIVE
      status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, false);
#endif

      status() << "Pointer Analysis" << eom;
#ifdef CONTEXT_SENSITIVE
      in_loopt in_loop(goto_functions);
      value_set_analysis_cst value_set_analysis(in_loop);

      std::vector<exprt> lock_exprs;
      simple_dependency_analysist::location_sett lock_locations;
      collect_lock_operations(goto_functions, lock_exprs, lock_locations);
      if(!lock_exprs.empty())
      {
	simple_dependency_analysist::id_sett id_set;
        simple_dependency_analysist sda(goto_functions);
        sda(lock_exprs, value_set_analysis.get_slice(), id_set);
      }
#else
      value_set_analysist value_set_analysis;
#endif
      value_set_analysis(goto_functions, ns);

      goto_functions.output(ns, std::cout);

      status() << "Lock set Analysis" << eom;
#ifdef CONTEXT_SENSITIVE
      may_lock_set_analysis_cst lock_set_analysis(in_loop, value_set_analysis);
#else
      lock_set_analysist lock_set_analysis(value_set_analysis);
#endif
      lock_set_analysis(goto_functions, ns);

      lock_set_analysis.show(ns, get_ui(), goto_functions);

      return 0;
    }

    if(cmdline.isset("show-local-may-alias"))
    {
      do_function_pointer_removal();
      do_partial_inlining();

      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);
    
      forall_goto_functions(it, goto_functions)
      {
        std::cout << ">>>>" << std::endl;
        std::cout << ">>>> " << it->first << std::endl;
        std::cout << ">>>>" << std::endl;
        local_may_aliast local_may_alias(it->second);
        local_may_alias.output(std::cout, it->second, ns);
        std::cout << std::endl;
      }

      return 0;
    }

    if(cmdline.isset("show-global-may-alias"))
    {
      do_function_pointer_removal();
      do_partial_inlining();
      do_remove_returns();
      parameter_assignments(symbol_table, goto_functions);

      // recalculate numbers, etc.
      goto_functions.update();
      
      namespacet ns(symbol_table);
      global_may_alias_analysist global_may_alias_analysis;
      global_may_alias_analysis(goto_functions, ns);
      global_may_alias_analysis.output(ns, goto_functions, std::cout);

      return 0;
    }

    if(cmdline.isset("show-local-bitvector-analysis"))
    {
      do_function_pointer_removal();
      do_partial_inlining();
      parameter_assignments(symbol_table, goto_functions);
    
      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);

      forall_goto_functions(it, goto_functions)
      {
        local_bitvector_analysist local_bitvector_analysis(it->second);
        std::cout << ">>>>" << std::endl;
        std::cout << ">>>> " << it->first << std::endl;
        std::cout << ">>>>" << std::endl;
        local_bitvector_analysis.output(std::cout, it->second, ns);
        std::cout << std::endl;
      }

      return 0;
    }
    
    if(cmdline.isset("show-custom-bitvector-analysis"))
    {
      do_function_pointer_removal();
      do_partial_inlining();
      do_remove_returns();
      parameter_assignments(symbol_table, goto_functions);
      
      remove_unused_functions(goto_functions, get_message_handler());
      
      if(!cmdline.isset("inline"))
      {
        thread_exit_instrumentation(goto_functions);
        mutex_init_instrumentation(symbol_table, goto_functions);
      }

      // recalculate numbers, etc.
      goto_functions.update();
      
      namespacet ns(symbol_table);
      custom_bitvector_analysist custom_bitvector_analysis;
      custom_bitvector_analysis(goto_functions, ns);
      custom_bitvector_analysis.output(ns, goto_functions, std::cout);

      return 0;
    }

    if(cmdline.isset("show-escape-analysis"))
    {
      do_function_pointer_removal();
      do_partial_inlining();
      do_remove_returns();
      parameter_assignments(symbol_table, goto_functions);

      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);

      escape_analysist escape_analysis;
      escape_analysis(goto_functions, ns);

      escape_analysis.output(ns, goto_functions, std::cout);

      return 0;
    }

    if(cmdline.isset("custom-bitvector-analysis"))
    {
      do_function_pointer_removal();
      do_partial_inlining();
      do_remove_returns();
      parameter_assignments(symbol_table, goto_functions);

      remove_unused_functions(goto_functions, get_message_handler());
    
      if(!cmdline.isset("inline"))
      {
        thread_exit_instrumentation(goto_functions);
        mutex_init_instrumentation(symbol_table, goto_functions);
      }

      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);

      custom_bitvector_analysist custom_bitvector_analysis;
      custom_bitvector_analysis(goto_functions, ns);
      custom_bitvector_analysis.check(ns, goto_functions, cmdline.isset("xml-ui"), std::cout);

      return 0;
    }

    if(cmdline.isset("show-points-to"))
    {
      do_function_pointer_removal();
      do_partial_inlining();

      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);

      status() << "Pointer Analysis" << eom;
      points_tot points_to;
      points_to(goto_functions);
      points_to.output(std::cout);
      return 0;
    }
    
    if(cmdline.isset("show-intervals"))
    {
      do_function_pointer_removal();
      do_partial_inlining();

      // recalculate numbers, etc.
      goto_functions.update();

      status() << "Interval Analysis" << eom;
      namespacet ns(symbol_table);
      ait<interval_domaint> interval_analysis;
      interval_analysis(goto_functions, ns);
      
      interval_analysis.output(ns, goto_functions, std::cout);
      return 0;
    }
    
    if(cmdline.isset("show-call-sequences"))
    {
      show_call_sequences(goto_functions);
      return 0;
    }

    if(cmdline.isset("check-call-sequence"))
    {
      do_remove_returns();
      check_call_sequence(goto_functions);
      return 0;
    }

    if(cmdline.isset("show-rw-set"))
    {
      namespacet ns(symbol_table);

      if(!cmdline.isset("inline"))
      {
        do_function_pointer_removal();
        do_partial_inlining();

        // recalculate numbers, etc.
        goto_functions.update();
      }
    
      status() << "Pointer Analysis" << eom;
      value_set_analysist value_set_analysis;
      value_set_analysis(goto_functions, ns);
      
      const symbolt &symbol=ns.lookup(ID_main);
      symbol_exprt main(symbol.name, symbol.type);
      
      std::cout << rw_set_functiont(value_set_analysis, ns, goto_functions, main);
      return 0;
    }

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table();
      return 0;
    }

    if(cmdline.isset("show-reaching-definitions"))
    {
      do_function_pointer_removal();

      const namespacet ns(symbol_table);
      reaching_definitions_analysist rd_analysis(ns);
      rd_analysis(goto_functions, ns);

      forall_goto_functions(f_it, goto_functions)
      {
        if(f_it->second.body_available())
        {
          std::cout << "////" << std::endl;
          std::cout << "//// Function: " << f_it->first << std::endl;
          std::cout << "////" << std::endl;
          std::cout << std::endl;
          rd_analysis.output(ns, f_it->second.body, std::cout);
        }
      }

      return 0;
    }

    if(cmdline.isset("show-dependence-graph"))
    {
      do_function_pointer_removal();

      const namespacet ns(symbol_table);
      dependence_grapht dependence_graph(ns);
      dependence_graph(goto_functions, ns);

      forall_goto_functions(f_it, goto_functions)
      {
        if(f_it->second.body_available())
        {
          std::cout << "////" << std::endl;
          std::cout << "//// Function: " << f_it->first << std::endl;
          std::cout << "////" << std::endl;
          std::cout << std::endl;
          dependence_graph.output(ns, f_it->second.body, std::cout);
        }
      }

      dependence_graph.output_dot(std::cout);

      return 0;
    }

    if(cmdline.isset("count-eloc"))
    {
      count_eloc(goto_functions);
      return 0;
    }

    if(cmdline.isset("list-symbols"))
    {
      show_symbol_table(true);
      return 0;
    }

    if(cmdline.isset("show-uninitialized"))
    {
      show_uninitialized(symbol_table, goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("interpreter"))
    {
      status() << "Starting interpreter" << eom;
      interpreter(symbol_table, goto_functions);
      return 0;
    }

    if(cmdline.isset("show-claims") ||
       cmdline.isset("show-properties"))
    {
      const namespacet ns(symbol_table);
      show_properties(ns, get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("document-claims-html") ||
       cmdline.isset("document-properties-html"))
    {
      document_properties_html(goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("document-claims-latex") ||
       cmdline.isset("document-properties-latex"))
    {
      document_properties_latex(goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("show-natural-loops"))
    {
      const namespacet ns(symbol_table);
      show_natural_loops(goto_functions);
      return 0;
    }

    if(cmdline.isset("show-goto-functions"))
    {
      namespacet ns(symbol_table);

      if(cmdline.isset("remove-function-pointers"))
      {
        do_function_pointer_removal();
      }
      if(cmdline.isset("remove-returns"))
      {
        do_remove_returns();
      }

      goto_functions.output(ns, std::cout);
      return 0;
    }

    if(cmdline.isset("list-undefined-functions"))
    {
      Forall_goto_functions(it, goto_functions)
        if(!it->second.body_available())
          std::cout << it->first << std::endl;
      return 0;
    }

    // experimental: print structs
    if(cmdline.isset("show-struct-alignment"))
    {
      print_struct_alignment_problems(symbol_table, std::cout);
      return 0;
    }

    if(cmdline.isset("show-locations"))
    {
      show_locations(get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("dump-c") || cmdline.isset("dump-cpp"))
    {
      const bool is_cpp=cmdline.isset("dump-cpp");
      const bool h=cmdline.isset("use-system-headers");
      namespacet ns(symbol_table);

      // restore RETURN instructions in case remove_returns had been
      // applied
      restore_returns(symbol_table, goto_functions);
      
      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]).c_str());
        #else
        std::ofstream out(cmdline.args[1].c_str());
        #endif
        if(!out)
        {
          error() << "failed to write to `" << cmdline.args[1] << "'";
          return 10;
        }
        (is_cpp ? dump_cpp : dump_c)(goto_functions, h, ns, out);
      }
      else
        (is_cpp ? dump_cpp : dump_c)(goto_functions, h, ns, std::cout);
        
      return 0;
    }
    
    if(cmdline.isset("call-graph"))
    {
      call_grapht call_graph(goto_functions);
      
      if(cmdline.isset("xml"))
        call_graph.output_xml(std::cout);
      else if(cmdline.isset("dot"))
        call_graph.output_dot(std::cout);
      else
        call_graph.output(std::cout);

      return 0;
    }
    
    if(cmdline.isset("dot"))
    {
      namespacet ns(symbol_table);
      
      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]).c_str());
        #else
        std::ofstream out(cmdline.args[1].c_str());
        #endif
        if(!out)
        {
          error() << "failed to write to " << cmdline.args[1] << "'";
          return 10;
        }

        dot(goto_functions, ns, out);
      }
      else
        dot(goto_functions, ns, std::cout);
        
      return 0;
    }

    if(cmdline.isset("accelerate"))
    {
      do_function_pointer_removal();
    
      namespacet ns(symbol_table);

      status() << "Performing full inlining" << eom;
      goto_inline(goto_functions, ns, ui_message_handler);

      status() << "Accelerating" << eom;
      accelerate_functions(goto_functions, symbol_table, cmdline.isset("z3"));
      remove_skip(goto_functions);
      goto_functions.update();
    }
    
    if(cmdline.isset("horn-encoding"))
    {
      status() << "Horn-clause encoding" << eom;
      namespacet ns(symbol_table);
      
      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]).c_str());
        #else
        std::ofstream out(cmdline.args[1].c_str());
        #endif
        
        if(!out)
        {
          error() << "Failed to open output file "
                  << cmdline.args[1] << eom;
          return 1;
        }
        
        horn_encoding(goto_functions, ns, out);
      }
      else
        horn_encoding(goto_functions, ns, std::cout);
        
      return 0;
    }
    
    // write new binary?
    if(cmdline.args.size()==2)
    {
      status() << "Writing GOTO program to `" << cmdline.args[1] << "'" << eom;
      
      if(write_goto_binary(
        cmdline.args[1], symbol_table, goto_functions, get_message_handler()))
        return 1;
      else
        return 0;
    }

    help();
    return 0;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 11;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return 11;
  }
  
  catch(int)
  {
    return 11;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return 11;
  }
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::do_function_pointer_removal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parse_optionst::do_function_pointer_removal()
{
  if(function_pointer_removal_done) return;
  function_pointer_removal_done=true;

  status() << "Function Pointer Removal" << eom;
  remove_function_pointers(symbol_table, goto_functions, false);
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::do_partial_inlining

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parse_optionst::do_partial_inlining()
{
  if(partial_inlining_done) return;
  partial_inlining_done=true;

  if(!cmdline.isset("inline"))
  {
    status() << "Partial Inlining" << eom;
    const namespacet ns(symbol_table);
    goto_partial_inline(goto_functions, ns, ui_message_handler);
  }
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::do_remove_returns

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parse_optionst::do_remove_returns()
{
  if(remove_returns_done) return;
  remove_returns_done=true;

  status() << "Removing returns" << eom;
  remove_returns(symbol_table, goto_functions);
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parse_optionst::get_goto_program()
{
  status() << "Reading GOTO program from `" << cmdline.args[0] << "'" << eom;

  if(read_goto_binary(cmdline.args[0],
    symbol_table, goto_functions, get_message_handler()))
    throw 0;

  config.set(cmdline);
  config.set_from_symbol_table(symbol_table);
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::instrument_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parse_optionst::instrument_goto_program()
{
  optionst options;

  // disable simplify when adding various checks?
  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);
  else
    options.set_option("simplify", true);

  // use assumptions instead of assertions?
  if(cmdline.isset("assert-to-assume"))
    options.set_option("assert-to-assume", true);
  else
    options.set_option("assert-to-assume", false);

  // check array bounds
  if(cmdline.isset("bounds-check"))
    options.set_option("bounds-check", true);
  else
    options.set_option("bounds-check", false);

  // check division by zero
  if(cmdline.isset("div-by-zero-check"))
    options.set_option("div-by-zero-check", true);
  else
    options.set_option("div-by-zero-check", false);

  // check undefined shifts
  if(cmdline.isset("undefined-shift-check"))
    options.set_option("undefined-shift-check", true);
  else
    options.set_option("undefined-shift-check", false);

  // check overflow/underflow
  if(cmdline.isset("signed-overflow-check"))
    options.set_option("signed-overflow-check", true);
  else
    options.set_option("signed-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("unsigned-overflow-check"))
    options.set_option("unsigned-overflow-check", true);
  else
    options.set_option("unsigned-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("float-overflow-check"))
    options.set_option("float-overflow-check", true);
  else
    options.set_option("float-overflow-check", false);

  // check for NaN (not a number)
  if(cmdline.isset("nan-check"))
    options.set_option("nan-check", true);
  else
    options.set_option("nan-check", false);

  // check pointers
  if(cmdline.isset("pointer-check"))
    options.set_option("pointer-check", true);
  else
    options.set_option("pointer-check", false);

  // check pointers
  if(cmdline.isset("memory-leak-check"))
    options.set_option("memory-leak-check", true);
  else
    options.set_option("memory-leak-check", false);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_value("error-label"));

  // unwind loops 
  if(cmdline.isset("unwind"))
  {
    status() << "Unwinding loops" << eom;
    options.set_option("unwind", cmdline.get_value("unwind"));
  }

  // skip over selected loops
  if(cmdline.isset("skip-loops"))
  {
    status() << "Adding gotos to skip loops" << eom;
    if(skip_loops(
        goto_functions,
        cmdline.get_value("skip-loops"),
        get_message_handler()))
      throw 0;
  }

  // we add the library in some cases, as some analyses benefit

  if(cmdline.isset("add-library") ||
     cmdline.isset("mm"))
  {
    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
      config.ansi_c.defines.push_back("__CPROVER_CUSTOM_BITVECTOR_ANALYSIS");
  
    status() << "Adding CPROVER library" << eom;
    link_to_library(symbol_table, goto_functions, ui_message_handler);
  }

  namespacet ns(symbol_table);

  if(cmdline.isset("show-custom-bitvector-analysis") ||
     cmdline.isset("custom-bitvector-analysis"))
  {
    partial_inlining_done=true;
    status() << "Partial Inlining" << eom;
    const namespacet ns(symbol_table);
    goto_partial_inline(goto_functions, ns, ui_message_handler);
    status() << "Propagating Constants" << eom;
    constant_propagator_ait constant_propagator_ai(goto_functions, ns);
    remove_skip(goto_functions);
  }

  if(cmdline.isset("escape-analysis"))
  {
    do_function_pointer_removal();
    do_partial_inlining();
    do_remove_returns();
    parameter_assignments(symbol_table, goto_functions);

    namespacet ns(symbol_table);

    // recalculate numbers, etc.
    goto_functions.update();

    status() << "Escape Analysis" << eom;
    escape_analysist escape_analysis;
    escape_analysis(goto_functions, ns);
    escape_analysis.instrument(goto_functions, ns);

    // inline added functions, they are often small
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    // recalculate numbers, etc.
    goto_functions.update();
  }
    
  // now do full inlining, if requested
  if(cmdline.isset("inline"))
  {
    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(
      symbol_table, goto_functions, cmdline.isset("pointer-check"));

    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
    {
      do_remove_returns();
      thread_exit_instrumentation(goto_functions);
      mutex_init_instrumentation(symbol_table, goto_functions);
    }

    status() << "Performing full inlining" << eom;
    goto_inline(goto_functions, ns, ui_message_handler);
  }

  if(cmdline.isset("constant-propagator"))
  {
    do_function_pointer_removal();

    namespacet ns(symbol_table);

    status() << "Propagating Constants" << eom;

    constant_propagator_ait constant_propagator_ai(goto_functions, ns);
    
    remove_skip(goto_functions);
  }

  // add generic checks, if needed
  goto_check(ns, options, goto_functions);
  
  // check for uninitalized local varibles
  if(cmdline.isset("uninitialized-check"))
  {
    status() << "Adding checks for uninitialized local variables" << eom;
    add_uninitialized_locals_assertions(symbol_table, goto_functions);
  }
  
  // check for maximum call stack size
  if(cmdline.isset("stack-depth"))
  {
    status() << "Adding check for maximum call stack size" << eom;
    stack_depth(symbol_table, goto_functions,
        unsafe_string2unsigned(cmdline.get_value("stack-depth")));
  }

  // ignore default/user-specified initialization of variables with static
  // lifetime
  if(cmdline.isset("nondet-static"))
  {
    status() << "Adding nondeterministic initialization of static/global variables" << eom;
    nondet_static(ns, goto_functions);
  }

  if(cmdline.isset("string-abstraction"))
  {
    status() << "String Abstraction" << eom;
    string_abstraction(symbol_table,
      get_message_handler(), goto_functions);
  }
  
  // some analyses require function pointer removal and partial inlining

  if(cmdline.isset("remove-pointers") ||
     cmdline.isset("race-check") ||
     cmdline.isset("mm") ||
     cmdline.isset("isr") ||
     cmdline.isset("concurrency"))
  {
    if(!cmdline.isset("inline"))
    {
      status() << "Function Pointer Removal" << eom;
      remove_function_pointers(symbol_table, goto_functions, cmdline.isset("pointer-check"));

      // do partial inlining
      status() << "Partial Inlining" << eom;
      goto_partial_inline(goto_functions, ns, ui_message_handler);
    }
    
    status() << "Pointer Analysis" << eom;
    value_set_analysist value_set_analysis;
    value_set_analysis(goto_functions, ns);

    if(cmdline.isset("remove-pointers"))
    {
      // removing pointers
      status() << "Removing Pointers" << eom;
      remove_pointers(
        goto_functions, symbol_table, value_set_analysis);
    }

    if(cmdline.isset("race-check"))
    {
      status() << "Adding Race Checks" << eom;
      race_check(
        value_set_analysis,
        symbol_table,
        goto_functions);
    }

    if(cmdline.isset("mm"))
    {
      // TODO: move to wmm/weak_mem, and copy goto_functions AFTER some of the
      // modifications. Do the analysis on the copy, after remove_asm, and 
      // instrument the original (without remove_asm)
      remove_asm(symbol_table, goto_functions);
      goto_functions.update();

      std::string mm=cmdline.get_value("mm");
      memory_modelt model;

      // strategy of instrumentation
      instrumentation_strategyt inst_strategy;
      if(cmdline.isset("one-event-per-cycle"))
        inst_strategy=one_event_per_cycle;
      else if(cmdline.isset("minimum-interference"))
        inst_strategy=min_interference;
      else if(cmdline.isset("read-first"))
        inst_strategy=read_first;
      else if(cmdline.isset("write-first"))
        inst_strategy=write_first;
      else if(cmdline.isset("my-events"))
        inst_strategy=my_events;
      else
        /* default: instruments all unsafe pairs */
        inst_strategy=all;
      
      const unsigned unwind_loops = 
        ( cmdline.isset("unwind")?unsafe_string2unsigned(cmdline.get_value("unwind")):0 );
      const unsigned max_var =
        ( cmdline.isset("max-var")?unsafe_string2unsigned(cmdline.get_value("max-var")):0 );
      const unsigned max_po_trans =
        ( cmdline.isset("max-po-trans")?unsafe_string2unsigned(cmdline.get_value("max-po-trans")):0 );

      if(mm=="tso")
      {
        status() << "Adding weak memory (TSO) Instrumentation" << eom;
        model=TSO;
      }
      else if(mm=="pso")
      {
        status() << "Adding weak memory (PSO) Instrumentation" << eom;
        model=PSO;
      }
      else if(mm=="rmo")
      {
        status() << "Adding weak memory (RMO) Instrumentation" << eom;
        model=RMO;
      }
      else if(mm=="power")
      {
        status() << "Adding weak memory (Power) Instrumentation" << eom;
        model=Power;
      }
      else
      {
        error() << "Unknown weak memory model `" << mm << "'" << eom;
        model=Unknown;
      }

      loop_strategyt loops=arrays_only;

      if(cmdline.isset("force-loop-duplication"))
        loops=all_loops;
      if(cmdline.isset("no-loop-duplication"))
        loops=no_loop;

      if(model!=Unknown)
        weak_memory(
          model,
          value_set_analysis,
          symbol_table,
          goto_functions,
          cmdline.isset("scc"),
          inst_strategy,
          unwind_loops,
          !cmdline.isset("cfg-kill"),
          cmdline.isset("no-dependencies"),
          loops,
          max_var,
          max_po_trans,
          !cmdline.isset("no-po-rendering"),
          cmdline.isset("render-cluster-file"),
          cmdline.isset("render-cluster-function"),
          cmdline.isset("cav11"),
          cmdline.isset("hide-internals"),
          get_message_handler(),
          cmdline.isset("ignore-arrays"));
    }

    // Interrupt handler
    if(cmdline.isset("isr"))
    {
      status() << "Instrumenting interrupt handler" << eom;
      interrupt(
        value_set_analysis,
        symbol_table,
        goto_functions,
        cmdline.get_value("isr"));
    }

    // Memory-mapped I/O
    if(cmdline.isset("mmio"))
    {
      status() << "Instrumenting memory-mapped I/O" << eom;
      mmio(
        value_set_analysis,
        symbol_table,
        goto_functions);
    }

    if(cmdline.isset("concurrency"))
    {
      status() << "Sequentializing concurrency" << eom;
      concurrency(
        value_set_analysis,
        symbol_table,
        goto_functions);
    }
  }  

  if(cmdline.isset("interval-analysis"))
  {
    status() << "Interval analysis" << eom;
    interval_analysis(ns, goto_functions);
  }

  if(cmdline.isset("havoc-loops"))
  {
    status() << "Havocing loops" << eom;
    havoc_loops(goto_functions);
  }

  if(cmdline.isset("k-induction"))
  {
    bool base_case=cmdline.isset("base-case");
    bool step_case=cmdline.isset("step-case");

    if(step_case && base_case)
      throw "please specify only one of --step-case and --base-case";
    else if(!step_case && !base_case)
      throw "please specify one of --step-case and --base-case";

    unsigned k=unsafe_string2unsigned(cmdline.get_value("k-induction"));
    
    if(k==0)
      throw "please give k>=1";

    status() << "Instrumenting k-induction for k=" << k << ", "
             << (base_case?"base case":"step case") << eom;
    
    k_induction(goto_functions, base_case, step_case, k);
  }

  if(cmdline.isset("function-enter"))
  {
    status() << "Function enter instrumentation" << eom;
    function_enter(
      symbol_table,
      goto_functions,
      cmdline.get_value("function-enter"));
  }

  if(cmdline.isset("function-exit"))
  {
    status() << "Function exit instrumentation" << eom;
    function_exit(
      symbol_table,
      goto_functions,
      cmdline.get_value("function-exit"));
  }

  if(cmdline.isset("branch"))
  {
    status() << "Branch instrumentation" << eom;
    branch(
      symbol_table,
      goto_functions,
      cmdline.get_value("branch"));
  }

  // add failed symbols
  add_failed_symbols(symbol_table);
  
  // recalculate numbers, etc.
  goto_functions.update();

  // add loop ids
  goto_functions.compute_loop_numbers();
  
  // nondet volatile?
  if(cmdline.isset("nondet-volatile"))
  {
    status() << "Making volatile variables non-deterministic" << eom;
    nondet_volatile(symbol_table, goto_functions);
  }

  // reachability slice?
  if(cmdline.isset("reachability-slice"))
  {
    status() << "Performing a reachability slice" << eom;
    reachability_slicer(goto_functions);
  }

  // full slice?
  if(cmdline.isset("full-slice"))
  {
    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(
      symbol_table, goto_functions, cmdline.isset("pointer-check"));

    status() << "Performing a full slice" << eom;
    full_slicer(goto_functions, ns);
  }
  
  // label the assertions
  label_properties(goto_functions);

  // recalculate numbers, etc.
  goto_functions.update();
}

/*******************************************************************\

Function: goto_instrument_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void goto_instrument_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *     Goto-Instrument " CBMC_VERSION " - Copyright (C) 2008-2013       * *\n"
    "* *                    Daniel Kroening                      * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-instrument [-?] [-h] [--help]  show help\n"
    " goto-instrument in out              perform instrumentation\n"
    "\n"
    "Main options:\n"
    " --document-properties-html   generate HTML property documentation\n"
    " --document-properties-latex  generate Latex property documentation\n"
    " --dump-c                     generate C source\n"
    " --dump-cpp                   generate C++ source\n"
    " --dot                        generate CFG graph in DOT format\n"
    " --interpreter                do concrete execution\n"
    " --count-eloc                 count effective lines of code\n"
    "\n"
    "Diagnosis:\n"
    " --show-loops                 show the loops in the program\n"
    " --show-properties            show the properties\n"
    " --show-symbol-table          show symbol table\n"
    " --list-symbols               list symbols with type information\n"
    " --show-goto-functions        show goto program\n"
    " --list-undefined-functions   list functions without body\n"
    " --show-struct-alignment      show struct members that might be concurrently accessed\n"
    " --show-natural-loops         show natural loop heads\n"
    " --show-value-sets            show results of pointer analysis (full output with xml-ui)\n"
    " --show-sharing               show results of sharing analysis (full output with xml-ui)\n"
    " --show-lock-sets             show results of lock-set analysis (full output with xml-ui)\n"
    " --show-deadlocks             show results of deadlock analysis (full output with xml-ui)\n"
    "\n"
    "Safety checks:\n"
    " --no-assertions              ignore user assertions\n"
    " --bounds-check               add array bounds checks\n"
    " --div-by-zero-check          add division by zero checks\n"
    " --pointer-check              add pointer checks\n"
    " --memory-leak-check          add memory leak checks\n"
    " --signed-overflow-check      add arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    add arithmetic over- and underflow checks\n"
    " --undefined-shift-check      add range checks for shift distances\n"
    " --nan-check                  add floating-point NaN checks\n"
    " --uninitialized-check        add checks for uninitialized locals (experimental)\n"
    " --error-label label          check that label is unreachable\n"
    " --stack-depth n              add check that call stack size of non-inlined functions never exceeds n\n"
    " --race-check                 add floating-point data race checks\n"
    "\n"
    "Semantic transformations:\n"
    " --nondet-volatile            makes reads from volatile variables non-deterministic\n"
    " --unwind <n>                 unwinds the loops <n> times\n"
    " --isr <function>             instruments an interrupt service routine\n"
    " --mmio                       instruments memory-mapped I/O\n"
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    " --check-invariant function   instruments invariant checking function\n"
    " --remove-pointers            converts pointer arithmetic to base+offset expressions\n"
    "\n"
    "Loop transformations:\n"
    " --k-induction <k>            check loops with k-induction\n"
    " --step-case                  k-induction: do step-case\n"
    " --base-case                  k-induction: do base-case\n"
    " --havoc-loops                over-approximate all loops\n"
    " --accelerate                 add loop accelerators\n"
    " --skip-loops <loop-ids>      add gotos to skip selected loops during execution\n"
    "\n"
    "Memory model instrumentations:\n"
    " --mm <tso,pso,rmo,power>     instruments a weak memory model\n"
    " --scc                        detects critical cycles per SCC (one thread per SCC)\n"
    " --one-event-per-cycle        only instruments one event per cycle\n"
    " --minimum-interference       instruments an optimal number of events\n"
    " --my-events                  only instruments events whose ids appear in inst.evt\n"
    " --cfg-kill                   enables symbolic execution used to reduce spurious cycles\n"
    " --no-dependencies            no dependency analysis\n"
    " --no-po-rendering            no representation of the threads in the dot\n"
    " --render-cluster-file        clusterises the dot by files\n"
    " --render-cluster-function    clusterises the dot by functions\n"
    "\n"
    "Slicing:\n"
    " --reachability-slice         slice away instructions that can't reach assertions\n"
    " --full-slice                 slice away instructions that don't affect assertions\n"
    "\n"
    "Further transformations:\n"
    " --constant-propagator        propagate constants and simplify expressions\n"
    " --inline                     perform full inlining\n"
    " --add-library                add models of C library functions\n"
    "\n"
    "Other options:\n"
    " --use-system-headers         with --dump-c/--dump-cpp: generate C source with includes\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
