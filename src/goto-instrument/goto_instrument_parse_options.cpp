/*******************************************************************\

Module: Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Main Module

#include "goto_instrument_parse_options.h"

#include <fstream>
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/json.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_exceptions.h>
#include <goto-programs/remove_instanceof.h>
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
#include <goto-programs/slice_global_inits.h>

#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/show_value_sets.h>

#include <analyses/natural_loops.h>
#include <analyses/global_may_alias.h>
#include <analyses/local_bitvector_analysis.h>
#include <analyses/custom_bitvector_analysis.h>
#include <analyses/escape_analysis.h>
#include <analyses/call_graph.h>
#include <analyses/interval_analysis.h>
#include <analyses/interval_domain.h>
#include <analyses/reaching_definitions.h>
#include <analyses/dependence_graph.h>
#include <analyses/constant_propagator.h>
#include <analyses/is_threaded.h>

#include <cbmc/version.h>

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
#include "code_contracts.h"
#include "unwind.h"
#include "model_argc_argv.h"
#include "undefined_functions.h"
#include "remove_function.h"

void goto_instrument_parse_optionst::eval_verbosity()
{
  unsigned int v=8;

  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10)
      v=10;
  }

  ui_message_handler.set_verbosity(v);
}

/// invoke main modules
int goto_instrument_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
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

    {
      bool unwind=cmdline.isset("unwind");
      bool unwindset=cmdline.isset("unwindset");
      bool unwindset_file=cmdline.isset("unwindset-file");

      if(unwindset && unwindset_file)
        throw "only one of --unwindset and --unwindset-file supported at a "
              "time";

      if(unwind || unwindset || unwindset_file)
      {
        int k=-1;

        if(unwind)
          k=std::stoi(cmdline.get_value("unwind"));

        unwind_sett unwind_set;

        if(unwindset_file)
        {
          std::string us;
          std::string fn=cmdline.get_value("unwindset-file");

#ifdef _MSC_VER
          std::ifstream file(widen(fn));
#else
          std::ifstream file(fn);
#endif
          if(!file)
            throw "cannot open file "+fn;

          std::stringstream buffer;
          buffer << file.rdbuf();
          us=buffer.str();
          parse_unwindset(us, unwind_set);
        }
        else if(unwindset)
          parse_unwindset(cmdline.get_value("unwindset"), unwind_set);

        bool unwinding_assertions=cmdline.isset("unwinding-assertions");
        bool partial_loops=cmdline.isset("partial-loops");
        bool continue_as_loops=cmdline.isset("continue-as-loops");

        if(unwinding_assertions+partial_loops+continue_as_loops>1)
          throw "more than one of --unwinding-assertions,--partial-loops,"
                "--continue-as-loops selected";

        goto_unwindt::unwind_strategyt unwind_strategy=
          goto_unwindt::unwind_strategyt::ASSUME;

        if(unwinding_assertions)
        {
          unwind_strategy=goto_unwindt::unwind_strategyt::ASSERT;
        }
        else if(partial_loops)
        {
          unwind_strategy=goto_unwindt::unwind_strategyt::PARTIAL;
        }
        else if(continue_as_loops)
        {
          unwind_strategy=goto_unwindt::unwind_strategyt::CONTINUE;
        }

        goto_unwindt goto_unwind;
        goto_unwind(goto_functions, unwind_set, k, unwind_strategy);

        goto_functions.update();
        goto_functions.compute_loop_numbers();

        if(cmdline.isset("log"))
        {
          std::string filename=cmdline.get_value("log");
          bool have_file=!filename.empty() && filename!="-";

          jsont result=goto_unwind.output_log_json();

          if(have_file)
          {
#ifdef _MSC_VER
            std::ofstream of(widen(filename));
#else
            std::ofstream of(filename);
#endif
            if(!of)
              throw "failed to open file "+filename;

            of << result;
            of.close();
          }
          else
          {
            std::cout << result << '\n';
          }
        }
      }
    }

    if(cmdline.isset("show-threaded"))
    {
      namespacet ns(symbol_table);

      is_threadedt is_threaded(goto_functions);

      forall_goto_functions(f_it, goto_functions)
      {
        std::cout << "////\n";
        std::cout << "//// Function: " << f_it->first << '\n';
        std::cout << "////\n\n";

        const goto_programt &goto_program=f_it->second.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          goto_program.output_instruction(ns, "", std::cout, i_it);
          std::cout << "Is threaded: " << (is_threaded(i_it)?"True":"False")
                    << "\n\n";
        }
      }
    }

    if(cmdline.isset("show-value-sets"))
    {
      do_indirect_call_and_rtti_removal();
      do_partial_inlining();

      // recalculate numbers, etc.
      goto_functions.update();

      status() << "Pointer Analysis" << eom;
      namespacet ns(symbol_table);
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_functions);

      show_value_sets(get_ui(), goto_functions, value_set_analysis);
      return 0;
    }

    if(cmdline.isset("show-global-may-alias"))
    {
      do_indirect_call_and_rtti_removal();
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
      do_indirect_call_and_rtti_removal();
      do_partial_inlining();
      parameter_assignments(symbol_table, goto_functions);

      // recalculate numbers, etc.
      goto_functions.update();

      namespacet ns(symbol_table);

      forall_goto_functions(it, goto_functions)
      {
        local_bitvector_analysist local_bitvector_analysis(it->second);
        std::cout << ">>>>\n";
        std::cout << ">>>> " << it->first << '\n';
        std::cout << ">>>>\n";
        local_bitvector_analysis.output(std::cout, it->second, ns);
        std::cout << '\n';
      }

      return 0;
    }

    if(cmdline.isset("show-custom-bitvector-analysis"))
    {
      do_indirect_call_and_rtti_removal();
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
      do_indirect_call_and_rtti_removal();
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
      do_indirect_call_and_rtti_removal();
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
      custom_bitvector_analysis.check(
        ns,
        goto_functions,
        cmdline.isset("xml-ui"),
        std::cout);

      return 0;
    }

    if(cmdline.isset("show-points-to"))
    {
      do_indirect_call_and_rtti_removal();
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
      do_indirect_call_and_rtti_removal();
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

    if(cmdline.isset("list-calls-args"))
    {
      do_indirect_call_and_rtti_removal();
      do_partial_inlining();

      namespacet ns(symbol_table);
      list_calls_and_arguments(ns, goto_functions);

      return 0;
    }

    if(cmdline.isset("show-rw-set"))
    {
      namespacet ns(symbol_table);

      if(!cmdline.isset("inline"))
      {
        do_indirect_call_and_rtti_removal();
        do_partial_inlining();

        // recalculate numbers, etc.
        goto_functions.update();
      }

      status() << "Pointer Analysis" << eom;
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_functions);

      const symbolt &symbol=ns.lookup(ID_main);
      symbol_exprt main(symbol.name, symbol.type);

      std::cout <<
        rw_set_functiont(value_set_analysis, ns, goto_functions, main);
      return 0;
    }

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table();
      return 0;
    }

    if(cmdline.isset("show-reaching-definitions"))
    {
      do_indirect_call_and_rtti_removal();

      const namespacet ns(symbol_table);
      reaching_definitions_analysist rd_analysis(ns);
      rd_analysis(goto_functions, ns);

      rd_analysis.output(ns, goto_functions, std::cout);

      return 0;
    }

    if(cmdline.isset("show-dependence-graph"))
    {
      do_indirect_call_and_rtti_removal();

      const namespacet ns(symbol_table);
      dependence_grapht dependence_graph(ns);
      dependence_graph(goto_functions, ns);

      dependence_graph.output(ns, goto_functions, std::cout);
      dependence_graph.output_dot(std::cout);

      return 0;
    }

    if(cmdline.isset("count-eloc"))
    {
      count_eloc(goto_functions);
      return 0;
    }

    if(cmdline.isset("list-eloc"))
    {
      list_eloc(goto_functions);
      return 0;
    }

    if(cmdline.isset("print-path-lengths"))
    {
      print_path_lengths(goto_functions);
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
      interpreter(symbol_table, goto_functions, get_message_handler());
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

    if(cmdline.isset("print-internal-representation"))
    {
      for(auto const &pair : goto_functions.function_map)
        for(auto const &ins : pair.second.body.instructions)
        {
          if(ins.code.is_not_nil())
            status() << ins.code.pretty() << eom;
          if(ins.guard.is_not_nil())
            status() << "[guard] " << ins.guard.pretty() << eom;
        }
      return 0;
    }

    if(cmdline.isset("show-goto-functions"))
    {
      namespacet ns(symbol_table);
      show_goto_functions(ns, get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("list-undefined-functions"))
    {
      const namespacet ns(symbol_table);
      list_undefined_functions(goto_functions, ns, std::cout);
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
      const bool h_libc=!cmdline.isset("no-system-headers");
      const bool h_all=cmdline.isset("use-all-headers");
      namespacet ns(symbol_table);

      // restore RETURN instructions in case remove_returns had been
      // applied
      restore_returns(symbol_table, goto_functions);

      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]));
        #else
        std::ofstream out(cmdline.args[1]);
        #endif
        if(!out)
        {
          error() << "failed to write to `" << cmdline.args[1] << "'";
          return 10;
        }
        (is_cpp ? dump_cpp : dump_c)(goto_functions, h_libc, h_all, ns, out);
      }
      else
        (is_cpp ? dump_cpp : dump_c)(
          goto_functions, h_libc, h_all, ns, std::cout);

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
        std::ofstream out(widen(cmdline.args[1]));
        #else
        std::ofstream out(cmdline.args[1]);
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
      do_indirect_call_and_rtti_removal();

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
        std::ofstream out(widen(cmdline.args[1]));
        #else
        std::ofstream out(cmdline.args[1]);
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

    if(cmdline.isset("drop-unused-functions"))
    {
      do_indirect_call_and_rtti_removal();

      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_functions, get_message_handler());
    }

    if(cmdline.isset("undefined-function-is-assume-false"))
    {
      do_indirect_call_and_rtti_removal();

      undefined_function_abort_path(goto_functions);
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
// NOLINTNEXTLINE(readability/fn_size)
}

void goto_instrument_parse_optionst::do_indirect_call_and_rtti_removal(
  bool force)
{
  if(function_pointer_removal_done && !force)
    return;

  function_pointer_removal_done=true;

  status() << "Function Pointer Removal" << eom;
  remove_function_pointers(
    get_message_handler(),
    symbol_table,
    goto_functions,
    cmdline.isset("pointer-check"));
  status() << "Virtual function removal" << eom;
  remove_virtual_functions(symbol_table, goto_functions);
  status() << "Catch and throw removal" << eom;
  remove_exceptions(symbol_table, goto_functions);
  status() << "Java instanceof removal" << eom;
  remove_instanceof(symbol_table, goto_functions);
}

/// Remove function pointers that can be resolved by analysing const variables
/// (i.e. can be resolved using remove_const_function_pointers). Function
/// pointers that cannot be resolved will be left as function pointers.
void goto_instrument_parse_optionst::do_remove_const_function_pointers_only()
{
  // Don't bother if we've already done a full function pointer
  // removal.
  if(function_pointer_removal_done)
  {
    return;
  }

  status() << "Removing const function pointers only" << eom;
  remove_function_pointers(
    get_message_handler(),
    symbol_table,
    goto_functions,
    cmdline.isset("pointer-check"),
    true); // abort if we can't resolve via const pointers
}

void goto_instrument_parse_optionst::do_partial_inlining()
{
  if(partial_inlining_done)
    return;

  partial_inlining_done=true;

  if(!cmdline.isset("inline"))
  {
    status() << "Partial Inlining" << eom;
    const namespacet ns(symbol_table);
    goto_partial_inline(goto_functions, ns, ui_message_handler);
  }
}

void goto_instrument_parse_optionst::do_remove_returns()
{
  if(remove_returns_done)
    return;

  remove_returns_done=true;

  status() << "Removing returns" << eom;
  remove_returns(symbol_table, goto_functions);
}

void goto_instrument_parse_optionst::get_goto_program()
{
  status() << "Reading GOTO program from `" << cmdline.args[0] << "'" << eom;

  if(read_goto_binary(cmdline.args[0],
    symbol_table, goto_functions, get_message_handler()))
    throw 0;

  config.set(cmdline);
}

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

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

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

  namespacet ns(symbol_table);

  // initialize argv with valid pointers
  if(cmdline.isset("model-argc-argv"))
  {
    unsigned max_argc=
      safe_string2unsigned(cmdline.get_value("model-argc-argv"));

    status() << "Adding up to " << max_argc
             << " command line arguments" << eom;
    if(model_argc_argv(
        symbol_table,
        goto_functions,
        max_argc,
        get_message_handler()))
      throw 0;
  }

  if(cmdline.isset("remove-function-body"))
  {
    remove_functions(
      symbol_table,
      goto_functions,
      cmdline.get_values("remove-function-body"),
      get_message_handler());
  }

  // we add the library in some cases, as some analyses benefit

  if(cmdline.isset("add-library") ||
     cmdline.isset("mm"))
  {
    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
      config.ansi_c.defines.push_back("__CPROVER_CUSTOM_BITVECTOR_ANALYSIS");

    // add the library
    link_to_library(symbol_table, goto_functions, ui_message_handler);
  }

  // now do full inlining, if requested
  if(cmdline.isset("inline"))
  {
    do_indirect_call_and_rtti_removal();

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

  if(cmdline.isset("show-custom-bitvector-analysis") ||
     cmdline.isset("custom-bitvector-analysis"))
  {
    do_partial_inlining();

    status() << "Propagating Constants" << eom;
    constant_propagator_ait constant_propagator_ai(goto_functions, ns);
    remove_skip(goto_functions);
  }

  if(cmdline.isset("escape-analysis"))
  {
    do_indirect_call_and_rtti_removal();
    do_partial_inlining();
    do_remove_returns();
    parameter_assignments(symbol_table, goto_functions);

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

  // verify and set invariants and pre/post-condition pairs
  if(cmdline.isset("apply-code-contracts"))
  {
    status() << "Applying Code Contracts" << eom;
    code_contracts(symbol_table, goto_functions);
  }

  // replace function pointers, if explicitly requested
  if(cmdline.isset("remove-function-pointers"))
  {
    do_indirect_call_and_rtti_removal();
  }
  else if(cmdline.isset("remove-const-function-pointers"))
  {
    do_remove_const_function_pointers_only();
  }

  if(cmdline.isset("function-inline"))
  {
    std::string function=cmdline.get_value("function-inline");
    assert(!function.empty());

    bool caching=!cmdline.isset("no-caching");

    do_indirect_call_and_rtti_removal();

    status() << "Inlining calls of function `" << function << "'" << eom;

    if(!cmdline.isset("log"))
    {
      goto_function_inline(
        goto_functions,
        function,
        ns,
        ui_message_handler,
        true,
        caching);
    }
    else
    {
      std::string filename=cmdline.get_value("log");
      bool have_file=!filename.empty() && filename!="-";

      jsont result=
        goto_function_inline_and_log(
          goto_functions,
          function,
          ns,
          ui_message_handler,
          true,
          caching);

      if(have_file)
      {
#ifdef _MSC_VER
        std::ofstream of(widen(filename));
#else
        std::ofstream of(filename);
#endif
        if(!of)
          throw "failed to open file "+filename;

        of << result;
        of.close();
      }
      else
      {
        std::cout << result << '\n';
      }
    }

    goto_functions.update();
    goto_functions.compute_loop_numbers();
  }

  if(cmdline.isset("partial-inline"))
  {
    do_indirect_call_and_rtti_removal();

    status() << "Partial inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler, true);

    goto_functions.update();
    goto_functions.compute_loop_numbers();
  }

  // now do full inlining, if requested
  if(cmdline.isset("inline"))
  {
    do_indirect_call_and_rtti_removal(/*force=*/true);

    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
    {
      do_remove_returns();
      thread_exit_instrumentation(goto_functions);
      mutex_init_instrumentation(symbol_table, goto_functions);
    }

    status() << "Performing full inlining" << eom;
    goto_inline(goto_functions, ns, ui_message_handler, true);
  }

  if(cmdline.isset("constant-propagator"))
  {
    do_indirect_call_and_rtti_removal();

    status() << "Propagating Constants" << eom;

    constant_propagator_ait constant_propagator_ai(goto_functions, ns);

    remove_skip(goto_functions);
  }

  // add generic checks, if needed
  goto_check(ns, options, goto_functions);

  // check for uninitalized local variables
  if(cmdline.isset("uninitialized-check"))
  {
    status() << "Adding checks for uninitialized local variables" << eom;
    add_uninitialized_locals_assertions(symbol_table, goto_functions);
  }

  // check for maximum call stack size
  if(cmdline.isset("stack-depth"))
  {
    status() << "Adding check for maximum call stack size" << eom;
    stack_depth(
      symbol_table,
      goto_functions,
      unsafe_string2unsigned(cmdline.get_value("stack-depth")));
  }

  // ignore default/user-specified initialization of variables with static
  // lifetime
  if(cmdline.isset("nondet-static"))
  {
    status() << "Adding nondeterministic initialization of static/global "
                "variables" << eom;
    nondet_static(ns, goto_functions);
  }

  if(cmdline.isset("slice-global-inits"))
  {
    status() << "Slicing away initializations of unused global variables"
             << eom;
    slice_global_inits(ns, goto_functions);
  }

  if(cmdline.isset("string-abstraction"))
  {
    do_indirect_call_and_rtti_removal();
    do_remove_returns();

    status() << "String Abstraction" << eom;
    string_abstraction(
      symbol_table,
      get_message_handler(),
      goto_functions);
  }

  // some analyses require function pointer removal and partial inlining

  if(cmdline.isset("remove-pointers") ||
     cmdline.isset("race-check") ||
     cmdline.isset("mm") ||
     cmdline.isset("isr") ||
     cmdline.isset("concurrency"))
  {
    do_indirect_call_and_rtti_removal();
    do_partial_inlining();

    status() << "Pointer Analysis" << eom;
    value_set_analysist value_set_analysis(ns);
    value_set_analysis(goto_functions);

    if(cmdline.isset("remove-pointers"))
    {
      // removing pointers
      status() << "Removing Pointers" << eom;
      remove_pointers(
        goto_functions,
        symbol_table,
        value_set_analysis);
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

      const unsigned unwind_loops=
        cmdline.isset("unwind")?
        unsafe_string2unsigned(cmdline.get_value("unwind")):0;
      const unsigned max_var=
        cmdline.isset("max-var")?
        unsafe_string2unsigned(cmdline.get_value("max-var")):0;
      const unsigned max_po_trans=
        cmdline.isset("max-po-trans")?
        unsafe_string2unsigned(cmdline.get_value("max-po-trans")):0;

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
    status() << "Havocking loops" << eom;
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

  // label the assertions
  label_properties(goto_functions);

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
    if(cmdline.isset("property"))
      reachability_slicer(goto_functions, cmdline.get_values("property"));
    else
      reachability_slicer(goto_functions);
  }

  // full slice?
  if(cmdline.isset("full-slice"))
  {
    remove_returns(symbol_table, goto_functions);
    do_indirect_call_and_rtti_removal();

    status() << "Performing a full slice" << eom;
    if(cmdline.isset("property"))
      property_slicer(goto_functions, ns, cmdline.get_values("property"));
    else
      full_slicer(goto_functions, ns);
  }

  // recalculate numbers, etc.
  goto_functions.update();
}

/// display command line help
void goto_instrument_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *     Goto-Instrument " CBMC_VERSION " - Copyright (C) 2008-2013       * *\n" // NOLINT(*)
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
    " --list-eloc                  list full path names of lines containing code\n" // NOLINT(*)
    "\n"
    "Diagnosis:\n"
    " --show-loops                 show the loops in the program\n"
    " --show-properties            show the properties\n"
    " --show-symbol-table          show symbol table\n"
    " --list-symbols               list symbols with type information\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --print-internal-representation\n" // NOLINTNEXTLINE(*)
    "                              show verbose internal representation of the program\n"
    " --list-undefined-functions   list functions without body\n"
    " --show-struct-alignment      show struct members that might be concurrently accessed\n" // NOLINT(*)
    " --show-natural-loops         show natural loop heads\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --list-calls-args            list all function calls with their arguments\n"
    "\n"
    "Safety checks:\n"
    " --no-assertions              ignore user assertions\n"
    HELP_GOTO_CHECK
    " --uninitialized-check        add checks for uninitialized locals (experimental)\n" // NOLINT(*)
    " --error-label label          check that label is unreachable\n"
    " --stack-depth n              add check that call stack size of non-inlined functions never exceeds n\n" // NOLINT(*)
    " --race-check                 add floating-point data race checks\n"
    "\n"
    "Semantic transformations:\n"
    " --nondet-volatile            makes reads from volatile variables non-deterministic\n" // NOLINT(*)
    " --unwind <n>                 unwinds the loops <n> times\n"
    " --unwindset L:B,...          unwind loop L with a bound of B\n"
    " --unwindset-file <file>      read unwindset from file\n"
    " --partial-loops              permit paths with partial loops\n"
    " --unwinding-assertions       generate unwinding assertions\n"
    " --continue-as-loops          add loop for remaining iterations after unwound part\n" // NOLINT(*)
    " --isr <function>             instruments an interrupt service routine\n"
    " --mmio                       instruments memory-mapped I/O\n"
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n" // NOLINT(*)
    " --check-invariant function   instruments invariant checking function\n"
    " --remove-pointers            converts pointer arithmetic to base+offset expressions\n" // NOLINT(*)
    // NOLINTNEXTLINE(whitespace/line_length)
    " --undefined-function-is-assume-false\n" // NOLINTNEXTLINE(whitespace/line_length)
    "                              convert each call to an undefined function to assume(false)\n"
    "\n"
    "Loop transformations:\n"
    " --k-induction <k>            check loops with k-induction\n"
    " --step-case                  k-induction: do step-case\n"
    " --base-case                  k-induction: do base-case\n"
    " --havoc-loops                over-approximate all loops\n"
    " --accelerate                 add loop accelerators\n"
    " --skip-loops <loop-ids>      add gotos to skip selected loops during execution\n" // NOLINT(*)
    "\n"
    "Memory model instrumentations:\n"
    " --mm <tso,pso,rmo,power>     instruments a weak memory model\n"
    " --scc                        detects critical cycles per SCC (one thread per SCC)\n" // NOLINT(*)
    " --one-event-per-cycle        only instruments one event per cycle\n"
    " --minimum-interference       instruments an optimal number of events\n"
    " --my-events                  only instruments events whose ids appear in inst.evt\n" // NOLINT(*)
    " --cfg-kill                   enables symbolic execution used to reduce spurious cycles\n" // NOLINT(*)
    " --no-dependencies            no dependency analysis\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --no-po-rendering            no representation of the threads in the dot\n"
    " --render-cluster-file        clusterises the dot by files\n"
    " --render-cluster-function    clusterises the dot by functions\n"
    "\n"
    "Slicing:\n"
    " --reachability-slice         slice away instructions that can't reach assertions\n" // NOLINT(*)
    " --full-slice                 slice away instructions that don't affect assertions\n" // NOLINT(*)
    " --property id                slice with respect to specific property only\n" // NOLINT(*)
    " --slice-global-inits         slice away initializations of unused global variables\n" // NOLINT(*)
    "\n"
    "Further transformations:\n"
    " --constant-propagator        propagate constants and simplify expressions\n" // NOLINT(*)
    " --inline                     perform full inlining\n"
    " --partial-inline             perform partial inlining\n"
    " --function-inline <function> transitively inline all calls <function> makes\n" // NOLINT(*)
    " --no-caching                 disable caching of intermediate results during transitive function inlining\n" // NOLINT(*)
    " --log <file>                 log in json format which code segments were inlined, use with --function-inline\n" // NOLINT(*)
    " --remove-function-pointers   replace function pointers by case statement over function calls\n" // NOLINT(*)
    HELP_REMOVE_CONST_FUNCTION_POINTERS
    " --add-library                add models of C library functions\n"
    " --model-argc-argv <n>        model up to <n> command line arguments\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --remove-function-body <f>   remove the implementation of function <f> (may be repeated)\n"
    "\n"
    "Other options:\n"
    " --no-system-headers          with --dump-c/--dump-cpp: generate C source expanding libc includes\n" // NOLINT(*)
    " --use-all-headers            with --dump-c/--dump-cpp: generate C source with all includes\n" // NOLINT(*)
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    "\n";
}
