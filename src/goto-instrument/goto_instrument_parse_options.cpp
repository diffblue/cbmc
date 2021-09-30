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
#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/json.h>
#include <util/string2int.h>
#include <util/string_utils.h>
#include <util/version.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/ensure_one_backedge_per_target.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/interpreter.h>
#include <goto-programs/label_function_pointer_call_sites.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/parameter_assignments.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_calls_no_body.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/restrict_function_pointers.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/slice_global_inits.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/write_goto_binary.h>

#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/show_value_sets.h>
#include <pointer-analysis/value_set_analysis.h>

#include <analyses/call_graph.h>
#include <analyses/constant_propagator.h>
#include <analyses/custom_bitvector_analysis.h>
#include <analyses/dependence_graph.h>
#include <analyses/escape_analysis.h>
#include <analyses/global_may_alias.h>
#include <analyses/interval_analysis.h>
#include <analyses/interval_domain.h>
#include <analyses/is_threaded.h>
#include <analyses/lexical_loops.h>
#include <analyses/local_bitvector_analysis.h>
#include <analyses/local_safe_pointers.h>
#include <analyses/natural_loops.h>
#include <analyses/reaching_definitions.h>
#include <analyses/sese_regions.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/c_object_factory_parameters.h>
#include <ansi-c/cprover_library.h>

#include <assembler/remove_asm.h>

#include <cpp/cprover_library.h>

#include "accelerate/accelerate.h"
#include "alignment_checks.h"
#include "branch.h"
#include "call_sequences.h"
#include "concurrency.h"
#include "document_properties.h"
#include "dot.h"
#include "dump_c.h"
#include "full_slicer.h"
#include "function.h"
#include "havoc_loops.h"
#include "horn_encoding.h"
#include "insert_final_assert_false.h"
#include "interrupt.h"
#include "k_induction.h"
#include "mmio.h"
#include "model_argc_argv.h"
#include "nondet_static.h"
#include "nondet_volatile.h"
#include "points_to.h"
#include "race_check.h"
#include "reachability_slicer.h"
#include "remove_function.h"
#include "rw_set.h"
#include "show_locations.h"
#include "skip_loops.h"
#include "splice_call.h"
#include "stack_depth.h"
#include "thread_instrumentation.h"
#include "undefined_functions.h"
#include "uninitialized.h"
#include "unwind.h"
#include "unwindset.h"
#include "value_set_fi_fp_removal.h"
#include "wmm/weak_memory.h"

/// invoke main modules
int goto_instrument_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.args.size()!=1 && cmdline.args.size()!=2)
  {
    help();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  {
    register_languages();

    get_goto_program();

    {
      const bool validate_only = cmdline.isset("validate-goto-binary");

      if(validate_only || cmdline.isset("validate-goto-model"))
      {
        goto_model.validate(validation_modet::EXCEPTION);

        if(validate_only)
        {
          return CPROVER_EXIT_SUCCESS;
        }
      }
    }

    instrument_goto_program();

    if(cmdline.isset("validate-goto-model"))
    {
      goto_model.validate();
    }

    {
      bool unwind_given=cmdline.isset("unwind");
      bool unwindset_given=cmdline.isset("unwindset");
      bool unwindset_file_given=cmdline.isset("unwindset-file");

      if(unwindset_given && unwindset_file_given)
        throw "only one of --unwindset and --unwindset-file supported at a "
              "time";

      if(unwind_given || unwindset_given || unwindset_file_given)
      {
        unwindsett unwindset;

        if(unwind_given)
          unwindset.parse_unwind(cmdline.get_value("unwind"));

        if(unwindset_file_given)
          unwindset.parse_unwindset_file(cmdline.get_value("unwindset-file"));

        if(unwindset_given)
          unwindset.parse_unwindset(cmdline.get_values("unwindset"));

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
        goto_unwind(goto_model, unwindset, unwind_strategy);

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

        // goto_unwind holds references to instructions, only do remove_skip
        // after having generated the log above
        remove_skip(goto_model);
      }
    }

    if(cmdline.isset("show-threaded"))
    {
      namespacet ns(goto_model.symbol_table);

      is_threadedt is_threaded(goto_model);

      for(const auto &gf_entry : goto_model.goto_functions.function_map)
      {
        std::cout << "////\n";
        std::cout << "//// Function: " << gf_entry.first << '\n';
        std::cout << "////\n\n";

        const goto_programt &goto_program = gf_entry.second.body;

        forall_goto_program_instructions(i_it, goto_program)
        {
          goto_program.output_instruction(ns, gf_entry.first, std::cout, *i_it);
          std::cout << "Is threaded: " << (is_threaded(i_it)?"True":"False")
                    << "\n\n";
        }
      }

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("insert-final-assert-false"))
    {
      log.status() << "Inserting final assert false" << messaget::eom;
      bool fail = insert_final_assert_false(
        goto_model,
        cmdline.get_value("insert-final-assert-false"),
        ui_message_handler);
      if(fail)
      {
        return CPROVER_EXIT_INTERNAL_ERROR;
      }
      // otherwise, fall-through to write new binary
    }

    if(cmdline.isset("show-value-sets"))
    {
      do_indirect_call_and_rtti_removal();

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      log.status() << "Pointer Analysis" << messaget::eom;
      namespacet ns(goto_model.symbol_table);
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_model.goto_functions);
      show_value_sets(
        ui_message_handler.get_ui(), goto_model, value_set_analysis);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-global-may-alias"))
    {
      do_indirect_call_and_rtti_removal();
      do_remove_returns();
      parameter_assignments(goto_model);

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      global_may_alias_analysist global_may_alias_analysis;
      global_may_alias_analysis(goto_model);
      global_may_alias_analysis.output(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-local-bitvector-analysis"))
    {
      do_indirect_call_and_rtti_removal();
      parameter_assignments(goto_model);

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      namespacet ns(goto_model.symbol_table);

      for(const auto &gf_entry : goto_model.goto_functions.function_map)
      {
        local_bitvector_analysist local_bitvector_analysis(gf_entry.second, ns);
        std::cout << ">>>>\n";
        std::cout << ">>>> " << gf_entry.first << '\n';
        std::cout << ">>>>\n";
        local_bitvector_analysis.output(std::cout, gf_entry.second, ns);
        std::cout << '\n';
      }

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-local-safe-pointers") ||
       cmdline.isset("show-safe-dereferences"))
    {
      // Ensure location numbering is unique:
      goto_model.goto_functions.update();

      namespacet ns(goto_model.symbol_table);

      for(const auto &gf_entry : goto_model.goto_functions.function_map)
      {
        local_safe_pointerst local_safe_pointers;
        local_safe_pointers(gf_entry.second.body);
        std::cout << ">>>>\n";
        std::cout << ">>>> " << gf_entry.first << '\n';
        std::cout << ">>>>\n";
        if(cmdline.isset("show-local-safe-pointers"))
          local_safe_pointers.output(std::cout, gf_entry.second.body, ns);
        else
        {
          local_safe_pointers.output_safe_dereferences(
            std::cout, gf_entry.second.body, ns);
        }
        std::cout << '\n';
      }

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-sese-regions"))
    {
      // Ensure location numbering is unique:
      goto_model.goto_functions.update();

      namespacet ns(goto_model.symbol_table);

      for(const auto &gf_entry : goto_model.goto_functions.function_map)
      {
        sese_region_analysist sese_region_analysis;
        sese_region_analysis(gf_entry.second.body);
        std::cout << ">>>>\n";
        std::cout << ">>>> " << gf_entry.first << '\n';
        std::cout << ">>>>\n";
        sese_region_analysis.output(std::cout, gf_entry.second.body, ns);
        std::cout << '\n';
      }

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-custom-bitvector-analysis"))
    {
      do_indirect_call_and_rtti_removal();
      do_remove_returns();
      parameter_assignments(goto_model);

      remove_unused_functions(goto_model, ui_message_handler);

      if(!cmdline.isset("inline"))
      {
        thread_exit_instrumentation(goto_model);
        mutex_init_instrumentation(goto_model);
      }

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      custom_bitvector_analysist custom_bitvector_analysis;
      custom_bitvector_analysis(goto_model);
      custom_bitvector_analysis.output(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-escape-analysis"))
    {
      do_indirect_call_and_rtti_removal();
      do_remove_returns();
      parameter_assignments(goto_model);

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      escape_analysist escape_analysis;
      escape_analysis(goto_model);
      escape_analysis.output(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("custom-bitvector-analysis"))
    {
      do_indirect_call_and_rtti_removal();
      do_remove_returns();
      parameter_assignments(goto_model);

      remove_unused_functions(goto_model, ui_message_handler);

      if(!cmdline.isset("inline"))
      {
        thread_exit_instrumentation(goto_model);
        mutex_init_instrumentation(goto_model);
      }

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      namespacet ns(goto_model.symbol_table);

      custom_bitvector_analysist custom_bitvector_analysis;
      custom_bitvector_analysis(goto_model);
      custom_bitvector_analysis.check(
        goto_model,
        cmdline.isset("xml-ui"),
        std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-points-to"))
    {
      do_indirect_call_and_rtti_removal();

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      namespacet ns(goto_model.symbol_table);

      log.status() << "Pointer Analysis" << messaget::eom;
      points_tot points_to;
      points_to(goto_model);
      points_to.output(std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-intervals"))
    {
      do_indirect_call_and_rtti_removal();

      // recalculate numbers, etc.
      goto_model.goto_functions.update();

      log.status() << "Interval Analysis" << messaget::eom;
      namespacet ns(goto_model.symbol_table);
      ait<interval_domaint> interval_analysis;
      interval_analysis(goto_model);
      interval_analysis.output(goto_model, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-call-sequences"))
    {
      do_indirect_call_and_rtti_removal();
      show_call_sequences(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("check-call-sequence"))
    {
      do_remove_returns();
      check_call_sequence(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("list-calls-args"))
    {
      do_indirect_call_and_rtti_removal();

      list_calls_and_arguments(goto_model);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-rw-set"))
    {
      namespacet ns(goto_model.symbol_table);

      if(!cmdline.isset("inline"))
      {
        do_indirect_call_and_rtti_removal();

        // recalculate numbers, etc.
        goto_model.goto_functions.update();
      }

      log.status() << "Pointer Analysis" << messaget::eom;
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_model.goto_functions);

      const symbolt &symbol=ns.lookup(ID_main);
      symbol_exprt main(symbol.name, symbol.type);

      std::cout <<
        rw_set_functiont(value_set_analysis, goto_model, main);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-symbol-table"))
    {
      ::show_symbol_table(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-reaching-definitions"))
    {
      do_indirect_call_and_rtti_removal();

      const namespacet ns(goto_model.symbol_table);
      reaching_definitions_analysist rd_analysis(ns);
      rd_analysis(goto_model);
      rd_analysis.output(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-dependence-graph"))
    {
      do_indirect_call_and_rtti_removal();

      const namespacet ns(goto_model.symbol_table);
      dependence_grapht dependence_graph(ns);
      dependence_graph(goto_model);
      dependence_graph.output(goto_model, std::cout);
      dependence_graph.output_dot(std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("count-eloc"))
    {
      count_eloc(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("list-eloc"))
    {
      list_eloc(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("print-path-lengths"))
    {
      print_path_lengths(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("print-global-state-size"))
    {
      print_global_state_size(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("list-symbols"))
    {
      show_symbol_table_brief(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-uninitialized"))
    {
      show_uninitialized(goto_model, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("interpreter"))
    {
      do_indirect_call_and_rtti_removal();
      rewrite_union(goto_model);

      log.status() << "Starting interpreter" << messaget::eom;
      interpreter(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-claims") ||
       cmdline.isset("show-properties"))
    {
      const namespacet ns(goto_model.symbol_table);
      show_properties(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("document-claims-html") ||
       cmdline.isset("document-properties-html"))
    {
      document_properties_html(goto_model, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("document-claims-latex") ||
       cmdline.isset("document-properties-latex"))
    {
      document_properties_latex(goto_model, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(ui_message_handler.get_ui(), goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-natural-loops"))
    {
      show_natural_loops(goto_model, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-lexical-loops"))
    {
      show_lexical_loops(goto_model, std::cout);
    }

    if(cmdline.isset("print-internal-representation"))
    {
      for(auto const &pair : goto_model.goto_functions.function_map)
        for(auto const &ins : pair.second.body.instructions)
        {
          if(ins.get_code().is_not_nil())
            log.status() << ins.get_code().pretty() << messaget::eom;
          if(ins.has_condition())
          {
            log.status() << "[guard] " << ins.get_condition().pretty()
                         << messaget::eom;
          }
        }
      return CPROVER_EXIT_SUCCESS;
    }

    if(
      cmdline.isset("show-goto-functions") ||
      cmdline.isset("list-goto-functions"))
    {
      show_goto_functions(
        goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("list-undefined-functions"))
    {
      list_undefined_functions(goto_model, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    // experimental: print structs
    if(cmdline.isset("show-struct-alignment"))
    {
      print_struct_alignment_problems(goto_model.symbol_table, std::cout);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-locations"))
    {
      show_locations(ui_message_handler.get_ui(), goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(
      cmdline.isset("dump-c") || cmdline.isset("dump-cpp") ||
      cmdline.isset("dump-c-type-header"))
    {
      const bool is_cpp=cmdline.isset("dump-cpp");
      const bool is_header = cmdline.isset("dump-c-type-header");
      const bool h_libc=!cmdline.isset("no-system-headers");
      const bool h_all=cmdline.isset("use-all-headers");
      const bool harness=cmdline.isset("harness");
      namespacet ns(goto_model.symbol_table);

      // restore RETURN instructions in case remove_returns had been
      // applied
      restore_returns(goto_model);

      // dump_c (actually goto_program2code) requires valid instruction
      // location numbers:
      goto_model.goto_functions.update();

      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]));
        #else
        std::ofstream out(cmdline.args[1]);
        #endif
        if(!out)
        {
          log.error() << "failed to write to '" << cmdline.args[1] << "'";
          return CPROVER_EXIT_CONVERSION_FAILED;
        }
        if(is_header)
        {
          dump_c_type_header(
            goto_model.goto_functions,
            h_libc,
            h_all,
            harness,
            ns,
            cmdline.get_value("dump-c-type-header"),
            out);
        }
        else
        {
          (is_cpp ? dump_cpp : dump_c)(
            goto_model.goto_functions, h_libc, h_all, harness, ns, out);
        }
      }
      else
      {
        if(is_header)
        {
          dump_c_type_header(
            goto_model.goto_functions,
            h_libc,
            h_all,
            harness,
            ns,
            cmdline.get_value("dump-c-type-header"),
            std::cout);
        }
        else
        {
          (is_cpp ? dump_cpp : dump_c)(
            goto_model.goto_functions, h_libc, h_all, harness, ns, std::cout);
        }
      }

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("call-graph"))
    {
      do_indirect_call_and_rtti_removal();
      call_grapht call_graph(goto_model);

      if(cmdline.isset("xml"))
        call_graph.output_xml(std::cout);
      else if(cmdline.isset("dot"))
        call_graph.output_dot(std::cout);
      else
        call_graph.output(std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("reachable-call-graph"))
    {
      do_indirect_call_and_rtti_removal();
      call_grapht call_graph =
        call_grapht::create_from_root_function(
          goto_model, goto_functionst::entry_point(), false);
      if(cmdline.isset("xml"))
        call_graph.output_xml(std::cout);
      else if(cmdline.isset("dot"))
        call_graph.output_dot(std::cout);
      else
        call_graph.output(std::cout);

      return 0;
    }

    if(cmdline.isset("show-class-hierarchy"))
    {
      class_hierarchyt hierarchy;
      hierarchy(goto_model.symbol_table);
      if(cmdline.isset("dot"))
        hierarchy.output_dot(std::cout);
      else
        show_class_hierarchy(hierarchy, ui_message_handler);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("dot"))
    {
      namespacet ns(goto_model.symbol_table);

      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]));
        #else
        std::ofstream out(cmdline.args[1]);
        #endif
        if(!out)
        {
          log.error() << "failed to write to " << cmdline.args[1] << "'";
          return CPROVER_EXIT_CONVERSION_FAILED;
        }

        dot(goto_model, out);
      }
      else
        dot(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("accelerate"))
    {
      do_indirect_call_and_rtti_removal();

      namespacet ns(goto_model.symbol_table);

      log.status() << "Performing full inlining" << messaget::eom;
      goto_inline(goto_model, ui_message_handler);

      log.status() << "Removing calls to functions without a body"
                   << messaget::eom;
      remove_calls_no_bodyt remove_calls_no_body;
      remove_calls_no_body(goto_model.goto_functions);

      log.status() << "Accelerating" << messaget::eom;
      guard_managert guard_manager;
      accelerate_functions(
        goto_model, ui_message_handler, cmdline.isset("z3"), guard_manager);
      remove_skip(goto_model);
    }

    if(cmdline.isset("horn-encoding"))
    {
      log.status() << "Horn-clause encoding" << messaget::eom;
      namespacet ns(goto_model.symbol_table);

      if(cmdline.args.size()==2)
      {
        #ifdef _MSC_VER
        std::ofstream out(widen(cmdline.args[1]));
        #else
        std::ofstream out(cmdline.args[1]);
        #endif

        if(!out)
        {
          log.error() << "Failed to open output file " << cmdline.args[1]
                      << messaget::eom;
          return CPROVER_EXIT_CONVERSION_FAILED;
        }

        horn_encoding(goto_model, out);
      }
      else
        horn_encoding(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("drop-unused-functions"))
    {
      do_indirect_call_and_rtti_removal();

      log.status() << "Removing unused functions" << messaget::eom;
      remove_unused_functions(goto_model.goto_functions, ui_message_handler);
    }

    if(cmdline.isset("undefined-function-is-assume-false"))
    {
      do_indirect_call_and_rtti_removal();
      undefined_function_abort_path(goto_model);
    }

    // write new binary?
    if(cmdline.args.size()==2)
    {
      log.status() << "Writing GOTO program to '" << cmdline.args[1] << "'"
                   << messaget::eom;

      if(write_goto_binary(cmdline.args[1], goto_model, ui_message_handler))
        return CPROVER_EXIT_CONVERSION_FAILED;
      else
        return CPROVER_EXIT_SUCCESS;
    }
    else if(cmdline.args.size() < 2)
    {
      throw invalid_command_line_argument_exceptiont(
        "Invalid number of positional arguments passed",
        "[in] [out]",
        "goto-instrument needs one input and one output file, aside from other "
        "flags");
    }

    help();
    return CPROVER_EXIT_USAGE_ERROR;
  }
// NOLINTNEXTLINE(readability/fn_size)
}

void goto_instrument_parse_optionst::do_indirect_call_and_rtti_removal(
  bool force)
{
  if(function_pointer_removal_done && !force)
    return;

  function_pointer_removal_done=true;

  log.status() << "Function Pointer Removal" << messaget::eom;
  remove_function_pointers(
    ui_message_handler, goto_model, cmdline.isset("pointer-check"));
  log.status() << "Virtual function removal" << messaget::eom;
  remove_virtual_functions(goto_model);
  log.status() << "Cleaning inline assembler statements" << messaget::eom;
  remove_asm(goto_model);
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

  log.status() << "Removing const function pointers only" << messaget::eom;
  remove_function_pointers(
    ui_message_handler,
    goto_model,
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
    log.status() << "Partial Inlining" << messaget::eom;
    goto_partial_inline(goto_model, ui_message_handler);
  }
}

void goto_instrument_parse_optionst::do_remove_returns()
{
  if(remove_returns_done)
    return;

  remove_returns_done=true;

  log.status() << "Removing returns" << messaget::eom;
  remove_returns(goto_model);
}

void goto_instrument_parse_optionst::get_goto_program()
{
  log.status() << "Reading GOTO program from '" << cmdline.args[0] << "'"
               << messaget::eom;

  config.set(cmdline);

  auto result = read_goto_binary(cmdline.args[0], ui_message_handler);

  if(!result.has_value())
    throw 0;

  goto_model = std::move(result.value());

  config.set_from_symbol_table(goto_model.symbol_table);
}

void goto_instrument_parse_optionst::instrument_goto_program()
{
  optionst options;

  parse_nondet_volatile_options(cmdline, options);

  // disable simplify when adding various checks?
  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);
  else
    options.set_option("simplify", true);

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // unwind loops
  if(cmdline.isset("unwind"))
  {
    log.status() << "Unwinding loops" << messaget::eom;
    options.set_option("unwind", cmdline.get_value("unwind"));
  }

  {
    parse_function_pointer_restriction_options_from_cmdline(cmdline, options);

    if(
      options.is_set(RESTRICT_FUNCTION_POINTER_OPT) ||
      options.is_set(RESTRICT_FUNCTION_POINTER_BY_NAME_OPT) ||
      options.is_set(RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT))
    {
      label_function_pointer_call_sites(goto_model);

      const auto function_pointer_restrictions =
        function_pointer_restrictionst::from_options(
          options, goto_model, log.get_message_handler());

      restrict_function_pointers(
        ui_message_handler, goto_model, function_pointer_restrictions);
    }
  }

  // skip over selected loops
  if(cmdline.isset("skip-loops"))
  {
    log.status() << "Adding gotos to skip loops" << messaget::eom;
    if(skip_loops(
         goto_model, cmdline.get_value("skip-loops"), ui_message_handler))
      throw 0;
  }

  namespacet ns(goto_model.symbol_table);

  // initialize argv with valid pointers
  if(cmdline.isset("model-argc-argv"))
  {
    unsigned max_argc=
      safe_string2unsigned(cmdline.get_value("model-argc-argv"));

    log.status() << "Adding up to " << max_argc << " command line arguments"
                 << messaget::eom;
    if(model_argc_argv(goto_model, max_argc, ui_message_handler))
      throw 0;
  }

  if(cmdline.isset("remove-function-body"))
  {
    remove_functions(
      goto_model,
      cmdline.get_values("remove-function-body"),
      ui_message_handler);
  }

  // we add the library in some cases, as some analyses benefit

  if(cmdline.isset("add-library") ||
     cmdline.isset("mm"))
  {
    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
    {
      config.ansi_c.defines.push_back(
        std::string(CPROVER_PREFIX) + "CUSTOM_BITVECTOR_ANALYSIS");
    }

    // add the library
    log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
                 << messaget::eom;
    link_to_library(
      goto_model, ui_message_handler, cprover_cpp_library_factory);
    link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);
  }

  // now do full inlining, if requested
  if(cmdline.isset("inline"))
  {
    do_indirect_call_and_rtti_removal(true);

    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
    {
      do_remove_returns();
      thread_exit_instrumentation(goto_model);
      mutex_init_instrumentation(goto_model);
    }

    log.status() << "Performing full inlining" << messaget::eom;
    goto_inline(goto_model, ui_message_handler, true);
  }

  if(cmdline.isset("show-custom-bitvector-analysis") ||
     cmdline.isset("custom-bitvector-analysis"))
  {
    log.status() << "Propagating Constants" << messaget::eom;
    constant_propagator_ait constant_propagator_ai(goto_model);
    remove_skip(goto_model);
  }

  if(cmdline.isset("escape-analysis"))
  {
    do_indirect_call_and_rtti_removal();
    do_remove_returns();
    parameter_assignments(goto_model);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    log.status() << "Escape Analysis" << messaget::eom;
    escape_analysist escape_analysis;
    escape_analysis(goto_model);
    escape_analysis.instrument(goto_model);

    // inline added functions, they are often small
    goto_partial_inline(goto_model, ui_message_handler);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();
  }

  if(
    cmdline.isset(FLAG_LOOP_CONTRACTS) || cmdline.isset(FLAG_REPLACE_CALL) ||
    cmdline.isset(FLAG_ENFORCE_CONTRACT))
  {
    do_indirect_call_and_rtti_removal();
    code_contractst contracts(goto_model, log);

    std::set<std::string> to_replace(
      cmdline.get_values(FLAG_REPLACE_CALL).begin(),
      cmdline.get_values(FLAG_REPLACE_CALL).end());

    std::set<std::string> to_enforce(
      cmdline.get_values(FLAG_ENFORCE_CONTRACT).begin(),
      cmdline.get_values(FLAG_ENFORCE_CONTRACT).end());

    // It’s important to keep the order of contracts instrumentation, i.e.,
    // first replacement then enforcement. We rely on contract replacement
    // and inlining of sub-function calls to properly annotate all
    // assignments.
    contracts.replace_calls(to_replace);
    contracts.enforce_contracts(to_enforce);

    if(cmdline.isset(FLAG_LOOP_CONTRACTS))
      contracts.apply_loop_contracts();
  }

  if(cmdline.isset("value-set-fi-fp-removal"))
  {
    value_set_fi_fp_removal(goto_model, ui_message_handler);
    do_indirect_call_and_rtti_removal();
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

  if(cmdline.isset("replace-calls"))
  {
    do_indirect_call_and_rtti_removal();

    replace_callst replace_calls;
    replace_calls(goto_model, cmdline.get_values("replace-calls"));
  }

  if(cmdline.isset("function-inline"))
  {
    std::string function=cmdline.get_value("function-inline");
    PRECONDITION(!function.empty());

    bool caching=!cmdline.isset("no-caching");

    do_indirect_call_and_rtti_removal();

    log.status() << "Inlining calls of function '" << function << "'"
                 << messaget::eom;

    if(!cmdline.isset("log"))
    {
      goto_function_inline(
        goto_model, function, ui_message_handler, true, caching);
    }
    else
    {
      std::string filename=cmdline.get_value("log");
      bool have_file=!filename.empty() && filename!="-";

      jsont result = goto_function_inline_and_log(
        goto_model, function, ui_message_handler, true, caching);

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

    goto_model.goto_functions.update();
    goto_model.goto_functions.compute_loop_numbers();
  }

  if(cmdline.isset("partial-inline"))
  {
    do_indirect_call_and_rtti_removal();

    log.status() << "Partial inlining" << messaget::eom;
    goto_partial_inline(goto_model, ui_message_handler, 0, true);

    goto_model.goto_functions.update();
    goto_model.goto_functions.compute_loop_numbers();
  }

  if(cmdline.isset("remove-calls-no-body"))
  {
    log.status() << "Removing calls to functions without a body"
                 << messaget::eom;

    remove_calls_no_bodyt remove_calls_no_body;
    remove_calls_no_body(goto_model.goto_functions);

    goto_model.goto_functions.update();
    goto_model.goto_functions.compute_loop_numbers();
  }

  if(cmdline.isset("constant-propagator"))
  {
    do_indirect_call_and_rtti_removal();

    log.status() << "Propagating Constants" << messaget::eom;

    constant_propagator_ait constant_propagator_ai(goto_model);
    remove_skip(goto_model);
  }

  if(cmdline.isset("generate-function-body"))
  {
    optionst c_object_factory_options;
    parse_c_object_factory_options(cmdline, c_object_factory_options);
    c_object_factory_parameterst object_factory_parameters(
      c_object_factory_options);

    auto generate_implementation = generate_function_bodies_factory(
      cmdline.get_value("generate-function-body-options"),
      object_factory_parameters,
      goto_model.symbol_table,
      ui_message_handler);
    generate_function_bodies(
      std::regex(cmdline.get_value("generate-function-body")),
      *generate_implementation,
      goto_model,
      ui_message_handler);
  }

  if(cmdline.isset("generate-havocing-body"))
  {
    optionst c_object_factory_options;
    parse_c_object_factory_options(cmdline, c_object_factory_options);
    c_object_factory_parameterst object_factory_parameters(
      c_object_factory_options);

    auto options_split =
      split_string(cmdline.get_value("generate-havocing-body"), ',');
    if(options_split.size() < 2)
      throw invalid_command_line_argument_exceptiont{
        "not enough arguments for this option", "--generate-havocing-body"};

    if(options_split.size() == 2)
    {
      auto generate_implementation = generate_function_bodies_factory(
        std::string{"havoc,"} + options_split.back(),
        object_factory_parameters,
        goto_model.symbol_table,
        ui_message_handler);
      generate_function_bodies(
        std::regex(options_split[0]),
        *generate_implementation,
        goto_model,
        ui_message_handler);
    }
    else
    {
      CHECK_RETURN(options_split.size() % 2 == 1);
      for(size_t i = 1; i + 1 < options_split.size(); i += 2)
      {
        auto generate_implementation = generate_function_bodies_factory(
          std::string{"havoc,"} + options_split[i + 1],
          object_factory_parameters,
          goto_model.symbol_table,
          ui_message_handler);
        generate_function_bodies(
          options_split[0],
          options_split[i],
          *generate_implementation,
          goto_model,
          ui_message_handler);
      }
    }
  }

  // add generic checks, if needed
  goto_check(options, goto_model);

  // check for uninitalized local variables
  if(cmdline.isset("uninitialized-check"))
  {
    log.status() << "Adding checks for uninitialized local variables"
                 << messaget::eom;
    add_uninitialized_locals_assertions(goto_model);
  }

  // check for maximum call stack size
  if(cmdline.isset("stack-depth"))
  {
    log.status() << "Adding check for maximum call stack size" << messaget::eom;
    stack_depth(
      goto_model,
      safe_string2size_t(cmdline.get_value("stack-depth")));
  }

  // ignore default/user-specified initialization of variables with static
  // lifetime
  if(cmdline.isset("nondet-static-exclude"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables except for "
                    "the specified ones."
                 << messaget::eom;

    nondet_static(goto_model, cmdline.get_values("nondet-static-exclude"));
  }
  else if(cmdline.isset("nondet-static"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables"
                 << messaget::eom;
    nondet_static(goto_model);
  }

  if(cmdline.isset("slice-global-inits"))
  {
    log.status() << "Slicing away initializations of unused global variables"
                 << messaget::eom;
    slice_global_inits(goto_model);
  }

  if(cmdline.isset("string-abstraction"))
  {
    do_indirect_call_and_rtti_removal();
    do_remove_returns();

    log.status() << "String Abstraction" << messaget::eom;
    string_abstraction(goto_model, ui_message_handler);
  }

  // some analyses require function pointer removal and partial inlining

  if(cmdline.isset("remove-pointers") ||
     cmdline.isset("race-check") ||
     cmdline.isset("mm") ||
     cmdline.isset("isr") ||
     cmdline.isset("concurrency"))
  {
    do_indirect_call_and_rtti_removal();

    log.status() << "Pointer Analysis" << messaget::eom;
    value_set_analysist value_set_analysis(ns);
    value_set_analysis(goto_model.goto_functions);

    if(cmdline.isset("remove-pointers"))
    {
      // removing pointers
      log.status() << "Removing Pointers" << messaget::eom;
      remove_pointers(goto_model, value_set_analysis);
    }

    if(cmdline.isset("race-check"))
    {
      log.status() << "Adding Race Checks" << messaget::eom;
      race_check(value_set_analysis, goto_model);
    }

    if(cmdline.isset("mm"))
    {
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

      const unsigned max_var=
        cmdline.isset("max-var")?
        unsafe_string2unsigned(cmdline.get_value("max-var")):0;
      const unsigned max_po_trans=
        cmdline.isset("max-po-trans")?
        unsafe_string2unsigned(cmdline.get_value("max-po-trans")):0;

      if(mm=="tso")
      {
        log.status() << "Adding weak memory (TSO) Instrumentation"
                     << messaget::eom;
        model=TSO;
      }
      else if(mm=="pso")
      {
        log.status() << "Adding weak memory (PSO) Instrumentation"
                     << messaget::eom;
        model=PSO;
      }
      else if(mm=="rmo")
      {
        log.status() << "Adding weak memory (RMO) Instrumentation"
                     << messaget::eom;
        model=RMO;
      }
      else if(mm=="power")
      {
        log.status() << "Adding weak memory (Power) Instrumentation"
                     << messaget::eom;
        model=Power;
      }
      else
      {
        log.error() << "Unknown weak memory model '" << mm << "'"
                    << messaget::eom;
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
          goto_model,
          cmdline.isset("scc"),
          inst_strategy,
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
          ui_message_handler,
          cmdline.isset("ignore-arrays"));
    }

    // Interrupt handler
    if(cmdline.isset("isr"))
    {
      log.status() << "Instrumenting interrupt handler" << messaget::eom;
      interrupt(
        value_set_analysis,
        goto_model,
        cmdline.get_value("isr"));
    }

    // Memory-mapped I/O
    if(cmdline.isset("mmio"))
    {
      log.status() << "Instrumenting memory-mapped I/O" << messaget::eom;
      mmio(value_set_analysis, goto_model);
    }

    if(cmdline.isset("concurrency"))
    {
      log.status() << "Sequentializing concurrency" << messaget::eom;
      concurrency(value_set_analysis, goto_model);
    }
  }

  if(cmdline.isset("interval-analysis"))
  {
    log.status() << "Interval analysis" << messaget::eom;
    interval_analysis(goto_model);
  }

  if(cmdline.isset("havoc-loops"))
  {
    log.status() << "Havocking loops" << messaget::eom;
    havoc_loops(goto_model);
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

    log.status() << "Instrumenting k-induction for k=" << k << ", "
                 << (base_case ? "base case" : "step case") << messaget::eom;

    k_induction(goto_model, base_case, step_case, k);
  }

  if(cmdline.isset("function-enter"))
  {
    log.status() << "Function enter instrumentation" << messaget::eom;
    function_enter(
      goto_model,
      cmdline.get_value("function-enter"));
  }

  if(cmdline.isset("function-exit"))
  {
    log.status() << "Function exit instrumentation" << messaget::eom;
    function_exit(
      goto_model,
      cmdline.get_value("function-exit"));
  }

  if(cmdline.isset("branch"))
  {
    log.status() << "Branch instrumentation" << messaget::eom;
    branch(
      goto_model,
      cmdline.get_value("branch"));
  }

  // add failed symbols
  add_failed_symbols(goto_model.symbol_table);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // add loop ids
  goto_model.goto_functions.compute_loop_numbers();

  // label the assertions
  label_properties(goto_model);

  nondet_volatile(goto_model, options);

  // reachability slice?
  if(cmdline.isset("reachability-slice"))
  {
    do_indirect_call_and_rtti_removal();

    log.status() << "Performing a reachability slice" << messaget::eom;

    // reachability_slicer requires that the model has unique location numbers:
    goto_model.goto_functions.update();

    if(cmdline.isset("property"))
      reachability_slicer(goto_model, cmdline.get_values("property"));
    else
      reachability_slicer(goto_model);
  }

  if(cmdline.isset("fp-reachability-slice"))
  {
    do_indirect_call_and_rtti_removal();

    log.status() << "Performing a function pointer reachability slice"
                 << messaget::eom;
    function_path_reachability_slicer(
      goto_model, cmdline.get_comma_separated_values("fp-reachability-slice"));
  }

  // full slice?
  if(cmdline.isset("full-slice"))
  {
    do_indirect_call_and_rtti_removal();
    do_remove_returns();

    log.status() << "Performing a full slice" << messaget::eom;
    if(cmdline.isset("property"))
      property_slicer(goto_model, cmdline.get_values("property"));
    else
    {
      // full_slicer requires that the model has unique location numbers:
      goto_model.goto_functions.update();
      full_slicer(goto_model);
    }
  }

  // splice option
  if(cmdline.isset("splice-call"))
  {
    log.status() << "Performing call splicing" << messaget::eom;
    std::string callercallee=cmdline.get_value("splice-call");
    if(splice_call(
         goto_model.goto_functions,
         callercallee,
         goto_model.symbol_table,
         ui_message_handler))
      throw 0;
  }

  // aggressive slicer
  if(cmdline.isset("aggressive-slice"))
  {
    do_indirect_call_and_rtti_removal();

    // reachability_slicer requires that the model has unique location numbers:
    goto_model.goto_functions.update();

    log.status() << "Slicing away initializations of unused global variables"
                 << messaget::eom;
    slice_global_inits(goto_model);

    log.status() << "Performing an aggressive slice" << messaget::eom;
    aggressive_slicert aggressive_slicer(goto_model, ui_message_handler);

    if(cmdline.isset("aggressive-slice-call-depth"))
      aggressive_slicer.call_depth =
        safe_string2unsigned(cmdline.get_value("aggressive-slice-call-depth"));

    if(cmdline.isset("aggressive-slice-preserve-function"))
      aggressive_slicer.preserve_functions(
        cmdline.get_values("aggressive-slice-preserve-function"));

    if(cmdline.isset("property"))
      aggressive_slicer.user_specified_properties =
        cmdline.get_values("property");

    if(cmdline.isset("aggressive-slice-preserve-functions-containing"))
      aggressive_slicer.name_snippets =
        cmdline.get_values("aggressive-slice-preserve-functions-containing");

    aggressive_slicer.preserve_all_direct_paths =
      cmdline.isset("aggressive-slice-preserve-all-direct-paths");

    aggressive_slicer.doit();

    goto_model.goto_functions.update();

    log.status() << "Performing a reachability slice" << messaget::eom;
    if(cmdline.isset("property"))
      reachability_slicer(goto_model, cmdline.get_values("property"));
    else
      reachability_slicer(goto_model);
  }

  if(cmdline.isset("ensure-one-backedge-per-target"))
  {
    log.status() << "Trying to force one backedge per target" << messaget::eom;
    ensure_one_backedge_per_target(goto_model);
  }

  // recalculate numbers, etc.
  goto_model.goto_functions.update();
}

/// display command line help
void goto_instrument_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("Goto-Instrument", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2008-2013") << '\n'
            << align_center_with_border("Daniel Kroening") << '\n'
            << align_center_with_border("kroening@kroening.com") << '\n'
            <<
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
    " --dump-c-type-header m       generate a C header for types local in m\n"
    " --dump-cpp                   generate C++ source\n"
    " --dot                        generate CFG graph in DOT format\n"
    " --interpreter                do concrete execution\n"
    "\n"
    "Diagnosis:\n"
    " --show-loops                 show the loops in the program\n"
    HELP_SHOW_PROPERTIES
    " --show-symbol-table          show loaded symbol table\n"
    " --list-symbols               list symbols with type information\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_GOTO_PROGRAM_STATS
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    " --print-internal-representation\n" // NOLINTNEXTLINE(*)
    "                              show verbose internal representation of the program\n"
    " --list-undefined-functions   list functions without body\n"
    " --show-struct-alignment      show struct members that might be concurrently accessed\n" // NOLINT(*)
    " --show-natural-loops         show natural loop heads\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --list-calls-args            list all function calls with their arguments\n"
    " --call-graph                 show graph of function calls\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --reachable-call-graph       show graph of function calls potentially reachable from main function\n"
    HELP_SHOW_CLASS_HIERARCHY
    // NOLINTNEXTLINE(whitespace/line_length)
    " --show-threaded              show instructions that may be executed by more than one thread\n"
    " --show-local-safe-pointers   show pointer expressions that are trivially dominated by a not-null check\n" // NOLINT(*)
    " --show-safe-dereferences     show pointer expressions that are trivially dominated by a not-null check\n" // NOLINT(*)
    "                              *and* used as a dereference operand\n" // NOLINT(*)
    HELP_VALIDATE
    // NOLINTNEXTLINE(whitespace/line_length)
    " --validate-goto-binary       check the well-formedness of the passed in goto\n"
    "                              binary and then exit\n"
    "\n"
    "Safety checks:\n"
    " --no-assertions              ignore user assertions\n"
    HELP_GOTO_CHECK
    " --uninitialized-check        add checks for uninitialized locals (experimental)\n" // NOLINT(*)
    " --stack-depth n              add check that call stack size of non-inlined functions never exceeds n\n" // NOLINT(*)
    " --race-check                 add floating-point data race checks\n"
    "\n"
    "Semantic transformations:\n"
    << HELP_NONDET_VOLATILE <<
    " --unwind <n>                 unwinds the loops <n> times\n"
    " --unwindset L:B,...          unwind loop L with a bound of B\n"
    " --unwindset-file <file>      read unwindset from file\n"
    " --partial-loops              permit paths with partial loops\n"
    " --unwinding-assertions       generate unwinding assertions\n"
    " --continue-as-loops          add loop for remaining iterations after unwound part\n" // NOLINT(*)
    " --isr <function>             instruments an interrupt service routine\n"
    " --mmio                       instruments memory-mapped I/O\n"
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n" // NOLINT(*)
    " --nondet-static-exclude e    same as nondet-static except for the variable e\n" //NOLINT(*)
    "                              (use multiple times if required)\n"
    " --check-invariant function   instruments invariant checking function\n"
    " --remove-pointers            converts pointer arithmetic to base+offset expressions\n" // NOLINT(*)
    " --splice-call caller,callee  prepends a call to callee in the body of caller\n"  // NOLINT(*)
    " --undefined-function-is-assume-false\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    "                              convert each call to an undefined function to assume(false)\n"
    HELP_INSERT_FINAL_ASSERT_FALSE
    HELP_REPLACE_FUNCTION_BODY
    HELP_ANSI_C_LANGUAGE
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
    HELP_REACHABILITY_SLICER
    " --full-slice                 slice away instructions that don't affect assertions\n" // NOLINT(*)
    " --property id                slice with respect to specific property only\n" // NOLINT(*)
    " --slice-global-inits         slice away initializations of unused global variables\n" // NOLINT(*)
    " --aggressive-slice           remove bodies of any functions not on the shortest path between\n" // NOLINT(*)
    "                              the start function and the function containing the property(s)\n" // NOLINT(*)
    " --aggressive-slice-call-depth <n>\n"
    "                              used with aggressive-slice, preserves all functions within <n> function calls\n" // NOLINT(*)
    "                              of the functions on the shortest path\n"
    " --aggressive-slice-preserve-function <f>\n"
    "                             force the aggressive slicer to preserve function <f>\n" // NOLINT(*)
    " --aggressive-slice-preserve-function containing <f>\n"
    "                              force the aggressive slicer to preserve all functions with names containing <f>\n" // NOLINT(*)
    "--aggressive-slice-preserve-all-direct-paths \n"
    "                             force aggressive slicer to preserve all direct paths\n" // NOLINT(*)
    "\n"
    "Further transformations:\n"
    " --constant-propagator        propagate constants and simplify expressions\n" // NOLINT(*)
    " --inline                     perform full inlining\n"
    " --partial-inline             perform partial inlining\n"
    " --function-inline <function> transitively inline all calls <function> makes\n" // NOLINT(*)
    " --no-caching                 disable caching of intermediate results during transitive function inlining\n" // NOLINT(*)
    " --log <file>                 log in json format which code segments were inlined, use with --function-inline\n" // NOLINT(*)
    " --remove-function-pointers   replace function pointers by case statement over function calls\n" // NOLINT(*)
    " --value-set-fi-fp-removal    build flow-insensitive value set and replace function pointers by a case statement\n" // NOLINT(*)
    "                              over the possible assignments. If the set of possible assignments is empty the function pointer\n" // NOLINT(*)
    "                              is removed using the standard remove-function-pointers pass. \n" // NOLINT(*)
    HELP_RESTRICT_FUNCTION_POINTER
    HELP_REMOVE_CALLS_NO_BODY
    HELP_REMOVE_CONST_FUNCTION_POINTERS
    " --add-library                add models of C library functions\n"
    " --model-argc-argv <n>        model up to <n> command line arguments\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --remove-function-body <f>   remove the implementation of function <f> (may be repeated)\n"
    HELP_REPLACE_CALLS
    "\n"
    "Code contracts:\n"
    HELP_LOOP_CONTRACTS
    HELP_REPLACE_CALL
    HELP_ENFORCE_CONTRACT
    "\n"
    "Other options:\n"
    " --no-system-headers          with --dump-c/--dump-cpp: generate C source expanding libc includes\n" // NOLINT(*)
    " --use-all-headers            with --dump-c/--dump-cpp: generate C source with all includes\n" // NOLINT(*)
    " --harness                    with --dump-c/--dump-cpp: include input generator in output\n" // NOLINT(*)
    " --version                    show version and exit\n"
    HELP_FLUSH
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
