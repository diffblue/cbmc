/*******************************************************************\

Module: Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Main Module

#include "goto_instrument_parse_options.h"

#include <util/exception_utils.h>
#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/json.h>
#include <util/options.h>
#include <util/string2int.h>
#include <util/string_utils.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/ensure_one_backedge_per_target.h>
#include <goto-programs/goto_check.h>
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
#include <goto-programs/rewrite_rw_ok.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/slice_global_inits.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/write_goto_binary.h>

#include <analyses/call_graph.h>
#include <analyses/constant_propagator.h>
#include <analyses/custom_bitvector_analysis.h>
#include <analyses/dependence_graph.h>
#include <analyses/escape_analysis.h>
#include <analyses/global_may_alias.h>
#include <analyses/guard.h>
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
#include <ansi-c/gcc_version.h>
#include <assembler/remove_asm.h>
#include <cpp/cprover_library.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/show_value_sets.h>
#include <pointer-analysis/value_set_analysis.h>

#include "alignment_checks.h"
#include "branch.h"
#include "call_sequences.h"
#include "concurrency.h"
#include "dot.h"
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
#include "remove_function.h"
#include "rw_set.h"
#include "show_locations.h"
#include "skip_loops.h"
#include "splice_call.h"
#include "stack_depth.h"
#include "thread_instrumentation.h"
#include "undefined_functions.h"
#include "unwind.h"
#include "value_set_fi_fp_removal.h"

#include <fstream> // IWYU pragma: keep
#include <iostream>
#include <memory>

#include "accelerate/accelerate.h"

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

    // configure gcc, if required -- get_goto_program will have set the config
    if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
    {
      gcc_versiont gcc_version;
      gcc_version.get("gcc");
      configure_gcc(gcc_version);
    }

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

    // ignore default/user-specified initialization
    // of matching variables with static lifetime
    if(cmdline.isset("nondet-static-matching"))
    {
      log.status() << "Adding nondeterministic initialization "
                      "of matching static/global variables"
                   << messaget::eom;
      nondet_static_matching(
        goto_model, cmdline.get_value("nondet-static-matching"));
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
        unwindsett unwindset{goto_model};

        if(unwind_given)
          unwindset.parse_unwind(cmdline.get_value("unwind"));

        if(unwindset_file_given)
        {
          unwindset.parse_unwindset_file(
            cmdline.get_value("unwindset-file"), ui_message_handler);
        }

        if(unwindset_given)
        {
          unwindset.parse_unwindset(
            cmdline.get_comma_separated_values("unwindset"),
            ui_message_handler);
        }

        bool unwinding_assertions=cmdline.isset("unwinding-assertions");
        bool partial_loops=cmdline.isset("partial-loops");
        bool continue_as_loops=cmdline.isset("continue-as-loops");
        if(continue_as_loops)
        {
          if(unwinding_assertions)
          {
            throw "unwinding assertions cannot be used with "
              "--continue-as-loops";
          }
          else if(partial_loops)
            throw "partial loops cannot be used with --continue-as-loops";
        }

        goto_unwindt::unwind_strategyt unwind_strategy=
          goto_unwindt::unwind_strategyt::ASSUME;

        if(unwinding_assertions)
        {
          if(partial_loops)
            unwind_strategy = goto_unwindt::unwind_strategyt::ASSERT_PARTIAL;
          else
            unwind_strategy = goto_unwindt::unwind_strategyt::ASSERT_ASSUME;
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
            std::ofstream of(widen_if_needed(filename));

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
          i_it->output(std::cout);
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
      value_set_analysis(goto_model);
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
      value_set_analysis(goto_model);

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
      rewrite_rw_ok(goto_model);

      const namespacet ns(goto_model.symbol_table);
      reaching_definitions_analysist rd_analysis(ns);
      rd_analysis(goto_model);
      rd_analysis.output(goto_model, std::cout);

      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-dependence-graph"))
    {
      do_indirect_call_and_rtti_removal();
      rewrite_rw_ok(goto_model);

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
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("print-internal-representation"))
    {
      for(auto const &pair : goto_model.goto_functions.function_map)
        for(auto const &ins : pair.second.body.instructions)
        {
          if(ins.code().is_not_nil())
            log.status() << ins.code().pretty() << messaget::eom;
          if(ins.has_condition())
          {
            log.status() << "[guard] " << ins.condition().pretty()
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
        std::ofstream out(widen_if_needed(cmdline.args[1]));

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
        std::ofstream out(widen_if_needed(cmdline.args[1]));

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
      remove_calls_no_body(goto_model.goto_functions, ui_message_handler);

      log.status() << "Accelerating" << messaget::eom;
      guard_managert guard_manager;
      accelerate_functions(
        goto_model, ui_message_handler, cmdline.isset("z3"), guard_manager);
      remove_skip(goto_model);
    }

    if(cmdline.isset("horn"))
    {
      log.status() << "Horn-clause encoding" << messaget::eom;
      namespacet ns(goto_model.symbol_table);

      if(cmdline.args.size()==2)
      {
        std::ofstream out(widen_if_needed(cmdline.args[1]));

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
  remove_function_pointers(ui_message_handler, goto_model, false);
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

  if(
    cmdline.isset("add-library") || cmdline.isset("mm") ||
    cmdline.isset("reachability-slice") ||
    cmdline.isset("reachability-slice-fb") ||
    cmdline.isset("fp-reachability-slice"))
  {
    if(cmdline.isset("show-custom-bitvector-analysis") ||
       cmdline.isset("custom-bitvector-analysis"))
    {
      config.ansi_c.defines.push_back(
        std::string(CPROVER_PREFIX) + "CUSTOM_BITVECTOR_ANALYSIS");
    }

    // remove inline assembler as that may yield further library function calls
    // that need to be resolved
    remove_asm(goto_model);

    // add the library
    log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
                 << messaget::eom;
    link_to_library(
      goto_model, ui_message_handler, cprover_cpp_library_factory);
    link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);
  }

  {
    parse_function_pointer_restriction_options_from_cmdline(cmdline, options);

    if(
      options.is_set(RESTRICT_FUNCTION_POINTER_OPT) ||
      options.is_set(RESTRICT_FUNCTION_POINTER_BY_NAME_OPT) ||
      options.is_set(RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT))
    {
      label_function_pointer_call_sites(goto_model);

      restrict_function_pointers(ui_message_handler, goto_model, options);
    }
  }

  // skip over selected loops
  if(cmdline.isset("skip-loops"))
  {
    log.status() << "Adding gotos to skip loops" << messaget::eom;
    if(skip_loops(
         goto_model, cmdline.get_value("skip-loops"), ui_message_handler))
    {
      throw 0;
    }
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

  if(cmdline.isset("loop-contracts-file"))
  {
    const auto file_name = cmdline.get_value("loop-contracts-file");
    contracts_wranglert contracts_wrangler(
      goto_model, file_name, ui_message_handler);
  }

  bool use_dfcc = cmdline.isset(FLAG_DFCC);
  if(use_dfcc)
  {
    if(cmdline.get_values(FLAG_DFCC).size() != 1)
    {
      throw invalid_command_line_argument_exceptiont(
        "Redundant options detected",
        "--" FLAG_DFCC,
        "Use a single " FLAG_DFCC " option");
    }

    do_indirect_call_and_rtti_removal();

    const irep_idt harness_id(cmdline.get_value(FLAG_DFCC));

    std::set<irep_idt> to_replace(
      cmdline.get_values(FLAG_REPLACE_CALL).begin(),
      cmdline.get_values(FLAG_REPLACE_CALL).end());

    if(
      !cmdline.get_values(FLAG_ENFORCE_CONTRACT).empty() &&
      !cmdline.get_values(FLAG_ENFORCE_CONTRACT_REC).empty())
    {
      throw invalid_command_line_argument_exceptiont(
        "Mutually exclusive options detected",
        "--" FLAG_ENFORCE_CONTRACT " and --" FLAG_ENFORCE_CONTRACT_REC
        "Use either --" FLAG_ENFORCE_CONTRACT
        " or --" FLAG_ENFORCE_CONTRACT_REC);
    }

    auto &to_enforce = !cmdline.get_values(FLAG_ENFORCE_CONTRACT_REC).empty()
                         ? cmdline.get_values(FLAG_ENFORCE_CONTRACT_REC)
                         : cmdline.get_values(FLAG_ENFORCE_CONTRACT);

    bool allow_recursive_calls =
      !cmdline.get_values(FLAG_ENFORCE_CONTRACT_REC).empty();

    std::set<std::string> to_exclude_from_nondet_static(
      cmdline.get_values("nondet-static-exclude").begin(),
      cmdline.get_values("nondet-static-exclude").end());

    if(
      cmdline.isset(FLAG_LOOP_CONTRACTS) &&
      cmdline.isset(FLAG_LOOP_CONTRACTS_NO_UNWIND))
    {
      // When the model is produced by Kani, we must not automatically unwind
      // the backjump introduced by the loop transformation.
      // Automatic unwinding duplicates assertions found in the loop body, and
      // since Kani expects property identifiers to remain unique. Having
      // duplicate instances of the assertions makes Kani fail to handle the
      // analysis results.
      log.warning() << "**** WARNING: transformed loops will not be unwound "
                    << "after applying loop contracts. Remember to unwind "
                    << "them at least twice to pass unwinding-assertions."
                    << messaget::eom;
    }

    dfcc(
      options,
      goto_model,
      harness_id,
      to_enforce.empty() ? optionalt<irep_idt>{}
                         : optionalt<irep_idt>{to_enforce.front()},
      allow_recursive_calls,
      to_replace,
      cmdline.isset(FLAG_LOOP_CONTRACTS),
      !cmdline.isset(FLAG_LOOP_CONTRACTS_NO_UNWIND),
      to_exclude_from_nondet_static,
      log.get_message_handler());
  }

  if(
    !use_dfcc &&
    (cmdline.isset(FLAG_LOOP_CONTRACTS) || cmdline.isset(FLAG_REPLACE_CALL) ||
     cmdline.isset(FLAG_ENFORCE_CONTRACT)))
  {
    do_indirect_call_and_rtti_removal();
    code_contractst contracts(goto_model, log);

    std::set<std::string> to_replace(
      cmdline.get_values(FLAG_REPLACE_CALL).begin(),
      cmdline.get_values(FLAG_REPLACE_CALL).end());

    std::set<std::string> to_enforce(
      cmdline.get_values(FLAG_ENFORCE_CONTRACT).begin(),
      cmdline.get_values(FLAG_ENFORCE_CONTRACT).end());

    std::set<std::string> to_exclude_from_nondet_static(
      cmdline.get_values("nondet-static-exclude").begin(),
      cmdline.get_values("nondet-static-exclude").end());

    // It's important to keep the order of contracts instrumentation, i.e.,
    // first replacement then enforcement. We rely on contract replacement
    // and inlining of sub-function calls to properly annotate all
    // assignments.
    contracts.replace_calls(to_replace);
    contracts.enforce_contracts(to_enforce, to_exclude_from_nondet_static);

    if(cmdline.isset(FLAG_LOOP_CONTRACTS))
    {
      if(cmdline.isset(FLAG_LOOP_CONTRACTS_NO_UNWIND))
      {
        contracts.unwind_transformed_loops = false;
        // When the model is produced by Kani, we must not automatically unwind
        // the backjump introduced by the loop transformation.
        // Automatic unwinding duplicates assertions found in the loop body, and
        // since Kani expects property identifiers to remain unique. Having
        // duplicate instances of the assertions makes Kani fail to handle the
        // analysis results.
        log.warning() << "**** WARNING: transformed loops will not be unwound "
                      << "after applying loop contracts. Remember to unwind "
                      << "them at least twice to pass unwinding-assertions."
                      << messaget::eom;
      }
      contracts.apply_loop_contracts(to_exclude_from_nondet_static);
    }
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
        std::ofstream of(widen_if_needed(filename));

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
    remove_calls_no_body(goto_model.goto_functions, ui_message_handler);

    goto_model.goto_functions.update();
    goto_model.goto_functions.compute_loop_numbers();
  }

  if(cmdline.isset("constant-propagator"))
  {
    do_indirect_call_and_rtti_removal();
    do_remove_returns();

    log.status() << "Propagating Constants" << messaget::eom;
    log.warning() << "**** WARNING: Constant propagation as performed by "
                     "goto-instrument is not expected to be sound. Do not use "
                     "--constant-propagator if soundness is important for your "
                     "use case."
                  << messaget::eom;

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
  goto_check_c(options, goto_model, ui_message_handler);
  transform_assertions_assumptions(options, goto_model);

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
      safe_string2size_t(cmdline.get_value("stack-depth")),
      ui_message_handler);
  }

  // ignore default/user-specified initialization of variables with static
  // lifetime
  if(cmdline.isset("nondet-static-exclude"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables except for "
                    "the specified ones."
                 << messaget::eom;
    std::set<std::string> to_exclude(
      cmdline.get_values("nondet-static-exclude").begin(),
      cmdline.get_values("nondet-static-exclude").end());
    nondet_static(goto_model, to_exclude);
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
    do_indirect_call_and_rtti_removal();

    log.status() << "Slicing away initializations of unused global variables"
                 << messaget::eom;
    slice_global_inits(goto_model, ui_message_handler);
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
    const namespacet ns(goto_model.symbol_table);
    value_set_analysist value_set_analysis(ns);
    value_set_analysis(goto_model);

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
    {
      reachability_slicer(
        goto_model, cmdline.get_values("property"), ui_message_handler);
    }
    else
      reachability_slicer(goto_model, ui_message_handler);
  }

  if(cmdline.isset("fp-reachability-slice"))
  {
    do_indirect_call_and_rtti_removal();

    log.status() << "Performing a function pointer reachability slice"
                 << messaget::eom;
    function_path_reachability_slicer(
      goto_model,
      cmdline.get_comma_separated_values("fp-reachability-slice"),
      ui_message_handler);
  }

  // full slice?
  if(cmdline.isset("full-slice"))
  {
    do_indirect_call_and_rtti_removal();
    do_remove_returns();
    rewrite_rw_ok(goto_model);

    log.warning() << "**** WARNING: Experimental option --full-slice, "
                  << "analysis results may be unsound. See "
                  << "https://github.com/diffblue/cbmc/issues/260"
                  << messaget::eom;
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
    slice_global_inits(goto_model, ui_message_handler);

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
    {
      reachability_slicer(
        goto_model, cmdline.get_values("property"), ui_message_handler);
    }
    else
      reachability_slicer(goto_model, ui_message_handler);
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
  std::cout << '\n'
            << banner_string("Goto-Instrument", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2008-2013") << '\n'
            << align_center_with_border("Daniel Kroening") << '\n'
            << align_center_with_border("kroening@kroening.com") << '\n';

  // clang-format off
  std::cout << help_formatter(
    "\n"
    "Usage:                     \tPurpose:\n"
    "\n"
    " {bgoto-instrument} [{y-?}] [{y-h}] [{y--help}] \t show this help\n"
    " {bgoto-instrument} {y--version} \t show version and exit\n"
    " {bgoto-instrument} [options] {uin} [{uout}] \t perform analysis or"
    " instrumentation\n"
    "\n"
    "Dump Source:\n"
    HELP_DUMP_C
    " {y--horn} \t print program as constrained horn clauses\n"
    "\n"
    "Diagnosis:\n"
    HELP_SHOW_PROPERTIES
    HELP_DOCUMENT_PROPERTIES
    " {y--show-symbol-table} \t show loaded symbol table\n"
    " {y--list-symbols} \t list symbols with type information\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_GOTO_PROGRAM_STATS
    " {y--show-locations} \t show all source locations\n"
    " {y--dot} \t generate CFG graph in DOT format\n"
    " {y--print-internal-representation} \t show verbose internal"
    " representation of the program\n"
    " {y--list-undefined-functions} \t list functions without body\n"
    " {y--list-calls-args} \t list all function calls with their arguments\n"
    " {y--call-graph} \t show graph of function calls\n"
    " {y--reachable-call-graph} \t show graph of function calls potentially"
    " reachable from main function\n"
    HELP_SHOW_CLASS_HIERARCHY
    HELP_VALIDATE
    " {y--validate-goto-binary} \t check the well-formedness of the passed in"
    " goto binary and then exit\n"
    " {y--interpreter} \t do concrete execution\n"
    "\n"
    "Data-flow analyses:\n"
    " {y--show-struct-alignment} \t show struct members that might be"
    " concurrently accessed\n"
    " {y--show-threaded} \t show instructions that may be executed by more than"
    " one thread\n"
    " {y--show-local-safe-pointers} \t show pointer expressions that are"
    " trivially dominated by a not-null check\n"
    " {y--show-safe-dereferences} \t show pointer expressions that are"
    " trivially dominated by a not-null check *and* used as a dereference"
    " operand\n"
    " {y--show-value-sets} \t show points-to information (using value sets)\n"
    " {y--show-global-may-alias} \t show may-alias information over globals\n"
    " {y--show-local-bitvector-analysis} \t show procedure-local pointer"
    " analysis\n"
    " {y--escape-analysis} \t perform escape analysis\n"
    " {y--show-escape-analysis} \t show results of escape analysis\n"
    " {y--custom-bitvector-analysis} \t perform configurable bitvector"
    " analysis\n"
    " {y--show-custom-bitvector-analysis} \t show results of configurable"
    " bitvector analysis\n"
    " {y--interval-analysis} \t perform interval analysis\n"
    " {y--show-intervals} \t show results of interval analysis\n"
    " {y--show-uninitialized} \t show maybe-uninitialized variables\n"
    " {y--show-points-to} \t show points-to information\n"
    " {y--show-rw-set} \t show read-write sets\n"
    " {y--show-call-sequences} \t show function call sequences\n"
    " {y--show-reaching-definitions} \t show reaching definitions\n"
    " {y--show-dependence-graph} \t show program-dependence graph\n"
    " {y--show-sese-regions} \t show single-entry-single-exit regions\n"
    "\n"
    "Safety checks:\n"
    " {y--no-assertions} \t ignore user assertions\n"
    HELP_GOTO_CHECK
    HELP_UNINITIALIZED_CHECK
    " {y--stack-depth} {un} \t add check that call stack size of non-inlined"
    " functions never exceeds {un}\n"
    " {y--race-check} \t add floating-point data race checks\n"
    "\n"
    "Semantic transformations:\n"
    HELP_NONDET_VOLATILE
    " {y--isr} {ufunction} \t instruments an interrupt service routine\n"
    " {y--mmio} \t instruments memory-mapped I/O\n"
    " {y--nondet-static} \t add nondeterministic initialization of variables"
    " with static lifetime\n"
    " {y--nondet-static-exclude} {ue} \t same as nondet-static except for the"
    " variable {ue} (use multiple times if required)\n"
    " {y--nondet-static-matching} {ur} \t add nondeterministic initialization"
    " of variables with static lifetime matching regex {ur}\n"
    " {y--function-enter} {uf}, {y--function-exit} {uf}, {y--branch} {uf} \t"
    " instruments a call to {uf} at the beginning, the exit, or a branch point,"
    " respectively\n"
    " {y--splice-call} {ucaller},{ucallee} \t prepends a call to {ucallee} in"
    " the body of {ucaller}\n"
    " {y--check-call-sequence} {useq} \t instruments checks to assert that all"
    " call sequences match {useq}\n"
    " {y--undefined-function-is-assume-false} \t convert each call to an"
    " undefined function to assume(false)\n"
    HELP_INSERT_FINAL_ASSERT_FALSE
    HELP_REPLACE_FUNCTION_BODY
    HELP_RESTRICT_FUNCTION_POINTER
    HELP_REMOVE_CALLS_NO_BODY
    " {y--add-library} \t add models of C library functions\n"
    HELP_CONFIG_LIBRARY
    " {y--model-argc-argv} {un} \t model up to {un} command line arguments\n"
    " {y--remove-function-body} {uf} remove the implementation of function {uf}"
    " (may be repeated)\n"
    HELP_REPLACE_CALLS
    HELP_ANSI_C_LANGUAGE
    "\n"
    "Semantics-preserving transformations:\n"
    " {y--ensure-one-backedge-per-target} \t transform loop bodies such that"
    " there is a single edge back to the loop head\n"
    " {y--drop-unused-functions} \t drop functions trivially unreachable from"
    " main function\n"
    HELP_REMOVE_POINTERS
    " {y--constant-propagator} \t propagate constants and simplify"
    " expressions\n"
    " {y--inline} \t perform full inlining\n"
    " {y--partial-inline} \t perform partial inlining\n"
    " {y--function-inline} {ufunction} \t transitively inline all calls"
    " {ufunction} makes\n"
    " {y--no-caching} \t disable caching of intermediate results during"
    " transitive function inlining\n"
    " {y--log} {ufile} \t log in JSON format which code segments were inlined,"
    " use with {y--function-inline}\n"
    " {y--remove-function-pointers} \t replace function pointers by case"
    " statement over function calls\n"
    HELP_REMOVE_CONST_FUNCTION_POINTERS
    " {y--value-set-fi-fp-removal} \t build flow-insensitive value set and"
    " replace function pointers by a case statement over the possible"
    " assignments. If the set of possible assignments is empty the function"
    " pointer is removed using the standard remove-function-pointers pass.\n"
    "\n"
    "Loop information and transformations:\n"
    HELP_UNWINDSET
    " {y--unwindset-file_<file>} \t read unwindset from file\n"
    " {y--partial-loops} \t permit paths with partial loops\n"
    " {y--unwinding-assertions} \t generate unwinding assertions\n"
    " {y--continue-as-loops} \t add loop for remaining iterations after"
    " unwound part\n"
    " {y--k-induction} {uk} \t check loops with k-induction\n"
    " {y--step-case} \t k-induction: do step-case\n"
    " {y--base-case} \t k-induction: do base-case\n"
    " {y--havoc-loops} \t over-approximate all loops\n"
    " {y--accelerate} \t add loop accelerators\n"
    " {y--z3} \t use Z3 when computing loop accelerators\n"
    " {y--skip-loops {uloop-ids} \t add gotos to skip selected loops during"
    " execution\n"
    " {y--show-lexical-loops} \t show single-entry-single-back-edge loops\n"
    " {y--show-natural-loops} \t show natural loop heads\n"
    "\n"
    "Memory model instrumentations:\n"
    HELP_WMM_FULL
    "\n"
    "Slicing:\n"
    HELP_REACHABILITY_SLICER
    HELP_FP_REACHABILITY_SLICER
    " {y--full-slice} \t slice away instructions that don't affect assertions\n"
    " {y--property} {uid} \t slice with respect to specific property only\n"
    " {y--slice-global-inits} \t slice away initializations of unused global"
    " variables\n"
    " {y--aggressive-slice} \t remove bodies of any functions not on the"
    " shortest path between the start function and the function containing the"
    " property/properties\n"
    " {y--aggressive-slice-call-depth} {un} \t used with aggressive-slice,"
    " preserves all functions within {un} function calls of the functions on"
    " the shortest path\n"
    " {y--aggressive-slice-preserve-function} {uf} \t force the aggressive"
    " slicer to preserve function {uf}\n"
    " {y--aggressive-slice-preserve-functions-containing} {uf} \t force the"
    " aggressive slicer to preserve all functions with names containing {uf}\n"
    " {y--aggressive-slice-preserve-all-direct-paths} \t force aggressive"
    " slicer to preserve all direct paths\n"
    "\n"
    "Code contracts:\n"
    HELP_DFCC
    HELP_LOOP_CONTRACTS
    HELP_LOOP_CONTRACTS_NO_UNWIND
    HELP_LOOP_CONTRACTS_FILE
    HELP_REPLACE_CALL
    HELP_ENFORCE_CONTRACT
    HELP_ENFORCE_CONTRACT_REC
    "\n"
    "User-interface options:\n"
    HELP_FLUSH
    " {y--xml} \t output files in XML where supported\n"
    " {y--xml-ui} \t use XML-formatted output\n"
    " {y--json-ui} \t use JSON-formatted output\n"
    " {y--verbosity} {u#} \t verbosity level\n"
    HELP_TIMESTAMP
    "\n");
  // clang-format on
}
