/*******************************************************************\

Module: Path Strategy Tests

Author: Kareem Khazem <karkhaz@karkhaz.com>, 2018

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <path_strategies.h>

#include <fstream>
#include <functional>
#include <string>

#include <ansi-c/ansi_c_language.h>

#include <cbmc/cbmc_parse_options.h>

#include <goto-checker/bmc_util.h>
#include <goto-checker/goto_symex_property_decider.h>
#include <goto-checker/symex_bmc.h>

#include <goto-symex/path_storage.h>

#include <goto-instrument/unwindset.h>

#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/tempfile.h>

// The actual test suite.
//
// Whenever you add a new path exploration strategy 'my-cool-strategy', for each
// of the test programs (under the GIVEN macros), add a new test using a call to
// `check_with_strategy("my-cool-strategy", c, event_list)` where `event_list`
// is a list of the events that you expect to see during symbolic execution.
// Events are either resumes or results.
//
// Whenever symbolic execution pauses and picks a path to resume from, you
// should note the line number of the path you expect that path strategy to
// resume from. A resume is either a JUMP, meaning that it's the target of a
// `goto` instruction, or a NEXT, meaning that it's the instruction following a
// `goto` instruction.
//
// Whenever symbolic execution reaches the end of a path, you should expect a
// result. Results are either DONE, meaning that verification of that path
// succeeded, or FOUND_FAIL, meaning that there was an assertion failure on that
// path.
//
// To figure out what the events should be, run CBMC on the test program with
// your strategy with `--verbosity 10` and look out for lines like
//
//  Resuming from jump target 'file nested-if/main.c line 13 function main'
//
//  Resuming from next instruction 'file nested-if/main.c line 14 function main'
//
//  VERIFICATION SUCCESSFUL
//
//  VERIFICATION FAILED
//
// And note the order in which they occur.

SCENARIO("path strategies")
{
  std::string c;
  GIVEN("a simple conditional program")
  {
    std::function<void(optionst &)> opts_callback = [](optionst &) {};

    c =
      "/*  1 */  int main()      \n"
      "/*  2 */  {               \n"
      "/*  3 */    int x;        \n"
      "/*  4 */    if(x)         \n"
      "/*  5 */      x = 1;      \n"
      "/*  6 */    else          \n"
      "/*  7 */      x = 0;      \n"
      "/*  8 */  }               \n";

    check_with_strategy(
      "lifo",
      opts_callback,
      c,
      {// Entry state is line 0
       symex_eventt::resume(symex_eventt::enumt::NEXT, 0),
       symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
       symex_eventt::resume(symex_eventt::enumt::NEXT, 5),
       symex_eventt::result(symex_eventt::enumt::SUCCESS)});
    check_with_strategy(
      "fifo",
      opts_callback,
      c,
      {// Entry state is line 0
       symex_eventt::resume(symex_eventt::enumt::NEXT, 0),
       symex_eventt::resume(symex_eventt::enumt::NEXT, 5),
       symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
       symex_eventt::result(symex_eventt::enumt::SUCCESS)});
  }

  GIVEN("a program with nested conditionals")
  {
    std::function<void(optionst &)> opts_callback = [](optionst &) {};

    c =
      "/*  1 */  int main()            \n"
      "/*  2 */  {                     \n"
      "/*  3 */    int x, y;           \n"
      "/*  4 */    if(x)               \n"
      "/*  5 */    {                   \n"
      "/*  6 */      if(y)             \n"
      "/*  7 */        y = 1;          \n"
      "/*  8 */      else              \n"
      "/*  9 */        y = 0;          \n"
      "/* 10 */    }                   \n"
      "/* 11 */    else                \n"
      "/* 12 */    {                   \n"
      "/* 13 */      if(y)             \n"
      "/* 14 */        y = 1;          \n"
      "/* 15 */      else              \n"
      "/* 16 */        y = 0;          \n"
      "/* 17 */    }                   \n"
      "/* 18 */  }                     \n";

    check_with_strategy(
      "lifo",
      opts_callback,
      c,
      {// Entry state is line 0
       symex_eventt::resume(symex_eventt::enumt::NEXT, 0),
       // Outer else, inner else
       symex_eventt::resume(symex_eventt::enumt::JUMP, 13),
       symex_eventt::resume(symex_eventt::enumt::JUMP, 16),
       // Outer else, inner if
       symex_eventt::resume(symex_eventt::enumt::NEXT, 14),
       // Outer if, inner else
       symex_eventt::resume(symex_eventt::enumt::NEXT, 6),
       symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
       // Outer if, inner if
       symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
       symex_eventt::result(symex_eventt::enumt::SUCCESS)});

    check_with_strategy(
      "fifo",
      opts_callback,
      c,
      {// Entry state is line 0
       symex_eventt::resume(symex_eventt::enumt::NEXT, 0),
       // Expand outer if, but don't continue depth-first
       symex_eventt::resume(symex_eventt::enumt::NEXT, 6),
       // Jump to outer else, but again don't continue depth-first
       symex_eventt::resume(symex_eventt::enumt::JUMP, 13),
       // Expand inner if of the outer if
       symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
       // No more branch points, so complete the path. Then continue BFSing
       symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
       symex_eventt::resume(symex_eventt::enumt::NEXT, 14),
       symex_eventt::resume(symex_eventt::enumt::JUMP, 16),
       symex_eventt::result(symex_eventt::enumt::SUCCESS)});
  }

  GIVEN("a loop program to test functional correctness")
  {
    std::function<void(optionst &)> opts_callback = [](optionst &opts) {
      opts.set_option("unwind", 2U);
    };

    // clang-format off
    c =
      "/*  1 */   int main()                          \n"
      "/*  2 */   {                                   \n"
      "/*  3 */     int x;                            \n"
      "/*  4 */     if(x == 1) {                      \n"
      "/*  5 */                                       \n"
      "/*  6 */       while(x)                        \n"
      "/*  7 */         --x;                          \n"
      "/*  8 */                                       \n"
      "/*  9 */       assert(x);                      \n"
      "/* 10 */     }                                 \n"
      "/* 11 */   }                                   \n";
    // clang-format on

    check_with_strategy(
      "lifo",
      opts_callback,
      c,
      {
        // Entry state is line 0
        symex_eventt::resume(symex_eventt::enumt::NEXT, 0),

        // The path where x != 1 and we have nothing to check:
        symex_eventt::resume(symex_eventt::enumt::JUMP, 11),

        // The path where we skip the loop body. Successful because the path is
        // implausible, we cannot have skipped the body if x == 1.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 6),
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::SUCCESS),

        // Enter the loop body once. Since we decrement x, the assertion should
        // fail.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::FAILURE),

        // The path where we enter the loop body twice. No result because
        // this path hits an unwind bound.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),

        // Overall we fail.
        symex_eventt::result(symex_eventt::enumt::FAILURE),
      });

    check_with_strategy(
      "fifo",
      opts_callback,
      c,
      {
        // Entry state is line 0
        symex_eventt::resume(symex_eventt::enumt::NEXT, 0),

        // First the path where we enter the if-block at line 4 then on hitting
        // the branch at line 6 consider skipping straight to the end, but find
        // nothing there to investigate:
        symex_eventt::resume(symex_eventt::enumt::NEXT, 6),
        symex_eventt::resume(symex_eventt::enumt::JUMP, 11),

        // The path where we skip the loop body. Successful because the path is
        // implausible, we cannot have skipped the body if x == 1.
        //
        // In this case, although we resume from line 7, we don't proceed until
        // the end of the path after executing line 7.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::SUCCESS),

        // Pop line 7 that we saved from above, and execute the loop a second
        // time. No result, since this path exceeds an unwind bound
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),

        // Pop line 7 that we saved from above and bail out. That corresponds to
        // executing the loop once, decrementing x to 0; assert(x) should fail.
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::FAILURE),

        // Overall we fail.
        symex_eventt::result(symex_eventt::enumt::FAILURE),
      });
  }

  GIVEN("program to check for stop-on-fail with path exploration")
  {
    std::function<void(optionst &)> halt_callback = [](optionst &opts) {
      opts.set_option("stop-on-fail", true);
    };
    std::function<void(optionst &)> no_halt_callback = [](optionst &) {};

    c =
      "/*  1 */  int main()      \n"
      "/*  2 */  {               \n"
      "/*  3 */    int x, y;     \n"
      "/*  4 */    if(x)         \n"
      "/*  5 */      assert(0);  \n"
      "/*  6 */    else          \n"
      "/*  7 */      assert(0);  \n"
      "/*  8 */  }               \n";

    GIVEN("no stopping on failure")
    {
      check_with_strategy(
        "lifo",
        no_halt_callback,
        c,
        {// Entry state is line 0
         symex_eventt::resume(symex_eventt::enumt::NEXT, 0),
         symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
         symex_eventt::result(symex_eventt::enumt::FAILURE),
         symex_eventt::resume(symex_eventt::enumt::NEXT, 5),
         symex_eventt::result(symex_eventt::enumt::FAILURE),
         // Overall result
         symex_eventt::result(symex_eventt::enumt::FAILURE)});
    }
    GIVEN("stopping on failure")
    {
      check_with_strategy(
        "lifo",
        halt_callback,
        c,
        {// Entry state is line 0
         symex_eventt::resume(symex_eventt::enumt::NEXT, 0),
         symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
         symex_eventt::result(symex_eventt::enumt::FAILURE),
         // Overall result
         symex_eventt::result(symex_eventt::enumt::FAILURE)});
    }
  }
}

// In theory, there should be no need to change the code below when adding new
// test cases...

void symex_eventt::validate_result(
  listt &events,
  const incremental_goto_checkert::resultt::progresst result,
  std::size_t &counter)
{
  INFO(
    "Expecting result to be '"
    << (result == incremental_goto_checkert::resultt::progresst::DONE
          ? "success"
          : "failure")
    << "' (item at index [" << counter << "] in expected results list");
  ++counter;

  if(result == incremental_goto_checkert::resultt::progresst::DONE)
  {
    REQUIRE(!events.empty());
    REQUIRE(events.front().first == symex_eventt::enumt::SUCCESS);
    events.pop_front();
  }
  else
  {
    REQUIRE(!events.empty());
    REQUIRE(events.front().first == symex_eventt::enumt::FAILURE);
    events.pop_front();
  }
}

void symex_eventt::validate_resume(
  listt &events,
  const goto_symex_statet &state,
  std::size_t &counter)
{
  REQUIRE(!events.empty());

  int dst = 0;
  if(!state.saved_target->source_location().get_line().empty())
    dst = std::stoi(state.saved_target->source_location().get_line().c_str());

  if(state.has_saved_next_instruction)
  {
    INFO(
      "Expecting resume to be 'next' to line "
      << dst << " (item at index [" << counter
      << "] in expected resumes list)");
    REQUIRE(events.front().first == symex_eventt::enumt::NEXT);
  }
  else if(state.has_saved_jump_target)
  {
    INFO(
      "Expecting resume to be 'jump' to line "
      << dst << " (item at index [" << counter
      << "] in expected resumes list)");
    REQUIRE(events.front().first == symex_eventt::enumt::JUMP);
  }
  else
    REQUIRE(false);

  ++counter;
  REQUIRE(events.front().second == dst);

  events.pop_front();
}

// This is a simplified copy of single_path_symex_checkert
// because we have to check the worklist every time goto-symex returns.
void _check_with_strategy(
  const std::string &strategy,
  const std::string &program,
  std::function<void(optionst &)> opts_callback,
  symex_eventt::listt &events)
{
  temporary_filet tmp("path-explore_", ".c");
  std::ofstream of(tmp().c_str());
  REQUIRE(of.is_open());

  of << program << std::endl;
  of.close();

  register_language(new_ansi_c_language);
  cmdlinet cmdline;
  cmdline.args.push_back(tmp());
  config.main = std::string("main");
  config.set(cmdline);

  optionst options;
  cbmc_parse_optionst::set_default_options(options);
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("paths", true);
  options.set_option("exploration-strategy", strategy);
  REQUIRE(is_valid_path_strategy(strategy));
  opts_callback(options);

  ui_message_handlert ui_message_handler(cmdline, "path-explore");
  ui_message_handler.set_verbosity(0);
  messaget log(ui_message_handler);

  goto_modelt goto_model;
  int ret;
  ret = cbmc_parse_optionst::get_goto_program(
    goto_model, options, cmdline, ui_message_handler);
  REQUIRE(ret == -1);

  symbol_tablet symex_symbol_table;
  namespacet ns(goto_model.get_symbol_table(), symex_symbol_table);
  propertiest properties(initialize_properties(goto_model));
  std::unique_ptr<path_storaget> worklist = get_path_strategy(strategy);
  guard_managert guard_manager;
  unwindsett unwindset{goto_model};

  {
    // Put initial state into the work list
    symex_target_equationt equation(ui_message_handler);
    symex_bmct symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      equation,
      options,
      *worklist,
      guard_manager,
      unwindset);
    setup_symex(symex, ns, options, ui_message_handler);

    symex.initialize_path_storage_from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);
  }

  std::size_t expected_results_cnt = 0;
  while(!worklist->empty())
  {
    path_storaget::patht &resume = worklist->peek();

    symex_eventt::validate_resume(events, resume.state, expected_results_cnt);

    symex_bmct symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      resume.equation,
      options,
      *worklist,
      guard_manager,
      unwindset);
    setup_symex(symex, ns, options, ui_message_handler);

    symex.resume_symex_from_saved_state(
      goto_symext::get_goto_function(goto_model),
      resume.state,
      &resume.equation,
      symex_symbol_table);
    postprocess_equation(
      symex, resume.equation, options, ns, ui_message_handler);

    incremental_goto_checkert::resultt result(
      incremental_goto_checkert::resultt::progresst::DONE);

    if(symex.get_remaining_vccs() > 0)
    {
      update_properties_status_from_symex_target_equation(
        properties, result.updated_properties, resume.equation);

      goto_symex_property_decidert property_decider(
        options, ui_message_handler, resume.equation, ns);

      const auto solver_runtime = prepare_property_decider(
        properties, resume.equation, property_decider, ui_message_handler);

      run_property_decider(
        result,
        properties,
        property_decider,
        ui_message_handler,
        solver_runtime,
        false);

      symex_eventt::validate_result(
        events, result.progress, expected_results_cnt);
    }

    worklist->pop();

    if(
      result.progress ==
        incremental_goto_checkert::resultt::progresst::FOUND_FAIL &&
      options.get_bool_option("stop-on-fail"))
    {
      worklist->clear();
    }

    if(worklist->empty())
    {
      update_status_of_not_checked_properties(
        properties, result.updated_properties);

      update_status_of_unknown_properties(
        properties, result.updated_properties);
    }
  }

  const resultt overall_result = determine_result(properties);
  symex_eventt::validate_result(
    events,
    overall_result == resultt::FAIL
      ? incremental_goto_checkert::resultt::progresst::FOUND_FAIL
      : incremental_goto_checkert::resultt::progresst::DONE,
    expected_results_cnt);

  INFO("The expected results list contains " << events.size() << " items");
  REQUIRE(events.empty());
}
