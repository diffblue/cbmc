/*******************************************************************\

Module: Path Strategy Tests

Author: Kareem Khazem <karkhaz@karkhaz.com>, 2018

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <path_strategies.h>

#include <fstream>
#include <functional>
#include <string>

#include <ansi-c/ansi_c_language.h>

#include <cbmc/bmc.h>
#include <cbmc/cbmc_parse_options.h>

#include <goto-checker/solver_factory.h>

#include <langapi/language_ui.h>
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
// result. Results are either SUCCESS, meaning that verification of that path
// succeeded, or FAILURE, meaning that there was an assertion failure on that
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
      {symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
       symex_eventt::resume(symex_eventt::enumt::NEXT, 5),
       symex_eventt::result(symex_eventt::enumt::SUCCESS)});
    check_with_strategy(
      "fifo",
      opts_callback,
      c,
      {symex_eventt::resume(symex_eventt::enumt::NEXT, 5),
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
      {// Outer else, inner else
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
      {// Expand outer if, but don't continue depth-first
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
      "/*  4 */     " CPROVER_PREFIX
      "assume(x == 1); \n"
      "/*  5 */                                       \n"
      "/*  6 */     while(x)                          \n"
      "/*  7 */       --x;                            \n"
      "/*  8 */                                       \n"
      "/*  9 */     assert(x);                        \n"
      "/* 10 */   }                                   \n";
    // clang-format on

    check_with_strategy(
      "lifo",
      opts_callback,
      c,
      {
        // The path where we skip the loop body. Successful because the path is
        // implausible, we cannot have skipped the body if x == 1.
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::SUCCESS),

        // Enter the loop body once. Since we decrement x, the assertion should
        // fail.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::FAILURE),

        // The path where we enter the loop body twice. Successful because
        // infeasible.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
        symex_eventt::result(symex_eventt::enumt::SUCCESS),

        // Overall we fail.
        symex_eventt::result(symex_eventt::enumt::FAILURE),
      });

    check_with_strategy(
      "fifo",
      opts_callback,
      c,
      {
        // The path where we skip the loop body. Successful because the path is
        // implausible, we cannot have skipped the body if x == 1.
        //
        // In this case, although we resume from line 7, we don't proceed until
        // the end of the path after executing line 7.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
        symex_eventt::resume(symex_eventt::enumt::JUMP, 9),
        symex_eventt::result(symex_eventt::enumt::SUCCESS),

        // Pop line 7 that we saved from above, and execute the loop a second
        // time. Successful, since this path is infeasible.
        symex_eventt::resume(symex_eventt::enumt::NEXT, 7),
        symex_eventt::result(symex_eventt::enumt::SUCCESS),

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
        {symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
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
        {symex_eventt::resume(symex_eventt::enumt::JUMP, 7),
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
  const safety_checkert::resultt result,
  std::size_t &counter)
{
  INFO(
    "Expecting result to be '"
    << (result == safety_checkert::resultt::SAFE ? "success" : "failure")
    << "' (item at index [" << counter << "] in expected results list");
  ++counter;

  REQUIRE(result != safety_checkert::resultt::ERROR);

  if(result == safety_checkert::resultt::SAFE)
  {
    REQUIRE(!events.empty());
    REQUIRE(events.front().first == symex_eventt::enumt::SUCCESS);
    events.pop_front();
  }
  else if(result == safety_checkert::resultt::UNSAFE)
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

  int dst = std::stoi(state.saved_target->source_location.get_line().c_str());

  if(state.has_saved_jump_target)
  {
    INFO(
      "Expecting resume to be 'jump' to line "
      << dst << " (item at index [" << counter
      << "] in expected resumes list)");
    REQUIRE(events.front().first == symex_eventt::enumt::JUMP);
  }
  else if(state.has_saved_next_instruction)
  {
    INFO(
      "Expecting resume to be 'next' to line "
      << dst << " (item at index [" << counter
      << "] in expected resumes list)");
    REQUIRE(events.front().first == symex_eventt::enumt::NEXT);
  }
  else
    REQUIRE(false);

  ++counter;
  REQUIRE(events.front().second == dst);

  events.pop_front();
}

// This is a simplified version of bmct::do_language_agnostic_bmc, without all
// the edge cases to deal with java programs, bytecode loaded on demand, etc. We
// need to replicate some of this stuff because the worklist is a local variable
// of do_language_agnostic_bmc, and we need to check the worklist every time
// symex returns.
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
  config.main = "main";
  config.set(cmdline);

  optionst opts;
  cbmc_parse_optionst::set_default_options(opts);
  opts.set_option("paths", true);
  opts.set_option("exploration-strategy", strategy);

  opts_callback(opts);

  ui_message_handlert mh(cmdline, "path-explore");
  mh.set_verbosity(0);
  messaget log(mh);

  path_strategy_choosert chooser;
  REQUIRE(chooser.is_valid_strategy(strategy));
  std::unique_ptr<path_storaget> worklist = chooser.get(strategy);

  goto_modelt gm;
  int ret;
  ret = cbmc_parse_optionst::get_goto_program(gm, opts, cmdline, log, mh);
  REQUIRE(ret == -1);

  solver_factoryt solvers(opts, gm.get_symbol_table(), mh, false);
  std::unique_ptr<solver_factoryt::solvert> cbmc_solver = solvers.get_solver();
  prop_convt &initial_pc = cbmc_solver->prop_conv();
  std::function<bool(void)> callback = []() { return false; };

  safety_checkert::resultt overall_result = safety_checkert::resultt::SAFE;
  std::size_t expected_results_cnt = 0;

  bmct bmc(opts, gm.get_symbol_table(), mh, initial_pc, *worklist, callback);
  safety_checkert::resultt tmp_result = bmc.run(gm);

  if(tmp_result != safety_checkert::resultt::PAUSED)
  {
    symex_eventt::validate_result(events, tmp_result, expected_results_cnt);
    overall_result &= tmp_result;
  }

  if(
    overall_result == safety_checkert::resultt::UNSAFE &&
    opts.get_bool_option("stop-on-fail") && opts.is_set("paths"))
  {
    worklist->clear();
  }

  while(!worklist->empty())
  {
    solver_factoryt solvers(opts, gm.get_symbol_table(), mh, false);
    cbmc_solver = solvers.get_solver();
    prop_convt &pc = cbmc_solver->prop_conv();
    path_storaget::patht &resume = worklist->peek();

    symex_eventt::validate_resume(events, resume.state, expected_results_cnt);

    path_explorert pe(
      opts,
      gm.get_symbol_table(),
      mh,
      pc,
      resume.equation,
      resume.state,
      *worklist,
      callback);
    tmp_result = pe.run(gm);

    if(tmp_result != safety_checkert::resultt::PAUSED)
    {
      symex_eventt::validate_result(events, tmp_result, expected_results_cnt);
      overall_result &= tmp_result;
    }
    worklist->pop();

    if(
      overall_result == safety_checkert::resultt::UNSAFE &&
      opts.get_bool_option("stop-on-fail"))
    {
      worklist->clear();
    }
  }

  symex_eventt::validate_result(events, overall_result, expected_results_cnt);

  INFO("The expected results list contains " << events.size() << " items");
  REQUIRE(events.empty());
}
