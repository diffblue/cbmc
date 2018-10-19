/*******************************************************************\

Module: Dispatch Loop Detector Tests

Author: Kareem Khazem <karkhaz@karkhaz.com>, 2018

\*******************************************************************/

#include "dispatch_loop_detector.h"

#include <ansi-c/ansi_c_language.h>

#include <cbmc/cbmc_parse_options.h>

#include <langapi/language_ui.h>
#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/tempfile.h>

#include <algorithm>
#include <sstream>

#define TEST_NAME(t) t, #t

SCENARIO("dispatch loop detector")
{
  // The included files are long C programs wrapped in a string literal.
  // There's a bit of duplication of information here, because the C++ standard
  // doesn't let me generate an #include directive from a preprocessor macro...
  const std::string basic_case =
#include "basic_case.c.string"
    ;
  check(
    TEST_NAME(basic_case),
    {
      {dispatch_loop_is_on_line, {93}},
      {cases_are_on_lines, {97, 100, 103}},
      {instruction_after_loop_is, {END_FUNCTION}},
    });

  const std::string basic_if =
#include "basic_if.c.string"
    ;
  check(
    TEST_NAME(basic_if),
    {
      {dispatch_loop_is_on_line, {93}},
      {cases_are_on_lines, {97, 99, /* 101 */}},
      {instruction_after_loop_is, {END_FUNCTION}},
    });

  const std::string if_with_blocks =
#include "if_with_blocks.c.string"
    ;
  check(
    TEST_NAME(if_with_blocks),
    {
      {dispatch_loop_is_on_line, {93}},
      {cases_are_on_lines, {97, 101, /* 105 */}},
      {instruction_after_loop_is, {END_FUNCTION}},
    });

  const std::string branches_call_into_common =
#include "branches_call_into_common.c.string"
    ;
  check(
    TEST_NAME(branches_call_into_common),
    {
      {dispatch_loop_is_on_line, {125}},
      {cases_are_on_lines, {129, 134, 139}},
      {instruction_after_loop_is, {END_FUNCTION}},
    });

  const std::string do_while_case =
#include "do_while_case.c.string"
    ;
  check(
    TEST_NAME(do_while_case),
    {
      {cases_are_on_lines, {99, 102, 105}},

      // Because of the do-while, the "head" of the loop is actually the
      // instruction after the do. The do doesn't get translated into a proper
      // goto instruction.
      {dispatch_loop_is_on_line, {97}},

      // Dead the declaration of the Colour `c`.
      {instruction_after_loop_is, {DEAD}},
    });

  const std::string if_with_before =
#include "if_with_before.c.string"
    ;
  check(
    TEST_NAME(if_with_before),
    {
      {cases_are_on_lines, {99, 103, /* 107 */}},
      {dispatch_loop_is_on_line, {95}},

      // Dead the declaration of int x.
      {instruction_after_loop_is, {DEAD}},
    });

  const std::string if_with_after =
#include "if_with_after.c.string"
    ;
  check(
    TEST_NAME(if_with_after),
    {
      {cases_are_on_lines, {96, 100, /* 104 */}},
      {dispatch_loop_is_on_line, {93}},

      // No declarations before the loop, so no DEADs. But there is a
      // declaration immediately after the loop
      {instruction_after_loop_is, {DECL}},
      {c_instruction_after_loop_is_on_line, {110}},
    });

  const std::string if_inside_case =
#include "if_inside_case.c.string"
    ;
  check(
    TEST_NAME(if_inside_case),
    {
      {cases_are_on_lines, {98, 104, 108}},
      {dispatch_loop_is_on_line, {94}},
    });

  const std::string depth_3_distance_2 =
#include "depth_3_distance_2.c.string"
    ;
  check(
    depth_3_distance_2,
    "depth-3_distance_2.c with depth 2, distance 2",
    {/* No dispatch loop found */},
    [](optionst &opts) {
      opts.set_option("dispatch-function-search-depth", 2);
      opts.set_option("dispatch-loop-decision-distance", 2);
    });
  check(
    depth_3_distance_2,
    "depth-3_distance_2.c with depth 3, distance 2",
    {{cases_are_on_lines, {95, 98, 101}}, {dispatch_loop_is_on_line, {109}}},
    [](optionst &opts) {
      opts.set_option("dispatch-function-search-depth", 3);
      opts.set_option("dispatch-loop-decision-distance", 2);
    });

  const std::string depth_3_distance_3 =
#include "depth_3_distance_3.c.string"
    ;
  check(
    depth_3_distance_3,
    "depth-3_distance_3.c with depth 3, distance 2",
    {/* No dispatch loop found */},
    [](optionst &opts) {
      opts.set_option("dispatch-function-search-depth", 3);
      opts.set_option("dispatch-loop-decision-distance", 2);
    });
  check(
    depth_3_distance_3,
    "depth-3_distance_3.c with depth 2, distance 3",
    {/* No dispatch loop found */},
    [](optionst &opts) {
      opts.set_option("dispatch-function-search-depth", 2);
      opts.set_option("dispatch-loop-decision-distance", 3);
    });
  check(
    depth_3_distance_3,
    "depth-3_distance_3.c with depth 3, distance 3",
    {{cases_are_on_lines, {95, 98, 101}}, {dispatch_loop_is_on_line, {110}}},
    [](optionst &opts) {
      opts.set_option("dispatch-function-search-depth", 3);
      opts.set_option("dispatch-loop-decision-distance", 3);
    });
}

// In theory, there should be no need to change the code below when adding new
// test cases...

void c_instruction_after_loop_is_on_line(
  const dispatch_loop_detectort::dispatch_loopt &loop,
  const std::list<std::size_t> &expected)
{
  INVARIANT(
    expected.size() == 1,
    "c_instruction_after_loop_is_on_line() expects a singleton set containing "
    "the expected line number of the dispatch loop");

  const std::set<goto_program_instruction_typet> to_skip = {
    NO_INSTRUCTION_TYPE, OTHER, SKIP, LOCATION, DEAD};
  goto_programt::const_targett tmp = loop.subsequent_instruction();
  REQUIRE(tmp->type != END_FUNCTION);
  while(to_skip.find(tmp->type) != to_skip.end())
  {
    ++tmp;
    REQUIRE(tmp->type != END_FUNCTION);
  }

  INFO(
    "We think the C language instruction after the dispatch loop is:"
    "\n<code>\n"
    << tmp->code.pretty() << "\n<guard>\n"
    << tmp->guard.pretty());

  const source_locationt &loc = tmp->code.source_location().is_not_nil()
                                  ? tmp->code.source_location()
                                  : tmp->source_location;
  REQUIRE(loc.is_not_nil());
  REQUIRE(std::stol(loc.get_line().c_str()) == expected.front());
}

void instruction_after_loop_is(
  const dispatch_loop_detectort::dispatch_loopt &loop,
  const std::list<std::size_t> &expected)
{
  INVARIANT(
    expected.size() == 1,
    "instruction_after_loop_is() expects a singleton set containing the "
    "expected line number of the dispatch loop");

  INFO(
    "We think the instruction after the dispatch loop is:\n<code>\n"
    << loop.subsequent_instruction()->code.pretty() << "\n<guard>\n"
    << loop.subsequent_instruction()->guard.pretty());

  REQUIRE(expected.front() == loop.subsequent_instruction()->type);
}

void dispatch_loop_is_on_line(
  const dispatch_loop_detectort::dispatch_loopt &loop,
  const std::list<std::size_t> &expected)
{
  INVARIANT(
    expected.size() == 1,
    "dispatch_loop_is_on_line() expects a singleton set containing the "
    "expected line number of the dispatch loop");

  INFO(
    "We think dispatch loop is:\n<code>\n"
    << loop.first_instruction()->code.pretty() << "\n<guard>\n"
    << loop.first_instruction()->guard.pretty())
  const source_locationt &loc =
    loop.first_instruction()->code.source_location().is_not_nil()
      ? loop.first_instruction()->code.source_location()
      : loop.first_instruction()->source_location;
  REQUIRE(loc.is_not_nil());
  REQUIRE(std::stol(loc.get_line().c_str()) == expected.front());
}

void cases_are_on_lines(
  const dispatch_loop_detectort::dispatch_loopt &loop,
  const std::list<std::size_t> &expected_lines)
{
  std::list<std::size_t> lines_in_cases;
  for(const auto &ins : loop.cases())
  {
    const source_locationt &loc = ins->code.source_location().is_not_nil()
                                    ? ins->code.source_location()
                                    : ins->source_location;
    REQUIRE(loc.is_not_nil());
    lines_in_cases.push_back(std::stol(loc.get_line().c_str()));
  }

  std::list<std::size_t> sorted_expected(expected_lines);
  sorted_expected.sort();
  lines_in_cases.sort();

  check_not_superset(
    sorted_expected, lines_in_cases, "Expected (but did not find)");
  check_not_superset(
    lines_in_cases, sorted_expected, "Found (but did not expect)");
}

void check_not_superset(
  const std::list<std::size_t> &list1,
  const std::list<std::size_t> &list2,
  const std::string &message_prefix)
{
  std::vector<std::size_t> diff;
  std::set_difference(
    list1.begin(),
    list1.end(),
    list2.begin(),
    list2.end(),
    std::inserter(diff, diff.begin()));
  std::stringstream ss;
  for(const auto &line : diff)
    ss << line << ", ";
  INFO(
    message_prefix << " the following lines to be cases of the dispatch loop: "
                   << ss.str());
  REQUIRE(diff.empty());
}

void _check(
  const std::string &program,
  const std::forward_list<
    std::pair<structure_predicatet, std::list<std::size_t>>>
    &loop_structure_checks,
  const std::function<void(optionst &)> opts_callback)
{
  temporary_filet tmp("dispatch-loop_", ".c");
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
  opts_callback(opts);
  std::stringstream ss;
  ss << "Options:\n---\n";
  opts.output(ss);
  ss << "\n---\n";
  INFO(ss.str());

  ui_message_handlert mh(cmdline, "dispatch-loop");
  mh.set_verbosity(5);
  messaget log(mh);

  goto_modelt gm;
  int ret;
  ret = cbmc_parse_optionst::get_goto_program(gm, opts, cmdline, log, mh);
  REQUIRE(ret == -1);

  dispatch_loop_detectort det(gm.goto_functions, opts, log);
  bool failed_to_find_loops = det.detect_dispatch_loops();

  if(failed_to_find_loops)
  {
    REQUIRE(loop_structure_checks.empty());
  }
  else
  {
    REQUIRE(!loop_structure_checks.empty());
    dispatch_loop_detectort::dispatch_loopt s(det);
    for(const auto &pair : loop_structure_checks)
      pair.first(s, pair.second);
  }
}
