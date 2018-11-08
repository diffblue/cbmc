/// \file Test for the dispatch loop detector
///
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_UNIT_DISPATCH_LOOP_DETECTOR_H
#define CPROVER_UNIT_DISPATCH_LOOP_DETECTOR_H

#include <goto-instrument/dispatch_loop_detector.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/safety_checker.h>

#include <testing-utils/catch.hpp>

#include <functional>

typedef std::function<void(
  const dispatch_loop_detectort::dispatch_loopt &,
  const std::list<std::size_t> &)>
  structure_predicatet;

void _check(
  const std::string &program,
  const std::forward_list<
    std::pair<structure_predicatet, std::list<std::size_t>>> &,
  const std::function<void(optionst &)>);

/// Call this one, not the underscore version
void check(
  const std::string &program,
  const std::string &test_name,
  const std::forward_list<
    std::pair<structure_predicatet, std::list<std::size_t>>>
    &loop_structure_checks,
  const std::function<void(optionst &)> opts_callback = [](optionst &o) {})
{
  WHEN("Testing program 'dispatch-loop-detector/" + test_name + ".c'")
  _check(program, loop_structure_checks, opts_callback);
}

/// This predicate is over the actual instruction after the loop, i.e.
/// loop.subsequent_instruction(). This will typically be END_FUNCTION or
/// DEAD. It won't be SKIP, because we skip over those.
///
/// The list argument needs to be a singleton, containing one of the
/// std::size_t values above for readability.
void instruction_after_loop_is(
  const dispatch_loop_detectort::dispatch_loopt &,
  const std::list<std::size_t> &);

/// This predicate tries to find the instruction that corresponds to a real C
/// program statement, so not DEAD or END_FUNCTION, but things like DECL etc.
/// If there is no such statement in the C language test case, don't test with
/// this predicate.
void c_instruction_after_loop_is_on_line(
  const dispatch_loop_detectort::dispatch_loopt &,
  const std::list<std::size_t> &);

/// The list needs to be a singleton, containing the line number of the first
/// instruction in the dispatch loop.
void dispatch_loop_is_on_line(
  const dispatch_loop_detectort::dispatch_loopt &,
  const std::list<std::size_t> &);

void cases_are_on_lines(
  const dispatch_loop_detectort::dispatch_loopt &,
  const std::list<std::size_t> &);

void check_not_superset(
  const std::list<std::size_t> &,
  const std::list<std::size_t> &,
  const std::string &);

#endif // CPROVER_UNIT_DISPATCH_LOOP_DETECTOR_H
