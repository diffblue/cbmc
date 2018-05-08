/// \file Test for path strategies set through `cbmc --paths ...`
///
/// \author Kareem Khazem

#ifndef CPROVER_PATH_STRATEGIES_H
#define CPROVER_PATH_STRATEGIES_H

#include <goto-programs/goto_model.h>
#include <goto-programs/safety_checker.h>

#include <goto-symex/goto_symex_state.h>

/// \brief Events that we expect to happen during path exploration
///
/// See the description in the .cpp file on how to use this class.
struct symex_eventt
{
public:
  enum class enumt
  {
    JUMP,
    NEXT,
    SUCCESS,
    FAILURE
  };
  typedef std::pair<enumt, int> pairt;
  typedef std::list<pairt> listt;

  static pairt resume(enumt kind, int location)
  {
    return pairt(kind, location);
  }

  static pairt result(enumt kind)
  {
    return pairt(kind, -1);
  }

  static void
  validate_result(listt &events, const safety_checkert::resultt result);

  static void validate_resume(listt &events, const goto_symex_statet &state);
};

void _check_with_strategy(
  const std::string &strategy,
  const std::string &program,
  const unsigned unwind_limit,
  symex_eventt::listt &events);

/// Call this one, not the underscore version
void check_with_strategy(
  const std::string &strategy,
  const std::string &program,
  symex_eventt::listt events,
  const unsigned unwind_limit)
{
  WHEN("strategy is '" + strategy + "'")
  _check_with_strategy(strategy, program, unwind_limit, events);
}

#endif // CPROVER_PATH_STRATEGIES_H
