/// \file Test for path strategies set through `cbmc --paths ...`
///
/// \author Kareem Khazem

#ifndef CPROVER_PATH_STRATEGIES_H
#define CPROVER_PATH_STRATEGIES_H

#include <goto-checker/incremental_goto_checker.h>

class goto_symex_statet;

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

  static void validate_result(
    listt &events,
    const incremental_goto_checkert::resultt::progresst result,
    std::size_t &);

  static void
  validate_resume(listt &events, const goto_symex_statet &state, std::size_t &);
};

void _check_with_strategy(
  const std::string &strategy,
  const std::string &program,
  std::function<void(optionst &)>,
  symex_eventt::listt &events);

/// Call this one, not the underscore version
void check_with_strategy(
  const std::string &strategy,
  std::function<void(optionst &)> opts_callback,
  const std::string &program,
  symex_eventt::listt events)
{
  WHEN("strategy is '" + strategy + "'")
  _check_with_strategy(strategy, program, opts_callback, events);
}

#endif // CPROVER_PATH_STRATEGIES_H
