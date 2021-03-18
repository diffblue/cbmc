/// \file
/// Complain about code formatting

#ifndef CPROVER_GOTO_INSTRUMENT_OPINIONATED_LINTER_H
#define CPROVER_GOTO_INSTRUMENT_OPINIONATED_LINTER_H

#include <goto-programs/goto_model.h>
#include <util/irep.h>
#include <util/message.h>

#include <util/make_unique.h>
#include <memory>

/// Analyses that return a score for a program, as well as a maximum score that
/// the program could achieve.
class linter_analysist
{
public:
  virtual int max_score() = 0;
  virtual int score() = 0;

  virtual ~linter_analysist() {}
};

/// Return a low score if the program, when converted to C, still contains gotos
class goto_hatert : public linter_analysist
{
protected:
  goto_modelt &gm;

public:
  explicit goto_hatert(goto_modelt &gm)
  : gm(gm)
  {}

  int max_score() override;
  int score() override;
};

/// Return a high score if the program has short functions on average.
class average_fun_lengtht : public linter_analysist
{
protected:
  const goto_functionst &gf;
  const std::list<int> boundaries;

public:
  explicit average_fun_lengtht(const goto_functionst &gf)
  : gf(gf), boundaries({80, 70, 60, 50, 40, 30, 20})
  {}

  int max_score() override;
  int score() override;
};

/// Linter: run all analyses and return a final score.
class considered_harmfult
{
protected:
  goto_modelt &gm;
  messaget log;
  std::list<linter_analysist *> analyses;
  const std::map<int, std::string> score_map;

public:
  considered_harmfult(
      goto_modelt &gm,
      message_handlert &mh)
  : gm(gm), log(mh), analyses(), score_map({
      {20,  u8"💩"},
      {40,  u8"🤮"},
      {60,  u8"😱"},
      {80,  u8"😖"},
      {101, u8"😐"},
    })
  {
    analyses.push_back(new average_fun_lengtht(this->gm.goto_functions));
    analyses.push_back(new goto_hatert(this->gm));
  }

  void operator()();
};

// clang-format off
#define OPT_OPINIONATED_LINTER "(condescending-linter)"
#define HELP_OPINIONATED_LINTER \
  " --condecending-linter          Complain about code formatting\n"
// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_OPINIONATED_LINTER_H
