/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_STATIC_INSTRUMENT_H
#define CPROVER_GOTO_ANALYZER_STATIC_INSTRUMENT_H

#include <iosfwd>

// What kind of instrumentation to add
enum class instrument_actiont
{
  NOTHING,
  ASSERT,
  ASSUME
};

// What kind of instrumentation to add at each location
struct instrument_configt
{
public:
  instrument_actiont function_start;
  instrument_actiont function_end;
  instrument_actiont function_call;
  instrument_actiont function_return;
  instrument_actiont any_goto_target;
  instrument_actiont backwards_goto_target;
  instrument_actiont after_goto_not_taken;
  bool requires;
  bool ensures;

  instrument_configt()
    : function_start(instrument_actiont::NOTHING),
      function_end(instrument_actiont::NOTHING),
      function_call(instrument_actiont::NOTHING),
      function_return(instrument_actiont::NOTHING),
      any_goto_target(instrument_actiont::NOTHING),
      backwards_goto_target(instrument_actiont::NOTHING),
      after_goto_not_taken(instrument_actiont::NOTHING),
      requires(false),
      ensures(false)
  {
  }

  // Parse from an option string
  explicit instrument_configt(const std::string &opts);
};

class ai_baset;
class goto_modelt;
class message_handlert;
class optionst;

// For using this functionality in other tools
void static_instrument_goto_model(
  goto_modelt &,
  const ai_baset &,
  const instrument_configt &,
  message_handlert &);

// As used in goto-analyze
bool static_instrument(
  goto_modelt &,
  const ai_baset &,
  const std::string &configuration_string,
  message_handlert &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_STATIC_INSTRUMENT_H
