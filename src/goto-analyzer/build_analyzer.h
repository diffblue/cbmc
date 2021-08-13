/*******************************************************************\

Module: Goto-Analyzer Command Line Option Processing

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_BUILD_ANALYZER_H
#define CPROVER_GOTO_ANALYZER_BUILD_ANALYZER_H

#include <memory>

class ai_baset;
class goto_modelt;
class namespacet;
class optionst;
class message_handlert;

/// Build an abstract interpreter configured by the options.
/// This may require options for:
///  * which interpreter to use
///  * which history to use
///  * which storage to use
///  * which domain to use
///  * how that domain is configured
/// Not every combination of options is supported.
/// Unsupported options will give null.
/// Domains also may throw a invalid_command_line_argument_exceptiont
std::unique_ptr<ai_baset> build_analyzer(
  const optionst &options,
  const goto_modelt &goto_model,
  const namespacet &ns,
  message_handlert &mh);

#endif // CPROVER_GOTO_ANALYZER_GOTO_ANALYZER_PARSE_OPTIONS_H
