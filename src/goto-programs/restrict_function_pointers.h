/*******************************************************************\

Module: GOTO Program Utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Given goto functions and a list of function parameters or globals
/// that are function pointers with lists of possible candidates, replace use of
/// these function pointers with calls to the candidate.
/// The purpose here is to avoid unnecessary branching
/// i.e. "there are 600 functions with this signature, but I know it's
/// always going to be one of these two"

#ifndef CPROVER_GOTO_PROGRAMS_RESTRICT_FUNCTION_POINTERS_H
#define CPROVER_GOTO_PROGRAMS_RESTRICT_FUNCTION_POINTERS_H

#include <unordered_map>
#include <unordered_set>

#include <util/cmdline.h>
#include <util/irep.h>

#include <goto-programs/goto_model.h>
#include <util/options.h>

#define RESTRICT_FUNCTION_POINTER_OPT "restrict-function-pointer"
#define RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT                                \
  "function-pointer-restrictions-file"

#define OPT_RESTRICT_FUNCTION_POINTER                                          \
  "(" RESTRICT_FUNCTION_POINTER_OPT                                            \
  "):"                                                                         \
  "(" RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT "):"

#define RESTRICT_FUNCTION_POINTER_HELP                                         \
  "--" RESTRICT_FUNCTION_POINTER_OPT                                           \
  " <pointer_name>/<target[,targets]*>\n"                                      \
  "           restrict a function pointer to a set of possible targets\n"      \
  "           targets must all exist in the symbol table with a matching "     \
  "type\n"                                                                     \
  "           works for globals and function parameters right now\n"           \
  "--" RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT                                 \
  " <file_name>\n"                                                             \
  "           add from function pointer restrictions from file"

void parse_function_pointer_restriction_options_from_cmdline(
  const cmdlinet &cmdline,
  optionst &options);

class message_handlert;
struct function_pointer_restrictionst
{
  using restrictionst =
    std::unordered_map<irep_idt, std::unordered_set<irep_idt>>;
  using value_type = restrictionst::value_type;
  const restrictionst restrictions;

  /// parse function pointer restrictions from command line
  ///
  /// Note: These are are only syntactically checked at this stage,
  ///       because type checking them requires a goto_modelt
  static function_pointer_restrictionst
  from_options(const optionst &options, message_handlert &message_handler);

  static function_pointer_restrictionst read_from_file(
    const std::string &filename,
    message_handlert &message_handler);

  void write_to_file(const std::string &filename) const;
};

/// Apply a function pointer restrictions to a goto_model. Each restriction is a
/// mapping from a pointer name to a set of possible targets. Replace calls of
/// these "restricted" pointers with a branch on the value of the function
/// pointer, comparing it to the set of possible targets. This also adds an
/// assertion that the pointer actually has one of the listed values.
///
/// Note: This requires label_function_pointer_call_sites to be run
///       before
void restrict_function_pointers(
  goto_modelt &goto_model,
  const function_pointer_restrictionst &restrictions);

#endif // CPROVER_GOTO_PROGRAMS_RESTRICT_FUNCTION_POINTERS_H
