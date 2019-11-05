/*******************************************************************\

Module: Restrict function pointers

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
#define RESTRICT_FUNCTION_POINTER_BY_NAME_OPT                                  \
  "restrict-function-pointer-by-name"

#define OPT_RESTRICT_FUNCTION_POINTER                                          \
  "(" RESTRICT_FUNCTION_POINTER_OPT                                            \
  "):"                                                                         \
  "(" RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT                                  \
  "):"                                                                         \
  "(" RESTRICT_FUNCTION_POINTER_BY_NAME_OPT "):"

#define HELP_RESTRICT_FUNCTION_POINTER                                         \
  "--" RESTRICT_FUNCTION_POINTER_OPT                                           \
  " <pointer_name>/<target[,targets]*>\n"                                      \
  "           restrict a function pointer to a set of possible targets\n"      \
  "           targets must all exist in the symbol table with a matching "     \
  "type\n"                                                                     \
  "           works for globals and function parameters right now\n"           \
  "--" RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT                                 \
  " <file_name>\n"                                                             \
  "           add function pointer restrictions from file"

void parse_function_pointer_restriction_options_from_cmdline(
  const cmdlinet &cmdline,
  optionst &options);

class jsont;
class message_handlert;

class function_pointer_restrictionst
{
public:
  using restrictionst =
    std::unordered_map<irep_idt, std::unordered_set<irep_idt>>;
  using restrictiont = restrictionst::value_type;

  const restrictionst restrictions;

  /// parse function pointer restrictions from command line
  ///
  /// Note: These are are only syntactically checked at this stage,
  ///       because type checking them requires a goto_modelt
  static function_pointer_restrictionst
  from_options(const optionst &options, message_handlert &message_handler);

  jsont to_json() const;
  static function_pointer_restrictionst from_json(const jsont &json);

  static function_pointer_restrictionst read_from_file(
    const std::string &filename,
    message_handlert &message_handler);

  void write_to_file(const std::string &filename) const;

  function_pointer_restrictionst
  merge(const function_pointer_restrictionst &other) const;

  static restrictionst parse_function_pointer_restrictions_from_command_line(
    const std::list<std::string> &restriction_opts,
    const std::string &option_name);

protected:
  static restrictionst merge_function_pointer_restrictions(
    restrictionst lhs,
    const restrictionst &rhs);

  static restrictionst parse_function_pointer_restrictions_from_file(
    const std::list<std::string> &filenames,
    message_handlert &message_handler);

  static restrictiont
  parse_function_pointer_restriction(const std::string &restriction_opt);
};

function_pointer_restrictionst get_function_pointer_by_name_restrictions(
  const goto_modelt &goto_model,
  const optionst &options);

/// Apply function pointer restrictions to a goto_model. Each restriction is a
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
