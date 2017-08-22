/*******************************************************************\

Module: Java specific language options

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_PARSE_OPTIONS_H
#define CPROVER_JAVA_BYTECODE_JAVA_PARSE_OPTIONS_H

#include <string>

#include <util/cmdline.h>
#include <util/message.h>

#define OPT_PARAM_JAVA_INCLUDE_FILES \
  "java-cp-include-files"

#define OPT_JAVA_INCLUDE_FILES \
  "(" OPT_PARAM_JAVA_INCLUDE_FILES "):"

#define HELP_JAVA_INCLUDE_FILES \
  " --java-cp-include-files      regexp or JSON list of files to load (with '@' prefix)\n" // NOLINT(whitespace/line_length)

std::string java_get_cp_include_files(const cmdlinet &, message_handlert &);

#endif
