/*******************************************************************\

Module: limit class path loading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// limit class path loading

#ifndef CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_LIMIT_H
#define CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_LIMIT_H

#include <set>
#include <regex>

#include <util/irep.h>
#include <util/message.h>

/// Class representing a filter for class file loading.
class java_class_loader_limitt:public messaget
{
  /// Whether to use regex_matcher instead of set_matcher
  bool use_regex_match;
  std::regex regex_matcher;
  std::set<std::string> set_matcher;

  void setup_class_load_limit(const std::string &);

public:
  explicit java_class_loader_limitt(
    message_handlert &message_handler,
    const std::string &java_cp_include_files)
    : messaget(message_handler)
  {
    setup_class_load_limit(java_cp_include_files);
  }

  bool load_class_file(const std::string &class_file_name);
};

#endif
