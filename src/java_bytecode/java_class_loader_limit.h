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

class java_class_loader_limitt:public messaget
{
  std::regex regex_matcher;
  std::set<std::string> set_matcher;
  bool regex_match;
  std::smatch string_matcher;

  void setup_class_load_limit(const std::string &);

public:
  explicit java_class_loader_limitt(
    message_handlert &_message_handler,
    const std::string &java_cp_include_files):
    messaget(_message_handler),
    regex_match(false)
  {
    setup_class_load_limit(java_cp_include_files);
  }

  bool load_class_file(const irep_idt &class_file_name);
};

#endif
