/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H

#include <util/symbol_table.h>
#include <util/message.h>

#include "java_bytecode_parse_tree.h"
#include "java_bytecode_language.h"

/// See class \ref java_bytecode_convert_classt
bool java_bytecode_convert_class(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  method_bytecodet &,
  lazy_methods_modet,
  java_string_library_preprocesst &string_preprocess);

void mark_java_implicitly_generic_class_type(
  const irep_idt &class_name,
  symbol_tablet &symbol_table);

/// An exception that is raised checking whether a class is implicitly
/// generic if a symbol for an outer class is missing
class missing_outer_class_symbol_exceptiont : public std::logic_error
{
public:
  explicit missing_outer_class_symbol_exceptiont(
    const std::string &outer,
    const std::string &inner)
    : std::logic_error(
        "Missing outer class symbol: " + outer + ", for class " + inner)
  {
  }
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H
