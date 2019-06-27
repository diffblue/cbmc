/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H

#include <unordered_set>
#include <util/symbol_table.h>
#include <util/message.h>

#include "java_bytecode_parse_tree.h"
#include "java_bytecode_language.h"

/// See class \ref java_bytecode_convert_classt
bool java_bytecode_convert_class(
  const java_class_loadert::parse_tree_with_overlayst &parse_trees,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  method_bytecodet &,
  java_string_library_preprocesst &string_preprocess,
  const std::unordered_set<std::string> &no_load_classes);

void convert_annotations(
  const java_bytecode_parse_treet::annotationst &parsed_annotations,
  std::vector<java_annotationt> &annotations);

void convert_java_annotations(
  const std::vector<java_annotationt> &java_annotations,
  java_bytecode_parse_treet::annotationst &annotations);

void mark_java_implicitly_generic_class_type(
  const irep_idt &class_name,
  symbol_tablet &symbol_table);

/// Register in the \p symbol_table new symbols for the objects
/// java::array[X] where X is byte, short, int, long, char, boolean, float,
/// double and reference.
/// Also registers a java::array[X].clone():Ljava/lang/Object; method for each
/// type.
void add_java_array_types(symbol_tablet &symbol_table);

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
