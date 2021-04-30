/*******************************************************************\

Module: Java Bytecode

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Process a pattern to use as a regex for selecting extra entry points for
/// ci_lazy_methodst

#ifndef CPROVER_JAVA_BYTECODE_LOAD_METHOD_BY_REGEX_H
#define CPROVER_JAVA_BYTECODE_LOAD_METHOD_BY_REGEX_H

#include <util/irep.h>

#include <functional>
#include <vector>

class symbol_tablet;

std::function<std::vector<irep_idt>(const symbol_tablet &symbol_table)>
build_load_method_by_regex(const std::string &pattern);

bool does_pattern_miss_descriptor(const std::string &pattern);

#endif // CPROVER_JAVA_BYTECODE_LOAD_METHOD_BY_REGEX_H
