/*******************************************************************\

Module: JAR File Reading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_JAR_FILE_H
#define CPROVER_JAVA_JAR_FILE_H

#include <string>
#include <vector>

bool get_jar_index(
  const std::string &jar_file,
  std::vector<std::string> &entries);

bool get_jar_entry(
  const std::string &jar_file,
  std::size_t index,
  std::vector<char> &);

#endif
