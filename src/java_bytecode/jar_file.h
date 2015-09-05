/*******************************************************************\

Module: JAR File Reading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_JAR_FILE_H
#define CPROVER_JAVA_JAR_FILE_H

#include <string>
#include <vector>
#include <map>

bool get_jar_index(
  const std::string &jar_file,
  std::vector<std::string> &entries);

bool get_jar_entry(
  const std::string &jar_file,
  std::size_t index,
  std::vector<char> &);

bool get_jar_manifest(
  const std::string &jar_file,
  std::map<std::string, std::string> &);

#endif
