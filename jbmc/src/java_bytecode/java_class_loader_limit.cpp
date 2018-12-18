/*******************************************************************\

Module: limit class path loading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// limit class path loading

#include "java_class_loader_limit.h"

#include <json/json_parser.h>

#include <util/invariant.h>

/// Initializes class with either regex matcher or match set. If the string
/// starts with an `@` it is treated as a path to a JSON file. Otherwise, it is
/// treated as a regex.
///
/// The regex case describes which class files should be loaded in the form of a
/// regular expression used with `regex_match`.
///
/// The match set is a list of files to load in JSON format, the argument is the
/// name of the JSON file, prefixed with `@`. The file contains one section to
/// list the .jar files to load and one section to list the .class files to load
/// from the .jar.
///
/// for example a file called `load.json` with the following content:
/// {
///   "jar":
///   [
///     "A.jar",
///     "B.jar"
///   ],
///   "classFiles":
///   [
///     "jarfile3$A.class",
///     "jarfile3.class"
///   ]
/// }
/// would be specified via `--java-cp-include-files @load.json` and would
/// instruct the driver to load `A.jar` and `B.jar` and the two .class files
/// `jarfile3$A.class` and `jarfile3.class`. All the rest of the .jar files is
/// ignored.
///
/// \param java_cp_include_files: parameter from `java-cp-include-files` in the
///   format as described above
void java_class_loader_limitt::setup_class_load_limit(
  const std::string &java_cp_include_files)
{
  PRECONDITION(!java_cp_include_files.empty());

  // '@' signals file reading with list of class files to load
  use_regex_match = java_cp_include_files[0] != '@';
  if(use_regex_match)
  {
    regex_matcher=std::regex(java_cp_include_files);
    debug() << "Limit loading to classes matching '" << java_cp_include_files
            << "'" << eom;
  }
  else
  {
    assert(java_cp_include_files.length()>1);
    jsont json_cp_config;
    if(parse_json(
         java_cp_include_files.substr(1),
         get_message_handler(),
         json_cp_config))
      throw "cannot read JSON input configuration for JAR loading";
    if(!json_cp_config.is_object())
      throw "the JSON file has a wrong format";
    jsont include_files=json_cp_config["classFiles"];
    if(!include_files.is_null() && !include_files.is_array())
      throw "the JSON file has a wrong format";
    for(const jsont &file_entry : to_json_array(include_files))
    {
      assert(file_entry.is_string());
      set_matcher.insert(file_entry.value);
    }
  }
}

/// Use the class load limiter to decide whether a class file should be loaded
/// or not.
/// \param file_name: the name of the class file to load
/// \return true if file should be loaded, else false
bool java_class_loader_limitt::load_class_file(const std::string &file_name)
{
  if(use_regex_match)
  {
    std::smatch string_matches;
    if(std::regex_match(file_name, string_matches, regex_matcher))
      return true;
    debug() << file_name + " discarded since not matching loader regexp" << eom;
    return false;
  }
  else
    // load .class file only if it is in the match set
    return set_matcher.find(file_name) != set_matcher.end();
}
