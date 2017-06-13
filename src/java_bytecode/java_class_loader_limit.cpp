/*******************************************************************\

Module: limit class path loading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <json/json_parser.h>

#include "java_class_loader_limit.h"

/*******************************************************************\

Function: java_class_loader_limitt::setup_class_load_limit

  Inputs: parameter from `java-cp-include-files`

 Outputs:

 Purpose: initializes class with either regex matcher or match set

\*******************************************************************/

void java_class_loader_limitt::setup_class_load_limit(
  std::string &java_cp_include_files)
{
  if(java_cp_include_files.empty())
    throw "class regexp cannot be empty";

  // '@' signals file reading with list of class files to load
  regex_match=java_cp_include_files[0]!='@';
  if(regex_match)
    regex_matcher=std::regex(java_cp_include_files);
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
    for(const jsont &file_entry : include_files.array)
    {
      assert(file_entry.is_string());
      set_matcher.insert(file_entry.value);
    }
  }
}

/*******************************************************************\

Function: java_class_loader_limitt::load_class_file

  Inputs: class file name

 Outputs: true if file should be loaded, else false

 Purpose:

\*******************************************************************/

bool java_class_loader_limitt::load_class_file(const irep_idt &file_name)
{
  if(regex_match)
  {
    return std::regex_match(
      id2string(file_name),
      string_matcher,
      regex_matcher);
  }
  // load .class file only if it is in the match set
  else
    return set_matcher.find(id2string(file_name))!=set_matcher.end();
}
