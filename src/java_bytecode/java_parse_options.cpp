/*******************************************************************\

Module: Java specific language options

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <util/config.h>
#include <util/message.h>
#include <util/suffix.h>

#include <json/json_parser.h>

#include "java_parse_options.h"

/*******************************************************************\

Function: java_get_cp_include_files

  Inputs: command-line object and message handler

 Outputs: returns value of Java class loading parameter

 Purpose: set-up java class loading limit (possible side effect:
           change of classpath)

\*******************************************************************/

std::string java_get_cp_include_files(
  const cmdlinet &cmd,
  message_handlert &message)
{
  if(!cmd.isset(OPT_PARAM_JAVA_INCLUDE_FILES))
    return ".*";
  std::string java_cp_include_files=cmd.get_value(OPT_PARAM_JAVA_INCLUDE_FILES);
  // load file list from JSON file
  if(java_cp_include_files[0]=='@')
  {
    jsont json_cp_config;
    if(parse_json(
         java_cp_include_files.substr(1),
         message,
         json_cp_config))
      throw "cannot read JSON input configuration for JAR loading";

    if(!json_cp_config.is_object())
      throw "the JSON file has a wrong format";
    jsont include_files=json_cp_config["jar"];
    if(!include_files.is_array())
      throw "the JSON file has a wrong format";

    // add jars from JSON config file to classpath
    for(const jsont &file_entry : include_files.array)
    {
      assert(file_entry.is_string() && has_suffix(file_entry.value, ".jar"));
      config.java.classpath.push_back(file_entry.value);
    }
  }
  return java_cp_include_files;
}
