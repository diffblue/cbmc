/*******************************************************************\

Module: JAR File Reading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAR_FILE_H
#define CPROVER_JAVA_BYTECODE_JAR_FILE_H

#define _LARGEFILE64_SOURCE 1
#include "miniz/miniz.h"

#include <string>
#include <vector>
#include <map>
#include <regex>
#include <util/message.h>

class jar_filet:public messaget
{
public:
  jar_filet():mz_ok(false) { }

  ~jar_filet();

  void open(std::string &java_cp_include_files, const std::string &);

  // Test for error; 'true' means we are good.
  explicit operator bool() const { return mz_ok; }

  typedef std::vector<std::string> indext;
  indext index;
  // map internal index to real index in jar central directory
  typedef std::map<int, int> filtered_jart;
  filtered_jart filtered_jar;

  std::string get_entry(std::size_t i);

  typedef std::map<std::string, std::string> manifestt;
  manifestt get_manifest();

protected:
  mz_zip_archive zip;
  bool mz_ok;
};

class jar_poolt:public messaget
{
public:
  void set_java_cp_include_files(std::string &_java_cp_include_files)
  {
    java_cp_include_files=_java_cp_include_files;
  }

  jar_filet &operator()(const std::string &file_name)
  {
    if(java_cp_include_files.empty())
      throw "class regexp cannot be empty";
    file_mapt::iterator it=file_map.find(file_name);
    if(it==file_map.end())
    {
      jar_filet &jar_file=file_map[file_name];
      jar_file.set_message_handler(get_message_handler());
      jar_file.open(java_cp_include_files, file_name);
      return jar_file;
    }
    else
      return file_map[file_name];
  }

protected:
  typedef std::map<std::string, jar_filet> file_mapt;
  file_mapt file_map;
  std::string java_cp_include_files;
};

#endif // CPROVER_JAVA_BYTECODE_JAR_FILE_H
