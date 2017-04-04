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

#include "java_class_loader_limit.h"

class jar_filet:public messaget
{
public:
  jar_filet():mz_ok(false) { }

  ~jar_filet();

  void open(java_class_loader_limitt &, const std::string &);

  // Test for error; 'true' means we are good.
  explicit operator bool() const { return mz_ok; }

  // map internal index to real index in jar central directory
  typedef std::map<irep_idt, size_t> filtered_jart;
  filtered_jart filtered_jar;

  std::string get_entry(const irep_idt &);

  typedef std::map<std::string, std::string> manifestt;
  manifestt get_manifest();

protected:
  mz_zip_archive zip;
  bool mz_ok;
};

class jar_poolt:public messaget
{
public:
  jar_filet &operator()(
    java_class_loader_limitt &class_loader_limit,
    const std::string &file_name)
  {
    file_mapt::iterator it=file_map.find(file_name);
    if(it==file_map.end())
    {
      jar_filet &jar_file=file_map[file_name];
      jar_file.set_message_handler(get_message_handler());
      jar_file.open(class_loader_limit, file_name);
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
