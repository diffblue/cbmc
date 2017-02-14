/*******************************************************************\

Module: JAR File Reading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAR_FILE_H
#define CPROVER_JAVA_BYTECODE_JAR_FILE_H

//#define MINIZ_HEADER_FILE_ONLY
#define _LARGEFILE64_SOURCE 1
#include "miniz_zip.h"

#include <string>
#include <vector>
#include <map>

class jar_filet
{
public:
  jar_filet():mz_ok(false) { }

  inline explicit jar_filet(const std::string &file_name)
  {
    open(file_name);
  }

  ~jar_filet();

  void open(const std::string &);

  // Test for error; 'true' means we are good.
  inline explicit operator bool() const { return true;  // TODO
  }

  typedef std::vector<std::string> indext;
  indext index;

  std::string get_entry(std::size_t i);

  typedef std::map<std::string, std::string> manifestt;
  manifestt get_manifest();

protected:
  mz_zip_archive zip;
  bool mz_ok;
};

class jar_poolt
{
public:
  jar_filet &operator()(const std::string &file_name)
  {
    file_mapt::iterator it=file_map.find(file_name);
    if(it==file_map.end())
    {
      jar_filet &jar_file=file_map[file_name];
      jar_file.open(file_name);
      return jar_file;
    }
    else
      return file_map[file_name];
  }

protected:
  typedef std::map<std::string, jar_filet> file_mapt;
  file_mapt file_map;
};

#endif // CPROVER_JAVA_BYTECODE_JAR_FILE_H
