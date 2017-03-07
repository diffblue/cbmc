/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>
#include <cassert>
#include <json/json_parser.h>
#include <unordered_set>
#include "jar_file.h"
#include <util/suffix.h>
#include <iostream>
/*******************************************************************\

Function: jar_filet::open

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jar_filet::open(
  std::string &java_cp_include_files,
  const std::string &filename)
{
  if(!mz_ok)
  {
    memset(&zip, 0, sizeof(zip));
    mz_bool mz_open=mz_zip_reader_init_file(&zip, filename.c_str(), 0);
    mz_ok=mz_open==MZ_TRUE;
  }

  if(mz_ok)
  {
    // '@' signals file reading with list of class files to load
    bool regex_match=java_cp_include_files[0]!='@';
    std::regex regex_matcher;
    std::smatch string_matcher;
    std::unordered_set<std::string> set_matcher;
    jsont json_cp_config;
    if(regex_match)
      regex_matcher=std::regex(java_cp_include_files);
    else
    {
      assert(java_cp_include_files.length()>1);
      if(parse_json(
           java_cp_include_files.substr(1),
           get_message_handler(),
           json_cp_config))
        throw "cannot read JSON input configuration for JAR loading";
      assert(json_cp_config.is_object() && "JSON has wrong format");
      jsont include_files=json_cp_config["classFiles"];
      assert(include_files.is_array() && "JSON has wrong format");
      for(const jsont &file_entry : include_files.array)
      {
        assert(file_entry.is_string());
        set_matcher.insert(file_entry.value);
      }
    }

    std::size_t number_of_files=
      mz_zip_reader_get_num_files(&zip);

    size_t filtered_index=0;
    for(std::size_t i=0; i<number_of_files; i++)
    {
      mz_uint filename_length=mz_zip_reader_get_filename(&zip, i, nullptr, 0);
      char *filename_char=new char[filename_length+1];
      mz_uint filename_len=
        mz_zip_reader_get_filename(&zip, i, filename_char, filename_length);
      assert(filename_length==filename_len);
      std::string file_name(filename_char);

      // non-class files are loaded in any case
      bool add_file=!has_suffix(file_name, ".class");
      // load .class file only if they match regex
      if(regex_match)
        add_file|=std::regex_match(file_name, string_matcher, regex_matcher);
      // load .class file only if it is in the match set
      else
        add_file|=set_matcher.count(file_name)>0;
      if(add_file)
      {
        index.push_back(file_name);
        filtered_jar[filtered_index]=i;
        filtered_index++;
      }
      delete[] filename_char;
    }
  }
}

/*******************************************************************\

Function: jar_filet::~jar_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jar_filet::~jar_filet()
{
  if(mz_ok)
  {
    mz_zip_reader_end(&zip);
    mz_ok=false;
  }
}

/*******************************************************************\

Function: jar_filet::get_entry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string jar_filet::get_entry(std::size_t i)
{
  if(!mz_ok)
    return std::string("");

  assert(i<index.size());

  std::string dest;

  size_t real_index=filtered_jar[i];
  mz_zip_archive_file_stat file_stat;
  memset(&file_stat, 0, sizeof(file_stat));
  mz_bool stat_ok=mz_zip_reader_file_stat(&zip, real_index, &file_stat);
  if(stat_ok!=MZ_TRUE)
    return std::string();
  std::vector<char> buffer;
  size_t bufsize=file_stat.m_uncomp_size;
  buffer.resize(bufsize);
  mz_bool read_ok=
    mz_zip_reader_extract_to_mem(&zip, real_index, buffer.data(), bufsize, 0);
  if(read_ok!=MZ_TRUE)
    return std::string();

  dest.insert(dest.end(), buffer.begin(), buffer.end());

  return dest;
}

/*******************************************************************\

Function: jar_filet::get_manifest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jar_filet::manifestt jar_filet::get_manifest()
{
  std::size_t i=0;
  bool found=false;

  for(const auto &e : index)
  {
    if(e=="META-INF/MANIFEST.MF")
    {
      found=true;
      break;
    }

    i++;
  }

  if(!found)
    return manifestt();

  std::string dest=get_entry(i);
  std::istringstream in(dest);

  manifestt manifest;

  std::string line;
  while(std::getline(in, line))
  {
    std::size_t pos=line.find(':');
    if(pos==std::string::npos)
      continue;
    std::string key=line.substr(0, pos);

    // skip spaces
    pos++;
    while(pos<line.size() && line[pos]==' ') pos++;

    std::string value=line.substr(pos, std::string::npos);

    // trim off \r
    if(!value.empty() && *value.rbegin()=='\r')
      value.resize(value.size()-1);

    // store
    manifest[key]=value;
  }

  return manifest;
}
