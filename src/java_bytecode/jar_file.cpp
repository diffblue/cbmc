/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <sstream>

#include "jar_file.h"

#ifdef HAVE_LIBZIP
#include <zip.h>
#endif

/*******************************************************************\

Function: get_jar_entry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define ZIP_READ_SIZE 10000

bool get_jar_entry(
  const std::string &jar_file,
  std::size_t index,
  std::vector<char> &dest)
{
  #ifdef HAVE_LIBZIP
  int zip_error;
  
  struct zip *zip=
    zip_open(jar_file.c_str(), 0, &zip_error);
    
  if(zip==NULL)
    return true; // error
    
  struct zip_file *zip_file=
    zip_fopen_index(zip, index, 0);
  
  if(zip_file==NULL)
  {
    zip_close(zip);
    return true; // error
  }

  std::vector<char> buffer;
  buffer.resize(ZIP_READ_SIZE);
  
  while(true)
  {
    int bytes_read=
      zip_fread(zip_file, buffer.data(), ZIP_READ_SIZE);
    assert(bytes_read<=ZIP_READ_SIZE);
    if(bytes_read<=0) break;
    dest.insert(dest.end(), buffer.begin(), buffer.begin()+bytes_read);
  }

  zip_fclose(zip_file);    
  zip_close(zip);
  
  return false;
  #else
  return true;
  #endif
}

/*******************************************************************\

Function: get_jar_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool get_jar_index(
  const std::string &jar_file,
  std::vector<std::string> &entries)
{
  #ifdef HAVE_LIBZIP
  int zip_error;
  struct zip *zip=zip_open(jar_file.c_str(), 0, &zip_error);

  if(zip==NULL)
    return true;
  
  std::size_t number_of_files=zip_get_num_entries(zip, 0);
  
  for(std::size_t index=0; index<number_of_files; index++)
  {
    std::string file_name=zip_get_name(zip, index, 0);
    entries.push_back(file_name);
  }
  
  zip_close(zip);
  
  return false;
  #else
  return true;
  #endif
}

/*******************************************************************\

Function: get_jar_manifest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define ZIP_READ_SIZE 10000

bool get_jar_manifest(
  const std::string &jar_file,
  std::map<std::string, std::string> &manifest)
{
  std::vector<std::string> entries;
  if(get_jar_index(jar_file, entries))
    return true;
    
  std::size_t index=0;
  bool found=false;
    
  for(std::vector<std::string>::const_iterator
      e_it=entries.begin(); e_it!=entries.end(); e_it++)
  {
    if(*e_it=="META-INF/MANIFEST.MF")
    {
      index=e_it-entries.begin();
      found=true;
      break;
    }
  }

  if(!found) return true;  
  
  std::vector<char> dest; 
  if(get_jar_entry(jar_file, index, dest))
    return true;

  std::istringstream in(dest.data());

  std::string line;
  while(std::getline(in, line))
  {
    std::size_t pos=line.find(':');
    if(pos==std::string::npos) continue;
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
  
  return false;
}
