/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

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

  std::vector<char> data;
  while(true)
  {
    dest.resize(dest.size()+ZIP_READ_SIZE);
    int bytes_read=
      zip_fread(zip_file, dest.data()-ZIP_READ_SIZE, ZIP_READ_SIZE);
    if(bytes_read<0) break;
    assert(bytes_read<=ZIP_READ_SIZE);
    dest.resize(dest.size()-ZIP_READ_SIZE+bytes_read);
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

