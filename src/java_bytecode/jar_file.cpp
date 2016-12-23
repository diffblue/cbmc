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

Function: jar_filet::open

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jar_filet::open(const std::string &filename)
{
  #ifdef HAVE_LIBZIP
  if(zip!=nullptr)
    // NOLINTNEXTLINE(readability/identifiers)
    zip_close(static_cast<struct zip *>(zip));

  int zip_error;
  zip=zip_open(filename.c_str(), 0, &zip_error);

  if(zip!=nullptr)
  {
    std::size_t number_of_files=
      // NOLINTNEXTLINE(readability/identifiers)
      zip_get_num_entries(static_cast<struct zip *>(zip), 0);

    index.reserve(number_of_files);

    for(std::size_t i=0; i<number_of_files; i++)
    {
      std::string file_name=
        // NOLINTNEXTLINE(readability/identifiers)
        zip_get_name(static_cast<struct zip *>(zip), i, 0);
      index.push_back(file_name);
    }
  }
  #else
  zip=nullptr;
  #endif
}

/*******************************************************************\

Function: jar_filet::~jar_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jar_filet::~jar_filet()
{
  #ifdef HAVE_LIBZIP
  if(zip!=nullptr)
    // NOLINTNEXTLINE(readability/identifiers)
    zip_close(static_cast<struct zip *>(zip));
  #endif
}

/*******************************************************************\

Function: jar_filet::get_entry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define ZIP_READ_SIZE 10000

std::string jar_filet::get_entry(std::size_t i)
{
  if(zip==nullptr)
    return std::string("");

  assert(i<index.size());

  std::string dest;

  #ifdef HAVE_LIBZIP
  void *zip_e=zip; // zip is both a type and a non-type
  // NOLINTNEXTLINE(readability/identifiers)
  struct zip *zip_p=static_cast<struct zip*>(zip_e);

  // NOLINTNEXTLINE(readability/identifiers)
  struct zip_file *zip_file=zip_fopen_index(zip_p, i, 0);

  if(zip_file==NULL)
  {
    zip_close(zip_p);
    zip=nullptr;
    return std::string(""); // error
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
  #endif

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

  return manifest;
}
