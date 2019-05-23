/*******************************************************************\

Module: Jar file reader

Author: Diffblue Ltd

\*******************************************************************/

#include "jar_file.h"

#include <algorithm>
#include <cctype>

#include <util/invariant.h>
#include <util/suffix.h>

#include "java_class_loader_limit.h"

void jar_filet::initialize_file_index()
{
  const size_t file_count=m_zip_archive.get_num_files();
  for(size_t index=0; index<file_count; index++)
    m_name_to_index.emplace(m_zip_archive.get_filename(index), index);
}

/// This constructor creates a jar_file object whose contents
/// are extracted from a file with given name.
jar_filet::jar_filet(
  const std::string &filename):
  m_zip_archive(filename)
{
  initialize_file_index();
}

/// This constructor creates a jar_file object whose contents
/// are extracted from a memory buffer (byte array) as opposed
/// to a jar file.
jar_filet::jar_filet(
  const void *data,
  size_t size):
  m_zip_archive(data, size)
{
  initialize_file_index();
}

// VS: No default move constructors or assigns

jar_filet::jar_filet(jar_filet &&other)
  : m_zip_archive(std::move(other.m_zip_archive)),
    m_name_to_index(std::move(other.m_name_to_index))
{
}

jar_filet &jar_filet::operator=(jar_filet &&other)
{
  m_zip_archive=std::move(other.m_zip_archive);
  m_name_to_index=std::move(other.m_name_to_index);
  return *this;
}

optionalt<std::string> jar_filet::get_entry(const std::string &name)
{
  const auto entry=m_name_to_index.find(name);
  if(entry==m_name_to_index.end())
    return {};

  try
  {
    return m_zip_archive.extract(entry->second);
  }
  catch(const std::runtime_error &)
  {
    return {};
  }
}

/// Wrapper for `std::isspace` from `cctype`
/// \param ch: the character to check
/// \return true if the parameter is considered to be a space in the current
///   locale, else false
static bool is_space(const char ch)
{
  return std::isspace(ch) != 0;
}

/// Remove leading and trailing whitespace characters from string
/// \param begin: iterator to start search in string
/// \param end: iterator to end search in string
/// \return string truncated from begin to end and all whitespace removed at the
///   begin and end
static std::string trim(
  const std::string::const_iterator begin,
  const std::string::const_iterator end)
{
  const auto out_begin=std::find_if_not(begin, end, is_space);
  const auto out_end=std::find_if_not(
    std::string::const_reverse_iterator(end),
    std::string::const_reverse_iterator(out_begin),
    is_space).base();
  return { out_begin, out_end };
}

std::unordered_map<std::string, std::string> jar_filet::get_manifest()
{
  const auto entry=get_entry("META-INF/MANIFEST.MF");

  if(!entry.has_value())
    return {};

  std::unordered_map<std::string, std::string> out;
  std::istringstream in(*entry);
  std::string line;
  while(std::getline(in, line))
  {
    const auto key_end=std::find(line.cbegin(), line.cend(), ':');
    if(key_end!=line.cend())
    {
      out.emplace(
        trim(line.cbegin(), key_end),
        trim(std::next(key_end), line.cend()));
    }
  }

  return out;
}

std::vector<std::string> jar_filet::filenames() const
{
  std::vector<std::string> out;
  for(const auto &pair : m_name_to_index)
    out.emplace_back(pair.first);
  return out;
}
