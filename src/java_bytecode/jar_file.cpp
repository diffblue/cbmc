/*******************************************************************\

Module: Jar file reader

Author: Diffblue Ltd

\*******************************************************************/

#include "jar_file.h"
#include <cctype>
#include <util/suffix.h>
#include <util/invariant.h>
#include "java_class_loader_limit.h"

jar_filet::jar_filet(
  java_class_loader_limitt &limit,
  const std::string &filename):
  m_zip_archive(filename)
{
  const size_t file_count=m_zip_archive.get_num_files();
  for(size_t index=0; index<file_count; index++)
  {
    const auto filename=m_zip_archive.get_filename(index);
    if(!has_suffix(filename, ".class") || limit.load_class_file(filename))
      m_name_to_index.emplace(filename, index);
  }
}

// VS: No default move constructors or assigns

jar_filet::jar_filet(jar_filet &&other):
  m_zip_archive(std::move(other.m_zip_archive)),
  m_name_to_index((other.m_name_to_index)) {}

jar_filet &jar_filet::operator=(jar_filet &&other)
{
  m_zip_archive=std::move(other.m_zip_archive);
  m_name_to_index=std::move(other.m_name_to_index);
  return *this;
}

std::string jar_filet::get_entry(const std::string &name)
{
  const auto entry=m_name_to_index.find(name);
  INVARIANT(entry!=m_name_to_index.end(), "File doesn't exist");
  try
  {
    return m_zip_archive.extract(entry->second);
  }
  catch(const std::runtime_error &)
  {
    return "";
  }
}

static bool is_space(const char ch)
{
  return std::isspace(ch);
}

/// Remove leading and trailing whitespace characters from string
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
  std::unordered_map<std::string, std::string> out;
  const auto entry=m_name_to_index.find("META-INF/MANIFEST.MF");
  if(entry!=m_name_to_index.end())
  {
    std::istringstream in(this->get_entry(entry->first));
    std::string line;
    while(std::getline(in, line))
    {
      const auto key_end=std::find(line.cbegin(), line.cend(), ':');
      if(key_end!=line.cend())
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
