/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "jar_pool.h"
#include "jar_file.h"

jar_filet &jar_poolt::operator()(const std::string &file_name)
{
  const auto it = m_archives.find(file_name);
  if(it == m_archives.end())
    return m_archives.emplace(file_name, jar_filet(file_name)).first->second;
  else
    return it->second;
}

jar_filet &jar_poolt::add_jar(
  const std::string &buffer_name,
  const void *pmem,
  size_t size)
{
  const auto it = m_archives.find(buffer_name);
  if(it == m_archives.end())
  {
    // VS: Can't construct in place
    auto file = jar_filet(pmem, size);
    return m_archives.emplace(buffer_name, std::move(file)).first->second;
  }
  else
    return it->second;
}
