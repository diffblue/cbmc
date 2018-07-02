/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#include "string_container.h"

#include <cstring>
#include <iostream>
#include <numeric>

string_ptrt::string_ptrt(const char *_s):s(_s), len(strlen(_s))
{
}

bool string_ptrt::operator==(const string_ptrt &other) const
{
  if(len!=other.len)
    return false;

  return len==0 || memcmp(s, other.s, len)==0;
}

string_containert::~string_containert()
{
}

unsigned string_containert::get(const char *s)
{
  string_ptrt string_ptr(s);

  hash_tablet::iterator it=hash_table.find(string_ptr);

  if(it!=hash_table.end())
    return it->second;

  size_t r=hash_table.size();

  // these are stable
  string_list.push_back(std::string(s));
  string_ptrt result(string_list.back());

  hash_table[result]=r;

  // these are not
  string_vector.push_back(&string_list.back());

  return r;
}

unsigned string_containert::get(const std::string &s)
{
  string_ptrt string_ptr(s);

  hash_tablet::iterator it=hash_table.find(string_ptr);

  if(it!=hash_table.end())
    return it->second;

  size_t r=hash_table.size();

  // these are stable
  string_list.push_back(s);
  string_ptrt result(string_list.back());

  hash_table[result]=r;

  // these are not
  string_vector.push_back(&string_list.back());

  return r;
}

void string_container_statisticst::dump_on_stream(std::ostream &out) const
{
  auto total_memory_usage = strings_memory_usage + vector_memory_usage +
                            map_memory_usage + list_memory_usage;
  out << "String container statistics:"
      << "\n  string count: " << string_count
      << "\n  string memory usage: " << strings_memory_usage.to_string()
      << "\n  vector memory usage: " << vector_memory_usage.to_string()
      << "\n  map memory usage:    " << map_memory_usage.to_string()
      << "\n  list memory usage:   " << list_memory_usage.to_string()
      << "\n  total memory usage:  " << total_memory_usage.to_string() << '\n';
}

string_container_statisticst string_containert::compute_statistics() const
{
  string_container_statisticst result;
  result.string_count = string_vector.size();
  result.vector_memory_usage = memory_sizet::from_bytes(
    sizeof(string_vector) +
    sizeof(string_vectort::value_type) * string_vector.capacity());
  result.strings_memory_usage = memory_sizet::from_bytes(std::accumulate(
    begin(string_vector),
    end(string_vector),
    std::size_t(0),
    [](std::size_t sz, const std::string *s) { return sz + s->capacity(); }));
  result.map_memory_usage = memory_sizet::from_bytes(
    sizeof(hash_table) + hash_table.size() * sizeof(hash_tablet::value_type));

  result.list_memory_usage = memory_sizet::from_bytes(
    sizeof(string_list) + 2 * sizeof(void *) * string_list.size());
  return result;
}
