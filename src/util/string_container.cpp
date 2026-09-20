/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#include "string_container.h"

#include <iostream>
#include <numeric>
#include <string_view>

string_containert::~string_containert()
{
}

unsigned string_containert::get(std::string_view s)
{
  hash_tablet::iterator it = hash_table.find(s);

  if(it!=hash_table.end())
    return it->second;

  size_t r=hash_table.size();

  // these are stable
  string_list.push_back(std::string(s));

  // the key is a view into the stable, interned copy -- not the (possibly
  // transient) argument
  hash_table[std::string_view{string_list.back()}] = r;

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
