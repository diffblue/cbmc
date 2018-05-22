/*******************************************************************\

Module: binary irep conversions with hashing

Author: CM Wintersteiger

Date: May 2007

\*******************************************************************/

/// \file
/// binary irep conversions with hashing

#ifndef CPROVER_UTIL_IREP_SERIALIZATION_H
#define CPROVER_UTIL_IREP_SERIALIZATION_H

#include <map>
#include <iosfwd>
#include <string>
#include <vector>

#include "irep_hash_container.h"
#include "irep.h"

void write_gb_word(std::ostream &, std::size_t);
void write_gb_string(std::ostream &, const std::string &);

class irep_serializationt
{
public:
  class ireps_containert
  {
  public:
    using ireps_on_readt = std::vector<std::pair<bool, irept> >;
    ireps_on_readt ireps_on_read;

    // number the ireps we have
    irep_full_hash_containert irep_full_hash_container;

    // this maps an irep number to a file offset
    using ireps_on_writet = std::map<std::size_t, std::streampos>;
    ireps_on_writet ireps_on_write;

    using string_mapt = std::vector<bool>;
    string_mapt string_map;

    using string_rev_mapt = std::vector<std::pair<bool, irep_idt> >;
    string_rev_mapt string_rev_map;

    void clear()
    {
      irep_full_hash_container.clear();
      ireps_on_write.clear();
      ireps_on_read.clear();
      string_map.clear();
      string_rev_map.clear();
    }
  };

  explicit irep_serializationt(ireps_containert &ic):
    ireps_container(ic)
  {
    read_buffer.resize(1, 0);
    clear();
  };

  const irept &reference_convert(std::istream &);
  void reference_convert(const irept &irep, std::ostream &);

  irep_idt read_string_ref(std::istream &);
  void write_string_ref(std::ostream &, const irep_idt &);

  void clear() { ireps_container.clear(); }

  static std::size_t read_gb_word(std::istream &);
  irep_idt read_gb_string(std::istream &);

private:
  ireps_containert &ireps_container;
  std::vector<char> read_buffer;

  void write_irep(std::ostream &, const irept &irep);
  void read_irep(std::istream &, irept &irep);
};

#endif // CPROVER_UTIL_IREP_SERIALIZATION_H
