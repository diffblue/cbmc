/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#ifndef CPROVER_ANSI_C_DESIGNATOR_H
#define CPROVER_ANSI_C_DESIGNATOR_H

#include <vector>
#include <iosfwd>

#include <util/type.h>

class designatort
{
public:
  struct entryt
  {
    size_t index;
    size_t size;
    bool vla_permitted;
    typet type, subtype;

    explicit entryt(const typet &type):
      index(0), size(0), vla_permitted(false), type(type)
    {
    }
  };

  bool empty() const { return index_list.empty(); }
  size_t size() const { return index_list.size(); }
  const entryt &operator[](size_t i) const { return index_list[i]; }
  entryt &operator[](size_t i) { return index_list[i]; }
  const entryt &back() const { return index_list.back(); }
  const entryt &front() const { return index_list.front(); }

  designatort() { }

  void push_entry(const entryt &entry)
  {
    index_list.push_back(entry);
  }

  void pop_entry()
  {
    index_list.pop_back();
  }

  void print(std::ostream &out) const;

protected:
  // a list of indices into arrays or structs
  typedef std::vector<entryt> index_listt;
  index_listt index_list;
};

inline std::ostream &operator << (std::ostream &os, const designatort &d)
{
  d.print(os);
  return os;
}

#endif // CPROVER_ANSI_C_DESIGNATOR_H
