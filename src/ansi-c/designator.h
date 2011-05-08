/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_DESIGNATOR_H
#define CPROVER_ANSI_C_DESIGNATOR_H

#include <type.h>

#include <vector>
#include <iostream>

class designatort
{
public:
  struct entryt
  {
    unsigned index;
    unsigned size;
    typet type, subtype;
    
    entryt():index(0), size(0)
    {
    }
  };

  bool empty() const { return index_list.empty(); }  
  unsigned size() const { return index_list.size(); }
  const entryt &operator[](unsigned i) const { return index_list[i]; }
  entryt &operator[](unsigned i) { return index_list[i]; }
  const entryt &back() const { return index_list.back(); };
  const entryt &front() const { return index_list.front(); };

  designatort() { }

  void push_entry(const entryt &entry)
  {
    index_list.push_back(entry);
  }
  
  void pop_entry()
  {
    index_list.pop_back();
  }

protected:
  // a list of indices into arrays or structs
  typedef std::vector<entryt> index_listt;
  index_listt index_list;
};

std::ostream &operator << (std::ostream &, const designatort &);

#endif
