/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_LINKAGE_SPEC_H
#define CPROVER_CPP_CPP_LINKAGE_SPEC_H

class cpp_linkage_spect:public exprt
{
public:
  cpp_linkage_spect():exprt(ID_cpp_linkage_spec)
  {
  }

  using itemst = std::vector<class cpp_itemt>;

  const itemst &items() const
  {
    return (const itemst &)operands();
  }

  itemst &items()
  {
    return (itemst &)operands();
  }

  irept &linkage()
  {
    return add(ID_linkage);
  }

  const irept &linkage() const
  {
    return find(ID_linkage);
  }
};

#endif // CPROVER_CPP_CPP_LINKAGE_SPEC_H
