// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Goto functions
/// A converted function, including its body.

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_TEMPLATE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTION_TEMPLATE_H

#include <vector>


template <class bodyT>
class goto_function_templatet
{
public:
  bodyT body;
  code_typet type;

  typedef std::vector<irep_idt> parameter_identifierst;
  parameter_identifierst parameter_identifiers;

  bool body_available() const
  {
    return !body.instructions.empty();
  }

  bool is_inlined() const
  {
    return type.get_bool(ID_C_inlined);
  }

  bool is_hidden() const
  {
    return type.get_bool(ID_C_hide);
  }

  void make_hidden()
  {
    type.set(ID_C_hide, true);
  }

  goto_function_templatet()
  {
  }

  void clear()
  {
    body.clear();
    type.clear();
    parameter_identifiers.clear();
  }

  void swap(goto_function_templatet &other)
  {
    body.swap(other.body);
    type.swap(other.type);
    parameter_identifiers.swap(other.parameter_identifiers);
  }

  void copy_from(const goto_function_templatet &other)
  {
    body.copy_from(other.body);
    type=other.type;
    parameter_identifiers=other.parameter_identifiers;
  }

  goto_function_templatet(const goto_function_templatet &)=delete;
  goto_function_templatet &operator=(const goto_function_templatet &)=delete;

  goto_function_templatet(goto_function_templatet &&other):
    body(std::move(other.body)),
    type(std::move(other.type)),
    parameter_identifiers(std::move(other.parameter_identifiers))
  {
  }

  goto_function_templatet &operator=(goto_function_templatet &&other)
  {
    body=std::move(other.body);
    type=std::move(other.type);
    parameter_identifiers=std::move(other.parameter_identifiers);
    return *this;
  }
};

#endif
