/*******************************************************************\

Module: Lint Examples

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

// clang-format off
class temp_classt : public base_classt
{}

class another_class: public base_classt
{}

class more_class: public base_classt
{}

class nonderived
{}

class nonderivedt
{}

#define ID_property_class dstring(23, 0)

int foo(class define);

int foo(class definet);

template <class U>
void bar(U t);

template<class U>
void bar(U t);

template < class U >
void bar(U t);

class testt
{
  template<class U>
  void bar(U t);
}
// clang-format on
