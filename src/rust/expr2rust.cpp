/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#include "expr2rust.h"

#include <ansi-c/expr2c_class.h>

class expr2rustt : public expr2ct
{
public:
  explicit expr2rustt(const namespacet &_ns) : expr2ct(_ns)
  {
  }

protected:
};

std::string expr2rust(const exprt &expr, const namespacet &ns)
{
  expr2rustt expr2rust(ns);
  expr2rust.get_shorthands(expr);
  return expr2rust.convert(expr);
}

std::string type2rust(const typet &type, const namespacet &ns)
{
  expr2rustt expr2rust(ns);
  return expr2rust.convert(type);
}
