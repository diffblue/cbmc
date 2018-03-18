/*******************************************************************\

Module: Expressions in JSON

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON

#ifndef CPROVER_UTIL_JSON_EXPR_H
#define CPROVER_UTIL_JSON_EXPR_H

#include "json.h"
#include "irep.h"

class source_locationt;
class typet;
class exprt;
class constant_exprt;
class namespacet;

class json_exprt
{
public:
  virtual json_objectt operator()(
    const exprt &,
    const namespacet &);

  virtual json_objectt operator()(
    const typet &,
    const namespacet &);

  virtual json_objectt operator()(const source_locationt &);

protected:
  virtual std::string from_constant(const namespacet &, const constant_exprt &);
  virtual std::string from_type(const namespacet &, const typet &);
};

#endif // CPROVER_UTIL_JSON_EXPR_H
