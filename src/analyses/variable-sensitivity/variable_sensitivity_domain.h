/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

There are different ways of handling arrays, structures, unions and
pointers.  Our existing solution basically ignores them which is
imprecise at best and out-right wrong at worst.  For one project we
needed to do better.  We could have implemented a particular way of
handling them in an existing domain, created a new one with it, etc.
This would work but it means duplicate code and it is is inflexible when
the same person / the next person comes along and says "actually, we
really care about the pointer precision but less so the array so could
you just ...".  Thus the idea was to do this properly:

1. Build a "non-relational domain" and allow the abstractions used for
individual variables to be different.

2. Give the user the option of which abstractions are used for structs,
unions, arrays and pointers.  These are the sensitivity options
discussed above.

3. Have the domain options control which kind of abstractions are used
for the individual values, i.e. constants, intervals, etc.


This is implemented in three parts:

abstract_objectt : The base / interface for abstractions of a single
variable.  The interface for these is effectively create (as top,
bottom, from a constant or copy), transform, merge, convert to constant
if possible.  Child classes add additional bits of interface, for
example array abstractions need a "read element" and a "write element"
method, structures need a "read field" and "write field", etc.  These
objects are intended to be immutable and thus operations tend to produce
pointers.  This is so that we can easily produce copy-on-write maps of
them which we need for scaling and performance.  There are also children
of these for the constant abstraction of one value, the interval
abstraction of one value (to be implemented), etc.

abstract_environment : This contains the map from variable names for
abstract_objectt's (the "non-relational" part of the domain).  The map
itself if copy-on-write for performance and scalability but this is all
wrapped up nicely in @danpoe's sharing_map.  The interface here is
evaluate (exprt -> abstract_objectt*), assign (name, abstract_objectt*
-> bool), assume (exprt -> bool) and merge.  It has a factory to build
abstract_objectt* from types or constants but apart from that, doesn't
know anything about which actual abstract_objectt's are being used.  As
long as program variables that are arrays have an abstract_objectt which
has the array interface, and so on for structs, unions, etc. then the
abstractions used for values can be freely mixed and matched in any way
the user can get the factory to build.

variable_sensitivity_domaint : Implements the ai_domain_baset interface
using an abstract_environment.  The only real code here is the
'transform' method which looks at the instruction type and converts that
into calls to eval, assume, assign and merge.


\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H

#include <map>
#include <memory>
#include <iosfwd>

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>

class variable_sensitivity_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;

  // no states
  virtual void make_bottom() override;

  // all states
  virtual void make_top() override;

  // a reasonable entry-point state
  virtual void make_entry() override;

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;

  void output(std::ostream &out) const;

  virtual bool merge(
    const variable_sensitivity_domaint &b,
    locationt from,
    locationt to);

  bool ai_simplify(
    exprt &condition,
    const namespacet &ns) const override;

  bool is_bottom() const override;
  bool is_top() const override;

  virtual std::vector<symbol_exprt> get_modified_symbols(const variable_sensitivity_domaint &other) const
  {
    return abstract_environmentt::modified_symbols(abstract_state, other.abstract_state);
  }

  virtual void restore_domain(std::vector<symbol_exprt> modified_symbols,  
    variable_sensitivity_domaint &target, const namespacet &ns) const;

private:
  void transform_function_call(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  bool ignore_function_call_transform(const irep_idt &function_id) const;

  abstract_environmentt abstract_state;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H
