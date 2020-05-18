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
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
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

  void merge_three_way_function_return(
    const ai_domain_baset &function_call,
    const ai_domain_baset &function_start,
    const ai_domain_baset &function_end,
    const namespacet &ns) override;

  bool ai_simplify(
    exprt &condition,
    const namespacet &ns) const override;

  bool is_bottom() const override;
  bool is_top() const override;

  virtual abstract_object_pointert eval(
    const exprt &expr, const namespacet &ns) const
  {
    return abstract_state.eval(expr, ns);
  }

private:
  void transform_function_call(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  bool ignore_function_call_transform(const irep_idt &function_id) const;

  std::vector<irep_idt> get_modified_symbols(
    const variable_sensitivity_domaint &other) const;

  void apply_domain(
    std::vector<symbol_exprt> modified_symbols,
    const variable_sensitivity_domaint &target,
    const namespacet &ns);

  abstract_environmentt abstract_state;

public:
  abstract_object_statisticst gather_statistics(const namespacet &ns) const;
};

template <>
struct get_domain_statisticst<variable_sensitivity_domaint>
{
  abstract_object_statisticst total_statistics = {};
  void
  add_entry(const variable_sensitivity_domaint &domain, const namespacet &ns)
  {
    auto statistics = domain.gather_statistics(ns);
    total_statistics.number_of_interval_abstract_objects +=
      statistics.number_of_interval_abstract_objects;
    total_statistics.number_of_globals += statistics.number_of_globals;
    total_statistics.number_of_single_value_intervals +=
      statistics.number_of_single_value_intervals;
    total_statistics.number_of_constants += statistics.number_of_constants;
    total_statistics.number_of_pointers += statistics.number_of_constants;
    total_statistics.number_of_arrays += statistics.number_of_arrays;
    total_statistics.number_of_structs += statistics.number_of_arrays;
    total_statistics.objects_memory_usage += statistics.objects_memory_usage;
  }

  void print(std::ostream &out) const
  {
    out << "<< Begin Variable Sensitivity Domain Statistics >>\n"
        << "  Memory Usage: "
        << total_statistics.objects_memory_usage.to_string() << '\n'
        << "  Number of structs: " << total_statistics.number_of_structs << '\n'
        << "  Number of arrays: " << total_statistics.number_of_arrays << '\n'
        << "  Number of pointers: " << total_statistics.number_of_pointers
        << '\n'
        << "  Number of constants: " << total_statistics.number_of_constants
        << '\n'
        << "  Number of intervals: "
        << total_statistics.number_of_interval_abstract_objects << '\n'
        << "  Number of single value intervals: "
        << total_statistics.number_of_single_value_intervals << '\n'
        << "  Number of globals: " << total_statistics.number_of_globals << '\n'
        << "<< End Variable Sensitivity Domain Statistics >>\n";
  }
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H
