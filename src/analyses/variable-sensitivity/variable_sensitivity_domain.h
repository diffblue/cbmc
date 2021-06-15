/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// There are different ways of handling arrays, structures, unions and
/// pointers.  interval_domaint and constant_propagator_domaint
/// basically ignores them which is imprecise at best and out-right
/// wrong at worst.  For one project we needed to do better.  We could
/// have implemented a particular way of handling them in an existing
/// domain, created a new one with it, etc.  This would work but it
/// means duplicate code and it is is inflexible when the same person
/// / the next person comes along and says "actually, we really care
/// about the pointer precision but less so the array so could you
/// just ...".  Thus the idea was to do this properly:
///
/// 1. Build a "non-relational domain" and allow the abstractions used for
/// individual variables to be different.
///
/// 2. Give the user the option of which abstractions are used for structs,
/// unions, arrays and pointers.  These are the sensitivity options
/// discussed above.
///
/// 3. Have the domain options control which kind of abstractions are used
/// for the individual values, i.e. constants, intervals, etc.
///
///
/// This is implemented in three parts:
///
/// abstract_objectt : The base / interface for abstractions of a single
/// variable.  The interface for these is effectively create (as top,
/// bottom, from a constant or copy), transform, merge, convert to constant
/// if possible.  Child classes add additional bits of interface, for
/// example array abstractions need a "read element" and a "write element"
/// method, structures need a "read field" and "write field", etc.  These
/// objects are intended to be immutable and thus operations tend to produce
/// pointers.  This is so that we can easily produce copy-on-write maps of
/// them which we need for scaling and performance.  There are also children
/// of these for the constant abstraction of one value, the interval
/// abstraction of one value (to be implemented), etc.
///
/// abstract_environment : This contains the map from variable names for
/// abstract_objectt's (the "non-relational" part of the domain).  The map
/// itself if copy-on-write for performance and scalability but this is all
/// wrapped up nicely in danpoe's sharing_map.  The interface here is
/// evaluate (exprt -> abstract_objectt*), assign (name, abstract_objectt*
/// -> bool), assume (exprt -> bool) and merge.  It has a factory to build
/// abstract_objectt* from types or constants but apart from that, doesn't
/// know anything about which actual abstract_objectt's are being used.  As
/// long as program variables that are arrays have an abstract_objectt which
/// has the array interface, and so on for structs, unions, etc. then the
/// abstractions used for values can be freely mixed and matched in any way
/// the user can get the factory to build.
///
/// variable_sensitivity_domaint : Implements the ai_domain_baset interface
/// using an abstract_environment.  The only real code here is the
/// 'transform' method which looks at the instruction type and converts that
/// into calls to eval, assume, assign and merge.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H

#include <iosfwd>
#include <memory>

#include <analyses/ai_domain.h>
#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/variable_sensitivity_configuration.h>

#define OPT_VSD                                                                \
  "(vsd-values):"                                                              \
  "(vsd-structs):"                                                             \
  "(vsd-arrays):"                                                              \
  "(vsd-pointers):"                                                            \
  "(vsd-unions):"                                                              \
  "(vsd-flow-insensitive)"                                                     \
  "(vsd-data-dependencies)"

// clang-format off
#define HELP_VSD \
    " --vsd-values                 value tracking - constants|intervals|set-of-constants\n" /* NOLINT(whitespace/line_length) */ \
    " --vsd-structs                struct field sensitive analysis - top-bottom|every-field\n" /* NOLINT(whitespace/line_length) */ \
    " --vsd-arrays                 array entry sensitive analysis - top-bottom|every-element\n" /* NOLINT(whitespace/line_length) */ \
    " --vsd-pointers               pointer sensitive analysis - top-bottom|constants|value-set\n" /* NOLINT(whitespace/line_length) */ \
    " --vsd-unions                 union sensitive analysis - top-bottom\n" \
    " --vsd-flow-insensitive       disables flow sensitivity\n" \
    " --vsd-data-dependencies      track data dependencies\n" \

// cland-format on

#define PARSE_OPTIONS_VSD(cmdline, options) \
  options.set_option("values", cmdline.get_value("vsd-values")); \
  options.set_option("pointers", cmdline.get_value("vsd-pointers")); \
  options.set_option("arrays", cmdline.get_value("vsd-arrays")); \
  options.set_option("structs", cmdline.get_value("vsd-structs")); \
  options.set_option("unions", cmdline.get_value("vsd-unions")); \
  options.set_option("flow-insensitive", cmdline.isset("vsd-flow-insensitive")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("data-dependencies", cmdline.isset("vsd-data-dependencies")); /* NOLINT(whitespace/line_length) */ \
  (void)0

class variable_sensitivity_domaint : public ai_domain_baset
{
public:
  explicit variable_sensitivity_domaint(
    variable_sensitivity_object_factory_ptrt _object_factory,
    const vsd_configt &_configuration)
    : abstract_state(_object_factory),
      flow_sensitivity(_configuration.flow_sensitivity)
  {
  }

  /// Compute the abstract transformer for a single instruction
  ///
  /// \param function_from: the name of the function containing from
  /// \param trace_from: the instruction before the abstract domain
  /// \param function_to: the name of the function containing to
  /// \param trace_to: the instruction after the abstract domain
  /// \param ai: the abstract interpreter
  /// \param ns: the namespace
  void transform(
    const irep_idt &function_from,
    trace_ptrt trace_from,
    const irep_idt &function_to,
    trace_ptrt trace_to,
    ai_baset &ai,
    const namespacet &ns) override;

  /// Sets the domain to bottom (no states / unreachable).
  void make_bottom() override;

  /// Sets the domain to top (all states).
  void make_top() override;

  /// Set up a reasonable entry-point state
  void make_entry() override;

  /// Basic text output of the abstract domain
  ///
  /// \param out: the output stream
  /// \param ai: the abstract interpreter
  /// \param ns: the namespace
  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

  void output(std::ostream &out) const;

  /// Computes the join between "this" and "b".
  ///
  /// \param b: the other domain
  /// \param from: it's preceding location
  /// \param to: it's current location
  ///
  /// \return true if something has changed.
  virtual bool
  merge(const variable_sensitivity_domaint &b, trace_ptrt from, trace_ptrt to);

  /// Perform a context aware merge of the changes that have been applied
  /// between function_start and the current state. Anything that has not been
  /// modified will be taken from the \p function_call domain.
  /// \param function_call: The local of the merge - values from here will be
  ///   taken if they have not been modified
  /// \param function_start: The base of the merge - changes that have been made
  ///   between here and the end will be retained.
  /// \param function_end: The end of the merge - changes that have been made
  ///   between the start and here will be retained.
  /// \param ns: The global namespace
  virtual void merge_three_way_function_return(
    const ai_domain_baset &function_call,
    const ai_domain_baset &function_start,
    const ai_domain_baset &function_end,
    const namespacet &ns);

  /// Use the information in the domain to simplify the expression
  /// with respect to the current location.  This may be able to
  /// reduce some values to constants.
  ///
  /// \param condition: the expression to simplify
  /// \param ns: the namespace
  ///
  /// \return True if no simplification was made
  bool ai_simplify(exprt &condition, const namespacet &ns) const override;

  /// Find out if the domain is currently unreachable.
  ///
  /// \return True if the domain is bottom (i.e. unreachable).
  bool is_bottom() const override;

  /// Is the domain completely top at this state
  ///
  /// \return True if the domain is top
  bool is_top() const override;

  virtual abstract_object_pointert
  eval(const exprt &expr, const namespacet &ns) const
  {
    return abstract_state.eval(expr, ns);
  }

private:
  /// Used by variable_sensitivity_domaint::transform to handle
  /// FUNCTION_CALL transforms. This is copying the values of the arguments
  /// into new symbols corresponding to the declared parameter names.
  ///
  /// If the function call is opaque we currently top the return value
  /// and the value of any things whose address is passed into the function.
  ///
  /// \param from: the location to transform from which is a function call
  /// \param to: the destination of the transform
  ///            (potentially inside the function call)
  /// \param ai: the abstract interpreter
  /// \param ns: the namespace of the current state
  void transform_function_call(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  /// Used to specify which CPROVER internal functions should be skipped
  /// over when doing function call transforms
  ///
  /// \param function_id: the name of the function being called
  ///
  /// \return Returns true if the function should be ignored
  bool ignore_function_call_transform(const irep_idt &function_id) const;

  /// Get symbols that have been modified since this domain and other
  /// \param other: The domain that things may have been modified in
  /// \return A list of symbols whose write location is different
  std::vector<irep_idt>
  get_modified_symbols(const variable_sensitivity_domaint &other) const;

  /// Given a domain and some symbols, apply those symbols values
  /// to the current domain
  /// \param modified_symbols: The symbols to write
  /// \param target: The domain to take the values from
  /// \param ns: The global namespace
  void apply_domain(
    std::vector<symbol_exprt> modified_symbols,
    const variable_sensitivity_domaint &target,
    const namespacet &ns);

  void assume(exprt expr, namespacet ns);

  abstract_environmentt abstract_state;
  flow_sensitivityt flow_sensitivity;

#ifdef ENABLE_STATS
public:
  abstract_object_statisticst gather_statistics(const namespacet &ns) const;
#endif
};

class variable_sensitivity_domain_factoryt
  : public ai_domain_factoryt<variable_sensitivity_domaint>
{
public:
  explicit variable_sensitivity_domain_factoryt(
    variable_sensitivity_object_factory_ptrt _object_factory,
    const vsd_configt &_configuration)
    : object_factory(_object_factory), configuration(_configuration)
  {
  }

  std::unique_ptr<statet> make(locationt l) const override
  {
    auto d = util_make_unique<variable_sensitivity_domaint>(
      object_factory, configuration);
    CHECK_RETURN(d->is_bottom());
    return std::unique_ptr<statet>(d.release());
  }

private:
  variable_sensitivity_object_factory_ptrt object_factory;
  const vsd_configt configuration;
};

#ifdef ENABLE_STATS
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
#endif

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H
