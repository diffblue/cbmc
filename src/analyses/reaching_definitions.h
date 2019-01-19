/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

/// \file
/// Range-based reaching definitions analysis (following Field- Sensitive
///   Program Dependence Analysis, Litvak et al., FSE 2010)
///
/// This module implements the reaching definitions data-flow analysis
/// (see https://en.wikipedia.org/wiki/Reaching_definition for basic
/// introduction) on multi-threaded GOTO programs.
///
/// The domain element is defined in a class `rd_range_domaint` and the actual
/// analysis is implemented in a class `reaching_definitions_analysist`. Beside
/// these classes there are more data structures necessary in the computation.
/// We discuss all of them in the following sub-sections.

#ifndef CPROVER_ANALYSES_REACHING_DEFINITIONS_H
#define CPROVER_ANALYSES_REACHING_DEFINITIONS_H

#include <util/base_exceptions.h>
#include <util/threeval.h>

#include "ai.h"
#include "goto_rw.h"

class value_setst;
class is_threadedt;
class dirtyt;
class reaching_definitions_analysist;

/// An instance of this class provides an assignment of unique numeric `ID` to
/// each inserted `reaching_definitiont` instance.
/// Requirement: V has a member "identifier" of type irep_idt
template<typename V>
class sparse_bitvector_analysist
{
public:
  const V &get(const std::size_t value_index) const
  {
    assert(value_index<values.size());
    return values[value_index]->first;
  }

  std::size_t add(const V &value)
  {
    inner_mapt &m=value_map[value.identifier];

    std::pair<typename inner_mapt::iterator, bool> entry=
      m.insert(std::make_pair(value, values.size()));

    if(entry.second)
      values.push_back(entry.first);

    return entry.first->second;
  }

  void clear()
  {
    value_map.clear();
    values.clear();
  }

protected:
  typedef typename std::map<V, std::size_t> inner_mapt;
  /// It is a map from an `ID` to the corresponding `reaching_definitiont`
  /// instance inside the map `value_map`. Namely, the map is implemented as an
  /// `std::vector` of iterators to elements of the map `value_map`. An index to
  /// this vector is the `ID` of the related `reaching_definitiont` instance.
  std::vector<typename inner_mapt::const_iterator> values;
  /// A map from names of program variables to a set of pairs
  /// (`reaching_definitiont`, `ID`). Formally, the map is defined as
  /// `value_map: var_names -> (reaching_definitiont -> ID)`.
  std::unordered_map<irep_idt, inner_mapt> value_map;
};

/// Identifies a GOTO instruction where a given variable is defined (i.e. it is
/// set to a certain value). It consists of these data:
struct reaching_definitiont
{
  /// The name of the variable which was defined.
  irep_idt identifier;
  /// The iterator to the GOTO instruction where the variable has been written
  /// to.
  ai_domain_baset::locationt definition_at;
  /// The two integers below define a range of bits (i.e. the begin and end bit
  /// indices) which represent the value of the variable. So, the integers
  /// represents the half-open interval `[bit_begin, bit_end)` of bits.
  /// However, `bit_end` can also be set a special value `-1`, which means
  /// infinite/unknown index.
  range_spect bit_begin;
  range_spect bit_end;
};

/// In order to use instances of this structure as keys in ordered containers,
/// such as std::map, an ordering is defined.
inline bool operator<(
  const reaching_definitiont &a,
  const reaching_definitiont &b)
{
  if(a.definition_at<b.definition_at)
    return true;
  if(b.definition_at<a.definition_at)
    return false;

  if(a.bit_begin<b.bit_begin)
    return true;
  if(b.bit_begin<a.bit_begin)
    return false;

  if(a.bit_end<b.bit_end)
    return true;
  if(b.bit_end<a.bit_end)
    return false;

  // we do not expect comparison of unrelated definitions
  // as this operator< is only used in sparse_bitvector_analysist
  assert(a.identifier==b.identifier);

  return false;
}

/// Because the class is inherited from `ai_domain_baset`, its instance
/// represents an element of a domain of the reaching definitions abstract
/// interpretation analysis. Each instance is thus associated with exactly one
/// instruction in an analysed GOTO program. And so, the instance holds
/// information for individual program variables about their reaching
/// definitions, at that instruction.
class rd_range_domaint:public ai_domain_baset
{
public:
  rd_range_domaint():
    ai_domain_baset(),
    has_values(false),
    bv_container(nullptr)
  {
  }

  void set_bitvector_container(
    sparse_bitvector_analysist<reaching_definitiont> &_bv_container)
  {
    bv_container=&_bv_container;
  }

  /// Computes an instance obtained from the instance `*this` by transformation
  /// over a GOTO instruction referenced by `from`. The method implements a
  /// switch according to a type of the instruction and then calls a dedicated
  /// `transform_*` method for the recognised instruction.
  /// \param function_from: Just passed to `transform_function_call` and
  ///   `transform_end_function` callees.
  /// \param from: Reference to a GOTO instruction according to which `*this`
  ///   instance should be transformed.
  /// \param function_to: Just passed to `transform_function_call` callee.
  /// \param to: Just passed to `transform_end_function` callee.
  /// \param ai: A reference to 'reaching_definitions_analysist' instance.
  /// \param ns: Just passed to callees.
  void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final override;

  void output(
    std::ostream &out,
    const ai_baset &,
    const namespacet &) const final override
  {
    output(out);
  }

  void make_top() final override
  {
    values.clear();
    if(bv_container)
      bv_container->clear();
    has_values=tvt(true);
  }

  void make_bottom() final override
  {
    values.clear();
    if(bv_container)
      bv_container->clear();
    has_values=tvt(false);
  }

  void make_entry() final override
  {
    make_top();
  }

  bool is_top() const override final
  {
    DATA_INVARIANT(!has_values.is_true() || values.empty(),
                   "If domain is top, the value map must be empty");
    return has_values.is_true();
  }

  bool is_bottom() const override final
  {
    DATA_INVARIANT(!has_values.is_false() || values.empty(),
                   "If domain is bottom, the value map must be empty");
    return has_values.is_false();
  }

  /// Implements the `join` operation of two instances `*this` and other`. It
  /// operates only on `this->values` and `other.values`. The keys in the
  /// resulting map is the union of variable names in both `this->values` and
  /// `other.values`. And for each variable `v` appearing in both maps
  /// `this->values` and `other.values` the resulting mapped set
  /// of `ID`s is the set union of `this->values[v]` and `other.values[v]`.
  /// NOTE: The operation actually does not produce a new `join` element. The
  /// instance `*this` is modified to become the `join` element.
  /// \param other: The instance to be merged into `*this` as the join operation
  /// \param from: Not used at all.
  /// \param to: Not used at all.
  /// \return Returns true iff there is something new
  bool merge(
    const rd_range_domaint &other,
    locationt from,
    locationt to);

  bool merge_shared(
    const rd_range_domaint &other,
    locationt from,
    locationt to,
    const namespacet &ns);

  // each element x represents a range of bits [x.first, x.second)
  typedef std::multimap<range_spect, range_spect> rangest;
  typedef std::map<locationt, rangest> ranges_at_loct;

  const ranges_at_loct &get(const irep_idt &identifier) const;
  void clear_cache(const irep_idt &identifier) const
  {
    export_cache[identifier].clear();
  }

private:
  /// This (three value logic) flag determines, whether the instance represents
  /// `top`, `bottom`, or any other element of the lattice, by values `TRUE`,
  /// `FALSE`, and `UNKNOWN` respectively. Initially it is set to `FALSE`.
  tvt has_values;

  /// It points to the actual reaching definitions data of individual program
  /// variables. This pointer is initially `nullptr` and it is later set (by
  /// `reaching_definitions_analysist` instance using the method
  /// `set_bitvector_container`) to a valid pointer, which is actually shared by
  /// all `rd_range_domaint` instances. NOTE: `reaching_definitions_analysist`
  /// inherits from `sparse_bitvector_analysist<reaching_definitiont>` and so
  /// `this` is passed to `set_bitvector_container` for all instances.
  sparse_bitvector_analysist<reaching_definitiont> *bv_container;

  typedef std::set<std::size_t> values_innert;
  #ifdef USE_DSTRING
  typedef std::map<irep_idt, values_innert> valuest;
  #else
  typedef std::unordered_map<irep_idt, values_innert> valuest;
  #endif
  /// It is an ordered map from program variable names to `ID`s of
  /// `reaching_definitiont` instances stored in map pointed to by
  /// `bv_container`. The map is not empty only if `has_value` is `UNKNOWN`.
  /// Variables in the map are all those which are live at the associated
  /// instruction.
  valuest values;

  #ifdef USE_DSTRING
  typedef std::map<irep_idt, ranges_at_loct> export_cachet;
  #else
  typedef std::unordered_map<irep_idt, ranges_at_loct> export_cachet;
  #endif
  /// It is a helper data structure. It consists of data already stored in
  /// `values` and `bv_container`. It is basically (an ordered) map from (a
  /// subset of) variables in `values` to iterators to GOTO instructions where
  /// the variables are defined. Moreover, each such iterator is also
  /// associated with a range of bits defining the value of that variable at
  /// that GOTO instruction. Both the iterators and the corresponding bit ranges
  /// are simply taken from `reaching_definitiont` instances obtained for `ID`s
  /// in `values[var_name]`. This data structure is actually used only in the
  /// `output` method; other methods only remove outdated data from it. Since
  /// the cache does not contribute to the computation, it should be either
  /// moved to the `output` method or removed entirely.
  mutable export_cachet export_cache;

  void populate_cache(const irep_idt &identifier) const;

  void transform_dead(
    const namespacet &ns,
    locationt from);
  void transform_start_thread(
    const namespacet &ns,
    reaching_definitions_analysist &rd);
  void transform_function_call(
    const namespacet &ns,
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    reaching_definitions_analysist &rd);
  void transform_end_function(
    const namespacet &ns,
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    reaching_definitions_analysist &rd);
  void transform_assign(
    const namespacet &ns,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    reaching_definitions_analysist &rd);

  void kill(
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);
  void kill_inf(
    const irep_idt &identifier,
    const range_spect &range_start);
  bool gen(
    locationt from,
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);

  void output(std::ostream &out) const;

  bool merge_inner(
    values_innert &dest,
    const values_innert &other);
};

class reaching_definitions_analysist:
  public concurrency_aware_ait<rd_range_domaint>,
  public sparse_bitvector_analysist<reaching_definitiont>
{
public:
  // constructor
  explicit reaching_definitions_analysist(const namespacet &_ns);

  virtual ~reaching_definitions_analysist();

  void initialize(const goto_functionst &goto_functions) override;

  statet &get_state(locationt l) override
  {
    statet &s=concurrency_aware_ait<rd_range_domaint>::get_state(l);

    rd_range_domaint *rd_state=dynamic_cast<rd_range_domaint*>(&s);
    INVARIANT_STRUCTURED(
      rd_state!=nullptr,
      bad_cast_exceptiont,
      "rd_state has type rd_range_domaint");

    rd_state->set_bitvector_container(*this);

    return s;
  }

  value_setst &get_value_sets() const
  {
    assert(value_sets);
    return *value_sets;
  }

  const is_threadedt &get_is_threaded() const
  {
    assert(is_threaded);
    return *is_threaded;
  }

  const dirtyt &get_is_dirty() const
  {
    assert(is_dirty);
    return *is_dirty;
  }

protected:
  const namespacet &ns;
  std::unique_ptr<value_setst> value_sets;
  std::unique_ptr<is_threadedt> is_threaded;
  std::unique_ptr<dirtyt> is_dirty;
};

#endif // CPROVER_ANALYSES_REACHING_DEFINITIONS_H
