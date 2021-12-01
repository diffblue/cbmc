/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_IREP_H
#define CPROVER_UTIL_IREP_H

#include <string>
#include <vector>

#include "invariant.h"
#include "irep_ids.h"

#define SHARING
#ifndef HASH_CODE
#  define HASH_CODE 1
#endif
// use forward_list by default, unless _GLIBCXX_DEBUG is set as the debug
// overhead is noticeably higher with the regression test suite taking four
// times as long.
#if !defined(NAMED_SUB_IS_FORWARD_LIST) && !defined(_GLIBCXX_DEBUG)
#  define NAMED_SUB_IS_FORWARD_LIST 1
#endif

#if NAMED_SUB_IS_FORWARD_LIST
#  include "forward_list_as_map.h"
#else
#include <map>
#endif

#ifdef USE_DSTRING
typedef dstringt irep_idt;
// NOLINTNEXTLINE(readability/identifiers)
typedef dstring_hash irep_id_hash;
#else
#include "string_hash.h"
typedef std::string irep_idt;
// NOLINTNEXTLINE(readability/identifiers)
typedef string_hash irep_id_hash;
#endif

inline const std::string &id2string(const irep_idt &d)
{
  #ifdef USE_DSTRING
  return as_string(d);
  #else
  return d;
  #endif
}

#ifdef IREP_DEBUG
#include <iostream>
#endif

class irept;
const irept &get_nil_irep();

/// Used in tree_nodet for activating or not reference counting.
/// tree_nodet uses inheritance from ref_count_ift instead of a field, so that
/// it gets deleted if empty ([[no_unique_address]] only appears in C++20).
template <bool enabled>
struct ref_count_ift
{
};

template <>
struct ref_count_ift<true>
{
  unsigned ref_count = 1;
};

/// A node with data in a tree, it contains:
///
/// * \ref irept::dt::data : A string (Unless `USE_STD_STRING` is set, this is
///   actually a \ref dstringt and thus an integer which is a reference into a
///   string table.)
///
/// * \ref irept::dt::named_sub : A map from `irep_idt` (a string) to \ref
///   irept. This is used for named children, i.e.  subexpressions, parameters,
///   etc. Children whose name begins with '#' are ignored by the
///   default \ref operator==.
///
/// * \ref irept::dt::sub : A vector of \ref irept which is used to store
///   ordered but unnamed children.
///
/// * \c ref_count : if sharing is activated, this is used to count the number
///   of references to a node.
///
/// * \c hash_code : if HASH_CODE is activated, this is used to cache the
///   result of the hash function.
template <typename treet, typename named_subtreest, bool sharing = true>
class tree_nodet : public ref_count_ift<sharing>
{
public:
  // These are not stable.
  typedef std::vector<treet> subt;

  // named_subt has to provide stable references; we can
  // use std::forward_list or std::vector< unique_ptr<T> > to save
  // memory and increase efficiency.
  using named_subt = named_subtreest;

  friend treet;

  /// This irep_idt is the only place to store data in an tree node
  irep_idt data;

  named_subt named_sub;
  subt sub;

#if HASH_CODE
  mutable std::size_t hash_code = 0;
#endif

  void clear()
  {
    data.clear();
    sub.clear();
    named_sub.clear();
#if HASH_CODE
    hash_code = 0;
#endif
  }

  void swap(tree_nodet &d)
  {
    d.data.swap(data);
    d.sub.swap(sub);
    d.named_sub.swap(named_sub);
#if HASH_CODE
    std::swap(d.hash_code, hash_code);
#endif
  }

  tree_nodet() = default;

  explicit tree_nodet(irep_idt _data) : data(std::move(_data))
  {
  }

  tree_nodet(irep_idt _data, named_subt _named_sub, subt _sub)
    : data(std::move(_data)),
      named_sub(std::move(_named_sub)),
      sub(std::move(_sub))
  {
  }
};

/// Base class for tree-like data structures with sharing
template <typename derivedt, typename named_subtreest>
class sharing_treet
{
public:
  using dt = tree_nodet<derivedt, named_subtreest, true>;
  using subt = typename dt::subt;
  using named_subt = typename dt::named_subt;

  /// Used to refer to this class from derived classes
  using tree_implementationt = sharing_treet;

  explicit sharing_treet(irep_idt _id) : data(new dt(std::move(_id)))
  {
  }

  sharing_treet(irep_idt _id, named_subt _named_sub, subt _sub)
    : data(new dt(std::move(_id), std::move(_named_sub), std::move(_sub)))
  {
  }

  // constructor for blank irep
  sharing_treet() : data(&empty_d)
  {
  }

  // copy constructor
  sharing_treet(const sharing_treet &irep) : data(irep.data)
  {
    if(data!=&empty_d)
    {
      PRECONDITION(data->ref_count != 0);
      data->ref_count++;
#ifdef IREP_DEBUG
      std::cout << "COPY " << data << " " << data->ref_count << '\n';
#endif
    }
  }

  // Copy from rvalue reference.
  // Note that this does avoid a branch compared to the
  // standard copy constructor above.
  sharing_treet(sharing_treet &&irep) : data(irep.data)
  {
#ifdef IREP_DEBUG
    std::cout << "COPY MOVE\n";
#endif
    irep.data=&empty_d;
  }

  sharing_treet &operator=(const sharing_treet &irep)
  {
#ifdef IREP_DEBUG
    std::cout << "ASSIGN\n";
#endif

    // Ordering is very important here!
    // Consider self-assignment, which may destroy 'irep'
    dt *irep_data=irep.data;
    if(irep_data!=&empty_d)
      irep_data->ref_count++;

    remove_ref(data); // this may kill 'irep'
    data=irep_data;

    return *this;
  }

  // Note that the move assignment operator does avoid
  // three branches compared to standard operator above.
  sharing_treet &operator=(sharing_treet &&irep)
  {
#ifdef IREP_DEBUG
    std::cout << "ASSIGN MOVE\n";
#endif
    // we simply swap two pointers
    std::swap(data, irep.data);
    return *this;
  }

  ~sharing_treet()
  {
    remove_ref(data);
  }

protected:
  dt *data;
  static dt empty_d;

  static void remove_ref(dt *old_data);
  static void nonrecursive_destructor(dt *old_data);
  void detach();

public:
  const dt &read() const
  {
    return *data;
  }

  dt &write()
  {
    detach();
#if HASH_CODE
    data->hash_code = 0;
#endif
    return *data;
  }
};

// Static field initialization
template <typename derivedt, typename named_subtreest>
typename sharing_treet<derivedt, named_subtreest>::dt
  sharing_treet<derivedt, named_subtreest>::empty_d;

/// Base class for tree-like data structures without sharing
template <typename derivedt, typename named_subtreest>
class non_sharing_treet
{
public:
  using dt = tree_nodet<derivedt, named_subtreest, false>;
  using subt = typename dt::subt;
  using named_subt = typename dt::named_subt;

  /// Used to refer to this class from derived classes
  using tree_implementationt = non_sharing_treet;

  explicit non_sharing_treet(irep_idt _id) : data(std::move(_id))
  {
  }

  non_sharing_treet(irep_idt _id, named_subt _named_sub, subt _sub)
    : data(std::move(_id), std::move(_named_sub), std::move(_sub))
  {
  }

  non_sharing_treet() = default;

  const dt &read() const
  {
    return data;
  }

  dt &write()
  {
#if HASH_CODE
    data.hash_code = 0;
#endif
    return data;
  }

protected:
  dt data;
};

/// There are a large number of kinds of tree structured or tree-like data in
/// CPROVER. \ref irept provides a single, unified representation for all of
/// these, allowing structure sharing and reference counting of data. As
/// such \ref irept is the basic unit of data in CPROVER.  Each \ref irept
/// contains (or references, if reference counted data sharing is enabled, as
/// it is by default - see the `SHARING` macro) to a node (see \ref tree_nodet).
/// The \ref irept::pretty function outputs the explicit tree structure of
/// an \ref irept and can be used to understand and debug problems with
/// `irept`s.
///
/// On their own `irept`s do not "mean" anything; they are effectively
/// generic tree nodes. Their interpretation depends on the contents of
/// result of the \ref id() function, i.e. the `data` field. `util/irep_ids.def`
/// contains a list of `id` values. During the build process it is used
/// to generate `util/irep_ids.h` which gives constants for each id
/// (named `ID_`). You can also make `irep_idt`s which do not come from
/// `util/irep_ids.def`. An `irep_idt` can then be used to identify what
/// kind of data the \ref irept stores and thus what can be done with it.
///
/// To simplify this process, there are a variety of classes that inherit
/// from \ref irept, roughly corresponding to the ids listed (i.e. `ID_or`
/// (the string "or”) corresponds to the class \ref or_exprt). These give
/// semantically relevant accessor functions for the data; effectively
/// different APIs for the same underlying data structure. None of these
/// classes add fields (only methods) and so static casting can be used. The
/// inheritance graph of the subclasses of \ref irept is a useful starting
/// point for working out how to manipulate data.
///
/// There are three main groups of classes (or APIs); those derived from
/// \ref typet, \ref codet and \ref exprt respectively. Although all of these
/// inherit from \ref irept, these are the most abstract level that code should
/// handle data. If code is manipulating plain `irept`s then something is wrong
/// with the architecture of the code.
///
/// Many of the key descendants of \ref exprt are declared in \ref std_expr.h.
/// All expressions have a named subexpression with ID "type", which gives the
/// type of the expression (slightly simplified from C/C++ as \ref
/// unsignedbv_typet, \ref signedbv_typet, \ref floatbv_typet, etc.). All type
/// conversions are explicit with a \ref typecast_exprt. One key descendant of
/// \ref exprt is \ref symbol_exprt which creates \ref irept instances with ID
/// “symbol”. These are used to represent variables; the name of which can be
/// found using the `get_identifier` accessor function.
///
/// \ref codet inherits from \ref exprt and is defined in `std_code.h`. It
/// represents executable code; statements in a C-like language rather than
/// expressions. In the front-end there are versions of these that hold
/// whole code blocks, but in goto-programs these have been flattened so
/// that each \ref irept represents one sequence point (almost one line of
/// code / one semi-colon). The most common descendant of \ref codet is
/// \ref code_assignt so a common pattern is to cast the \ref codet to an
/// assignment and then recurse on the expression on either side.
class irept
#ifdef SHARING
  : public sharing_treet<
      irept,
#else
  : public non_sharing_treet<
      irept,
#endif
#if NAMED_SUB_IS_FORWARD_LIST
      forward_list_as_mapt<irep_idt, irept>>
#else
      std::map<irep_idt, irept>>
#endif
{
public:
  using baset = tree_implementationt;

  bool is_nil() const
  {
    return id() == ID_nil;
  }
  bool is_not_nil() const
  {
    return id() != ID_nil;
  }

  explicit irept(const irep_idt &_id) : baset(_id)
  {
  }

  irept(const irep_idt &_id, const named_subt &_named_sub, const subt &_sub)
    : baset(_id, _named_sub, _sub)
  {
  }

  irept() = default;

  const irep_idt &id() const
  { return read().data; }

  const std::string &id_string() const
  { return id2string(read().data); }

  void id(const irep_idt &_data)
  { write().data=_data; }

  const irept &find(const irep_idt &name) const;
  irept &add(const irep_idt &name);
  irept &add(const irep_idt &name, irept irep);

  const std::string &get_string(const irep_idt &name) const
  {
    return id2string(get(name));
  }

  const irep_idt &get(const irep_idt &name) const;
  bool get_bool(const irep_idt &name) const;
  signed int get_int(const irep_idt &name) const;
  std::size_t get_size_t(const irep_idt &name) const;
  long long get_long_long(const irep_idt &name) const;

  void set(const irep_idt &name, const irep_idt &value)
  {
    add(name, irept(value));
  }
  void set(const irep_idt &name, irept irep)
  {
    add(name, std::move(irep));
  }
  void set(const irep_idt &name, const long long value);
  void set_size_t(const irep_idt &name, const std::size_t value);

  void remove(const irep_idt &name);
  void move_to_sub(irept &irep);
  void move_to_named_sub(const irep_idt &name, irept &irep);

  bool operator==(const irept &other) const;

  bool operator!=(const irept &other) const
  {
    return !(*this==other);
  }

  void swap(irept &irep)
  {
    std::swap(irep.data, data);
  }

  bool operator<(const irept &other) const;
  bool ordering(const irept &other) const;

  int compare(const irept &i) const;

  void clear() { *this=irept(); }

  void make_nil() { *this=get_nil_irep(); }

  subt &get_sub() { return write().sub; } // DANGEROUS
  const subt &get_sub() const { return read().sub; }
  named_subt &get_named_sub() { return write().named_sub; } // DANGEROUS
  const named_subt &get_named_sub() const { return read().named_sub; }

  std::size_t hash() const;
  std::size_t full_hash() const;

  bool full_eq(const irept &other) const;

  std::string pretty(unsigned indent=0, unsigned max_indent=0) const;

  static bool is_comment(const irep_idt &name)
  { return !name.empty() && name[0]=='#'; }

  /// count the number of named_sub elements that are not comments
  static std::size_t number_of_non_comments(const named_subt &);
};

// NOLINTNEXTLINE(readability/identifiers)
struct irep_hash
{
  std::size_t operator()(const irept &irep) const
  {
    return irep.hash();
  }
};

// NOLINTNEXTLINE(readability/identifiers)
struct irep_full_hash
{
  std::size_t operator()(const irept &irep) const
  {
    return irep.full_hash();
  }
};

// NOLINTNEXTLINE(readability/identifiers)
struct irep_full_eq
{
  bool operator()(const irept &i1, const irept &i2) const
  {
    return i1.full_eq(i2);
  }
};

struct irep_pretty_diagnosticst
{
  const irept &irep;
  explicit irep_pretty_diagnosticst(const irept &irep);
};

template <>
struct diagnostics_helpert<irep_pretty_diagnosticst>
{
  static std::string diagnostics_as_string(const irep_pretty_diagnosticst &irep)
  {
    return irep.irep.pretty();
  }
};

template <typename derivedt, typename named_subtreest>
void sharing_treet<derivedt, named_subtreest>::detach()
{
#ifdef IREP_DEBUG
  std::cout << "DETACH1: " << data << '\n';
#endif

  if(data == &empty_d)
  {
    data = new dt;

#ifdef IREP_DEBUG
    std::cout << "ALLOCATED " << data << '\n';
#endif
  }
  else if(data->ref_count > 1)
  {
    dt *old_data(data);
    data = new dt(*old_data);

#ifdef IREP_DEBUG
    std::cout << "ALLOCATED " << data << '\n';
#endif

    data->ref_count = 1;
    remove_ref(old_data);
  }

  POSTCONDITION(data->ref_count == 1);

#ifdef IREP_DEBUG
  std::cout << "DETACH2: " << data << '\n';
#endif
}

template <typename derivedt, typename named_subtreest>
void sharing_treet<derivedt, named_subtreest>::remove_ref(dt *old_data)
{
  if(old_data == &empty_d)
    return;

#if 0
    nonrecursive_destructor(old_data);
#else

  PRECONDITION(old_data->ref_count != 0);

#ifdef IREP_DEBUG
  std::cout << "R: " << old_data << " " << old_data->ref_count << '\n';
#endif

  old_data->ref_count--;
  if(old_data->ref_count == 0)
  {
#ifdef IREP_DEBUG
    std::cout << "D: " << pretty() << '\n';
    std::cout << "DELETING " << old_data->data << " " << old_data << '\n';
    old_data->clear();
    std::cout << "DEALLOCATING " << old_data << "\n";
#endif

    // may cause recursive call
    delete old_data;

#ifdef IREP_DEBUG
    std::cout << "DONE\n";
#endif
  }
#endif
}

/// Does the same as remove_ref, but using an explicit stack instead of
/// recursion.
template <typename derivedt, typename named_subtreest>
void sharing_treet<derivedt, named_subtreest>::nonrecursive_destructor(
  dt *old_data)
{
  std::vector<dt *> stack(1, old_data);

  while(!stack.empty())
  {
    dt *d = stack.back();
    stack.erase(--stack.end());
    if(d == &empty_d)
      continue;

    INVARIANT(d->ref_count != 0, "All contents of the stack must be in use");
    d->ref_count--;

    if(d->ref_count == 0)
    {
      stack.reserve(
        stack.size() + std::distance(d->named_sub.begin(), d->named_sub.end()) +
        d->sub.size());

      for(typename named_subt::iterator it = d->named_sub.begin();
          it != d->named_sub.end();
          it++)
      {
        stack.push_back(it->second.data);
        it->second.data = &empty_d;
      }

      for(typename subt::iterator it = d->sub.begin(); it != d->sub.end(); it++)
      {
        stack.push_back(it->data);
        it->data = &empty_d;
      }

      // now delete, won't do recursion
      delete d;
    }
  }
}

#endif // CPROVER_UTIL_IREP_H
