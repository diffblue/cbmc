/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_IREP_H
#define CPROVER_UTIL_IREP_H

#include <string>
#include <vector>

#include "deprecate.h"
#include "invariant.h"
#include "irep_ids.h"

#define SHARING
// #define HASH_CODE
#define USE_MOVE
// #define SUB_IS_LIST

#ifdef SUB_IS_LIST
#include <list>
#else
#include <map>
#endif

#ifdef USE_DSTRING
typedef dstringt irep_idt;
typedef dstringt irep_namet;
// NOLINTNEXTLINE(readability/identifiers)
typedef dstring_hash irep_id_hash;
#else
#include "string_hash.h"
typedef std::string irep_idt;
typedef std::string irep_namet;
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

inline const std::string &name2string(const irep_namet &n)
{
  #ifdef USE_DSTRING
  return as_string(n);
  #else
  return n;
  #endif
}

#define forall_irep(it, irep) \
  for(irept::subt::const_iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#define Forall_irep(it, irep) \
  for(irept::subt::iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#define forall_named_irep(it, irep) \
  for(irept::named_subt::const_iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#define Forall_named_irep(it, irep) \
  for(irept::named_subt::iterator it=(irep).begin(); \
      it!=(irep).end(); ++it)

#ifdef IREP_DEBUG
#include <iostream>
#endif

class irept;
const irept &get_nil_irep();

/// \brief Base class for tree-like data structures with sharing
///
/// There are a large number of kinds of tree structured or tree-like data in
/// CPROVER. \ref irept provides a single, unified representation for all of
/// these, allowing structure sharing and reference counting of data. As
/// such \ref irept is the basic unit of data in CPROVER.  Each \ref irept
/// contains (or references, if reference counted data sharing is enabled, as
/// it is by default - see the `SHARING` macro) a basic unit of data (of type
/// \ref dt) which contains four things:
///
/// * \ref irept::dt::data : A string, which is returned when the \ref id()
///   function is used. (Unless `USE_STD_STRING` is set, this is actually a
///   \ref dstringt and thus an integer which is a reference into a string
///   table.)
///
/// * \ref irept::dt::named_sub : A map from `irep_namet` (a string) to \ref
///   irept. This is used for named children, i.e.  subexpressions, parameters,
///   etc. Children whose name begins with '#' are ignored by the
///   default \ref operator==.
///
/// * \ref irept::dt::sub : A vector of \ref irept which is used to store
///   ordered but unnamed children.
///
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
{
public:
  // These are not stable.
  typedef std::vector<irept> subt;

  // named_subt has to provide stable references; with C++11 we could
  // use std::forward_list or std::vector< unique_ptr<T> > to save
  // memory and increase efficiency.

  #ifdef SUB_IS_LIST
  typedef std::list<std::pair<irep_namet, irept> > named_subt;
  #else
  typedef std::map<irep_namet, irept> named_subt;
  #endif

  bool is_nil() const { return id()==ID_nil; }
  bool is_not_nil() const { return id()!=ID_nil; }

  explicit irept(const irep_idt &_id)
#ifdef SHARING
    :data(&empty_d)
#endif
  {
    id(_id);
  }

  #ifdef SHARING
  // constructor for blank irep
  irept():data(&empty_d)
  {
  }

  // copy constructor
  irept(const irept &irep):data(irep.data)
  {
    if(data!=&empty_d)
    {
      // NOLINTNEXTLINE(build/deprecated)
      PRECONDITION(data->ref_count != 0);
      data->ref_count++;
      #ifdef IREP_DEBUG
      std::cout << "COPY " << data << " " << data->ref_count << '\n';
      #endif
    }
  }

  #ifdef USE_MOVE
  // Copy from rvalue reference.
  // Note that this does avoid a branch compared to the
  // standard copy constructor above.
  irept(irept &&irep):data(irep.data)
  {
    #ifdef IREP_DEBUG
    std::cout << "COPY MOVE\n";
    #endif
    irep.data=&empty_d;
  }
  #endif

  irept &operator=(const irept &irep)
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

  #ifdef USE_MOVE
  // Note that the move assignment operator does avoid
  // three branches compared to standard operator above.
  irept &operator=(irept &&irep)
  {
    #ifdef IREP_DEBUG
    std::cout << "ASSIGN MOVE\n";
    #endif
    // we simply swap two pointers
    std::swap(data, irep.data);
    return *this;
  }
  #endif

  ~irept()
  {
    remove_ref(data);
  }

  #else
  irept()
  {
  }
  #endif

  const irep_idt &id() const
  { return read().data; }

  const std::string &id_string() const
  { return id2string(read().data); }

  void id(const irep_idt &_data)
  { write().data=_data; }

  const irept &find(const irep_namet &name) const;
  irept &add(const irep_namet &name);
  irept &add(const irep_namet &name, const irept &irep);

  const std::string &get_string(const irep_namet &name) const
  {
    return id2string(get(name));
  }

  const irep_idt &get(const irep_namet &name) const;
  bool get_bool(const irep_namet &name) const;
  signed int get_int(const irep_namet &name) const;
  /// \deprecated use get_size_t instead
  DEPRECATED("Use get_size_t instead")
  unsigned int get_unsigned_int(const irep_namet &name) const;
  std::size_t get_size_t(const irep_namet &name) const;
  long long get_long_long(const irep_namet &name) const;

  void set(const irep_namet &name, const irep_idt &value)
  { add(name).id(value); }
  void set(const irep_namet &name, const irept &irep)
  { add(name, irep); }
  void set(const irep_namet &name, const long long value);

  void remove(const irep_namet &name);
  void move_to_sub(irept &irep);
  void move_to_named_sub(const irep_namet &name, irept &irep);

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

public:
  static bool is_comment(const irep_namet &name)
  { return !name.empty() && name[0]=='#'; }

  /// count the number of named_sub elements that are not comments
  static std::size_t number_of_non_comments(const named_subt &);

  class dt
  {
  private:
    friend class irept;

    #ifdef SHARING
    unsigned ref_count;
    #endif

    /// This irep_idt is the only place to store data in an irep, other than
    /// the mere nesting structure
    irep_idt data;

    named_subt named_sub;
    subt sub;

    #ifdef HASH_CODE
    mutable std::size_t hash_code;
    #endif

    void clear()
    {
      data.clear();
      sub.clear();
      named_sub.clear();
      #ifdef HASH_CODE
      hash_code=0;
      #endif
    }

    void swap(dt &d)
    {
      d.data.swap(data);
      d.sub.swap(sub);
      d.named_sub.swap(named_sub);
      #ifdef HASH_CODE
      std::swap(d.hash_code, hash_code);
      #endif
    }

    #ifdef SHARING
    dt():ref_count(1)
      #ifdef HASH_CODE
         , hash_code(0)
      #endif
    {
    }
    #else
    dt()
      #ifdef HASH_CODE
      :hash_code(0)
      #endif
    {
    }
    #endif
  };

protected:
  #ifdef SHARING
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
    #ifdef HASH_CODE
    data->hash_code=0;
    #endif
    return *data;
  }

  #else
  dt data;

public:
  const dt &read() const
  {
    return data;
  }

  dt &write()
  {
    #ifdef HASH_CODE
    data.hash_code=0;
    #endif
    return data;
  }
  #endif
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

#endif // CPROVER_UTIL_IREP_H
