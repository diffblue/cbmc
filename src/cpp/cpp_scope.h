/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_SCOPE_H
#define CPROVER_CPP_CPP_SCOPE_H

#include "cpp_id.h"

#include <iosfwd>
#include <set>
#include <unordered_map>
#include <unordered_set>

class cpp_scopet:public cpp_idt
{
public:
  cpp_scopet()
  {
    is_scope=true;
  }

  typedef std::set<cpp_idt *> id_sett;

  enum lookup_kindt { SCOPE_ONLY, QUALIFIED, RECURSIVE };

  id_sett lookup(const irep_idt &base_name_to_lookup, lookup_kindt kind)
  {
    if(base_name_to_lookup.empty())
      return {};

    if(kind != SCOPE_ONLY)
    {
      auto &entry = lookup_cache()[{this, base_name_to_lookup, kind, -1}];
      if(entry.generation == scope_generation)
        return entry.result;
      entry.generation = scope_generation;
      entry.result.clear();
      lookup_rec(base_name_to_lookup, kind, entry.result);
      return entry.result;
    }
    id_sett result;
    lookup_rec(base_name_to_lookup, kind, result);
    return result;
  }

  id_sett lookup(
    const irep_idt &base_name_to_lookup,
    lookup_kindt kind,
    cpp_idt::id_classt identifier_class)
  {
    if(base_name_to_lookup.empty())
      return {};

    if(kind != SCOPE_ONLY)
    {
      auto &entry = lookup_cache()[{
        this, base_name_to_lookup, kind, static_cast<int>(identifier_class)}];
      if(entry.generation == scope_generation)
        return entry.result;
      entry.generation = scope_generation;
      entry.result.clear();
      lookup_rec(base_name_to_lookup, kind, identifier_class, entry.result);
      return entry.result;
    }

    id_sett result;
    lookup_rec(base_name_to_lookup, kind, identifier_class, result);
    return result;
  }

  id_sett
  lookup_identifier(const irep_idt &id, cpp_idt::id_classt identifier_class);

  cpp_idt &insert(const irep_idt &_base_name)
  {
    if(!suppress_cache_invalidation)
      ++scope_generation;
    cpp_id_mapt::iterator it =
      sub.insert(std::pair<irep_idt, cpp_idt>(_base_name, cpp_idt()));
    it->second.base_name = _base_name;
    it->second.set_parent(*this);
    return it->second;
  }

  cpp_idt &insert(const cpp_idt &cpp_id)
  {
    if(!suppress_cache_invalidation)
      ++scope_generation;
    cpp_id_mapt::iterator it =
      sub.insert(std::pair<irep_idt, cpp_idt>(cpp_id.base_name, cpp_id));
    it->second.set_parent(*this);
    return it->second;
  }

  /// When true, insert() does not invalidate the lookup cache.
  static bool suppress_cache_invalidation;

  bool contains(const irep_idt &base_name_to_lookup);

  bool is_root_scope() const
  {
    return id_class==id_classt::ROOT_SCOPE;
  }

  bool is_global_scope() const
  {
    return id_class==id_classt::ROOT_SCOPE ||
           id_class==id_classt::NAMESPACE;
  }

  cpp_scopet &get_parent() const
  {
    return static_cast<cpp_scopet &>(cpp_idt::get_parent());
  }

  cpp_scopet &get_global_scope()
  {
    cpp_scopet *p=this;

    while(!p->is_global_scope())
      p=&(p->get_parent());

    return *p;
  }

  void add_secondary_scope(cpp_scopet &other)
  {
    PRECONDITION(other.is_scope);
    ++scope_generation;
    secondary_scopes.push_back(&other);
  }

  void add_using_scope(cpp_scopet &other)
  {
    PRECONDITION(other.is_scope);
    ++scope_generation;
    using_scopes.push_back(&other);
  }

  class cpp_scopet &new_scope(const irep_idt &new_scope_name);

  /// Global generation counter, incremented on any scope mutation.
  static std::size_t scope_generation;

  struct cache_keyt
  {
    const cpp_scopet *scope;
    irep_idt name;
    lookup_kindt kind;
    int id_class; // -1 for unfiltered, enum value for filtered
    bool operator==(const cache_keyt &o) const
    {
      return scope == o.scope && name == o.name && kind == o.kind &&
             id_class == o.id_class;
    }
  };

  struct cache_key_hasht
  {
    std::size_t operator()(const cache_keyt &k) const
    {
      auto h = std::hash<const void *>{}(k.scope);
      h ^= std::hash<irep_idt>{}(k.name) + 0x9e3779b9 + (h << 6) + (h >> 2);
      h ^= std::hash<int>{}(k.kind) + 0x9e3779b9 + (h << 6) + (h >> 2);
      h ^= std::hash<int>{}(k.id_class) + 0x9e3779b9 + (h << 6) + (h >> 2);
      return h;
    }
  };

  struct cache_entryt
  {
    std::size_t generation = 0;
    id_sett result;
  };

  static std::unordered_map<cache_keyt, cache_entryt, cache_key_hasht> &
  lookup_cache()
  {
    static std::unordered_map<cache_keyt, cache_entryt, cache_key_hasht> cache;
    return cache;
  }

  /// Clear all static caches. Must be called between type-checking
  /// different translation units to avoid dangling scope pointers.
  static void clear_static_caches()
  {
    lookup_cache().clear();
  }

protected:
  typedef std::unordered_set<const cpp_scopet *> visited_sett;

  void lookup_rec(const irep_idt &base_name, lookup_kindt kind, id_sett &);

  void lookup_rec(
    const irep_idt &base_name,
    lookup_kindt kind,
    id_sett &,
    visited_sett &visited);

  void lookup_rec(
    const irep_idt &base_name,
    lookup_kindt kind,
    cpp_idt::id_classt id_class,
    id_sett &);

  void lookup_rec(
    const irep_idt &base_name,
    lookup_kindt kind,
    cpp_idt::id_classt id_class,
    id_sett &,
    visited_sett &visited);
};

class cpp_root_scopet:public cpp_scopet
{
public:
  cpp_root_scopet()
  {
    id_class=id_classt::ROOT_SCOPE;
    identifier="::";
  }
};

std::ostream &operator << (std::ostream &out, cpp_scopet::lookup_kindt);

#endif // CPROVER_CPP_CPP_SCOPE_H
