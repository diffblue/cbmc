/*******************************************************************\

Module: A Template Class for Tries

Author: Peter Schrammel

\*******************************************************************/

#ifndef __TRIE_H
#define __TRIE_H

#include <list>
#include <map>
#include <iostream>

template<class Key, class Value, Value EmptyValue>
class trie
{
public:
  trie() : value(EmptyValue), parent(NULL) {}

  typedef trie<Key, Value, EmptyValue> triet;
  typedef std::map<Key, trie<Key, Value, EmptyValue> > elementst;
  elementst children;
  Value value;
  trie<Key, Value, EmptyValue> *parent;
  Key key;

  trie<Key, Value, EmptyValue> &operator[](const Key& _key)
  {
    typename elementst::iterator it = children.find(_key);
    if(it == children.end())
    {
      children[_key].parent = this;
      children[_key].key = _key;
      it = children.find(_key);
    }
    return it->second;
  }

  void make_root() 
  {
    parent = NULL;
    key = NULL;
    value = EmptyValue;
  }

  std::pair<bool, const trie<Key, Value, EmptyValue> &> insert(
    const std::list<Key> &w, const Value& _value)
  {
    assert(!w.empty());
    assert(_value!=EmptyValue);

    // shape of root
    assert(parent==NULL);
    assert(value==EmptyValue);

    bool exists = true;
    elementst *t = &children;

    trie<Key, Value, EmptyValue> *parent_ptr = this;
    assert(parent_ptr!=NULL);

    for(typename std::list<Key>::const_iterator it = w.begin();
        it != w.end(); ++it)
    {
      typename elementst::iterator e_it = t->find(*it);
      exists = exists && (e_it!=t->end());
      
      typename std::list<Key>::const_iterator p_it = it; ++p_it;

      if(p_it == w.end()) // last element of w
      {
        if(exists)
        {
          return std::pair<bool, const triet &>(true, e_it->second);
        }
        else
        {
          trie<Key, Value, EmptyValue> &tmp = (*t)[*it];
          tmp.value = _value;
          tmp.key = *it;
          tmp.parent = parent_ptr;

          return std::pair<bool, const triet &>(true, tmp);
        }
      }
      else if(!exists)
      {
        trie<Key, Value, EmptyValue> &tmp = (*t)[*it];
        tmp.value = EmptyValue;
        tmp.key = *it;
        tmp.parent = parent_ptr;
      }

      parent_ptr = &((*t)[*it]);
      assert(parent_ptr!=NULL);

      t = &((*t)[*it].children);
    }

    assert(false);
    return std::make_pair(true, *this);
  }

#if 0
  bool insert(const std::list<Key> &w, const Value& value)
  {
    bool exists = true;
    elementst *t = &children;
    trie<Key, Value, EmptyValue> *parent_ptr = this;
    for(typename std::list<Key>::const_iterator it = w.begin();
        it != w.end(); ++it)
    {
      typename elementst::iterator e_it = t->find(*it);
      exists = exists && (e_it!=t->end());

      typename std::list<Key>::const_iterator p_it = it; ++p_it;
      if(p_it == w.end())
      {
        trie<Key, Value, EmptyValue> &tmp = (*t)[*it];
        tmp.value = value;
        tmp.key = *it;
        tmp.parent = parent_ptr;
      }
      else if(!exists)
      {
        trie<Key, Value, EmptyValue> &tmp = (*t)[*it];
        tmp.value = EmptyValue;
        tmp.key = *it;
        tmp.parent = parent_ptr;
      }

      parent_ptr = &((*t)[*it]);
      t = &(*t)[*it].children;
    }
    return !exists;
  }
#endif

  Value find(const std::list<Key> &w) const
  {
    assert(!w.empty());
    assert(parent==NULL);

    const elementst *t = &children;
    for(typename std::list<Key>::const_iterator it = w.begin();
        it != w.end(); ++it)
    {
      typename elementst::const_iterator e_it = t->find(*it);
      if(e_it == t->end())
        return EmptyValue;
      typename std::list<Key>::const_iterator p_it = it; ++p_it;
      if(p_it==w.end() && e_it->second.value!=EmptyValue)
        return e_it->second.value;
      t = &e_it->second.children;
    }
    return EmptyValue;
  }

  Value find_prefix_of(const std::list<Key> &w)
  {
    assert(!w.empty());

    elementst *t = &children;
    for(typename std::list<Key>::const_iterator it = w.begin();
	it != w.end(); ++it) 
    {
      typename elementst::iterator e_it = t->find(*it);
      bool found = e_it!=t->end();
      if(found && e_it->second.value!=EmptyValue) 
        return e_it->second.value;
      if(!found)
        return EmptyValue;
      t = &e_it->second.children;
    }
    return EmptyValue;
  }

  //a subset of the elements in w appear in the same order in the trie
  Value find_sub_of(const std::list<Key> &w)
  {
    elementst *t = &children;
    for(typename std::list<Key>::const_iterator it = w.begin();
	it != w.end(); ++it) 
    {
      typename elementst::iterator e_it = t->find(*it);
      bool found = e_it!=t->end();
      if(found && e_it->second.value!=EmptyValue) 
        return e_it->second.value;
      if(found)
        t = &e_it->second.children;
    }
    return EmptyValue;
  }

  void build_word(std::list<Key> &w) const
  {
    assert(w.empty());
    assert(parent!=NULL);

    const trie<Key, Value, EmptyValue> *it = this;
    assert(it!=NULL);

    while(it->parent != NULL)
    {
      w.push_front(it->key);
      it = it->parent;
    }
  }

  void clear()
  {
    children.clear();
    make_root();
  }

  static void output(std::ostream &out, const elementst &t, unsigned indent=0) 
  {
    for(typename elementst::const_iterator it = t.begin();
	it != t.end(); ++it)
    {
      for(size_t j=0; j<indent; ++j) out << " ";
      out << it->first << "(" << it->second.value << ")" << std::endl;
      output(out, it->second.children, indent+1);
    }
  }

  static void output_word(std::ostream &out, const std::list<Key> &w) 
  {
    for(typename std::list<Key>::const_iterator it = w.begin();
	it != w.end(); ++it) 
    {
      if(it != w.begin()) out << ", ";
      out << *it;
    }
    out << std::endl;
  }

  void output(std::ostream &out) const
  {
    trie<Key, Value, EmptyValue>::output(out,children);
  }
};

#endif
