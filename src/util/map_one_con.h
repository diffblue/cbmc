/*******************************************************************\

Module: Map that stores equal values only once

Author: Daniel Poetzl

\*******************************************************************/

// Notes:
//
// The methods at() (for non-const instances) and operator[] return a non-const
// reference to a value in the map. If the reference count of the requested
// value in the map is >1 then a copy is created internally. It is thus allowed
// (and expected) to modify the value through the returned reference. On the
// next call to *any* method of map_one_cont the hash code of the previously
// returned value is recomputed and it is re-integrated into the map. The
// reference becomes invalid at this point.

#ifndef CPROVER_MAP_ONE_CON_H
#define CPROVER_MAP_ONE_CON_H

#include <cassert>
#include <climits>
#include <tuple>
#include <list>
#include <map>
#include <unordered_map>
#include <iostream>

template <class T>
struct dummy_hash
{
  size_t operator()(const T &v) const
  {
    assert(false);
    return 0;
  }
};

struct identity_hash
{
  size_t operator()(const size_t v) const
  {
    return v;
  }
};

template <class T>
struct dummy_equal_to
{
  bool operator()(const T &v1, const T &v2) const
  {
    assert(false);
    return true;
  }
};

namespace
{
  const unsigned collision_threshold=5;
}

template <
  class Key,
  class T,
  class Hash, // hash for T
  class Pred=std::equal_to<T>,
  class Compare=std::less<Key>,
  bool error_check=false
>
class map_one_cont final
{
public:
  typedef map_one_cont<Key, T, Hash, Pred, Compare, error_check> self_type;

  typedef Key key_type;
  typedef T mapped_type;
  // same as for std::map for compatibility
  typedef std::pair<const key_type, mapped_type> value_type;

  // hash, mapped value, reference count
  typedef std::tuple<size_t, mapped_type, unsigned> entryt;
  typedef std::list<entryt> entry_listt;
  typedef typename entry_listt::iterator entry_itt;
  typedef typename entry_listt::const_iterator const_entry_itt;

  typedef std::map<key_type, entry_itt> it_mapt;
  typedef std::list<entry_itt> it_listt;

  typedef std::unordered_map<size_t, it_listt, identity_hash> rev_mapt;

  typedef typename it_mapt::size_type size_type;

  class const_iterator;

  const_iterator find(const key_type &k) const
  {
    preamble();
    return const_iterator(it_map.find(k));
  }

  // creates mapped value if need be, calls default constructor
  mapped_type& operator[](const key_type &k)
  {
    preamble();

    const_iterator it=find(k);

    if(it!=end())
    {
      return at(it);
    }
    else
    {
      it=insert_internal(k, mapped_type());
      assert(it!=end());
      return at(it);
    }
  }

  // like [] but returns const reference
  const mapped_type &create_and_value_at(const key_type &k)
  {
    preamble();

    const_iterator it=find(k);

    if(it!=end())
    {
      return (*it).second;
    }
    else
    {
      it=insert_internal(k, mapped_type());
      assert(it!=end());
      return (*it).second;
    }
  }

  // synonym for at() with const instance
  const mapped_type &value_at(const key_type &k) const
  {
    preamble();
    return get_mapped_value(it_map.at(k)); // can throw exception
  }

  const mapped_type &at(const key_type &k) const
  {
    preamble();
    return get_mapped_value(it_map.at(k)); // can throw exception
  }

  mapped_type &at(const_iterator it)
  {
    preamble();

    assert(it!=end());

    needs_fix=true;

    // convert to non-const iterator
    typename it_mapt::iterator i_it=it_map.erase(it.it, it.it);

    entry_itt entry_it=i_it->second;
    assert(entry_it!=entry_list.end());

    last_entry_it_ptr=&(i_it->second);
    assert(*last_entry_it_ptr==entry_it);

    mapped_type &m=get_mapped_value(entry_it);
    unsigned &ref_count=get_ref_count(entry_it);

    if(ref_count==1)
    {
      delete_hash(entry_it);
      assert(get_ref_count(entry_it)==1);
      assert(get_hash(entry_it)==0);
      last_entry_it=entry_it;
      return m;
    }

    assert(ref_count>1);

    // now the reference count of the current entry decreases
    ref_count--;

    // make a copy
    entry_list.push_back(*entry_it);
    entry_itt new_entry_it=--entry_list.end();

    unsigned &new_ref_count=get_ref_count(new_entry_it);
    assert(&new_ref_count!=&ref_count);
    mapped_type &new_m=get_mapped_value(new_entry_it);
    assert(&m!=&new_m);
    assert(&get_hash(entry_it)!=&get_hash(new_entry_it));

    new_ref_count=1;
    last_entry_it=new_entry_it;
    *last_entry_it_ptr=new_entry_it; // set to new iterator already

    return new_m;
  }

  mapped_type &at(const key_type &k)
  {
    preamble();

    const_iterator it=find(k);
    if(it==end())
      throw std::out_of_range("map_one_cont::at");

    return at(it);
  }

  void erase(const_iterator it)
  {
    preamble();

    assert(it!=end());

    typename it_mapt::const_iterator i_it=it.it;
    entry_itt e_it=i_it->second;

    it_map.erase(i_it);

    unsigned &ref_count=get_ref_count(e_it);

    if(ref_count>1)
    {
      ref_count--;
    }
    else
    {
      assert(ref_count==1);

      delete_hash(e_it);

      entry_list.erase(e_it);
    }
  }

  // returns the number of elements erased (0 or 1)
  size_type erase(const key_type &k)
  {
    preamble();

    const_iterator it=find(k);
    if(it==end())
      return 0;

    erase(it);

    return 1;
  }

  // insert new element if key does not exist yet
  std::pair<const_iterator, bool> insert(const value_type &v)
  {
    preamble();

    const key_type &k=v.first;

    const_iterator it=find(k);
    if(it!=end())
      return std::make_pair(it, false);

    const mapped_type &m=v.second;

    it=insert_internal(k, m);
    assert(it!=end());

    return std::make_pair(it, true);
  }

  size_type size() const
  {
    preamble();

    return it_map.size();
  }

  size_type size_unique() const
  {
    preamble();

    return entry_list.size()-(size_type)needs_erase;
  }

  bool empty() const
  {
    preamble();

    return it_map.empty();
  }

  void clear()
  {
    preamble();

    it_map.clear();
    entry_list.clear();
    rev_map.clear();

    needs_fix=false;
    last_entry_it_ptr=NULL;

    if(error_check)
    {
      needs_erase=false;
      has_old=false;
      old_hash=0;

      num_ops=0;
    }
  }

  // explicit reintegrate
  void reintegrate()
  {
    preamble();
  }

  class const_iterator
  {
  public:
    friend self_type;
    typedef const std::pair<const key_type &, const mapped_type &> rett;

    const_iterator(typename it_mapt::const_iterator it) : it(it) {}

    // preincrement
    const_iterator operator++()
    {
      it++;
      return *this;
    }

    // postincrement
    const_iterator operator++(int dummy)
    {
      const_iterator self=*this;
      it++;
      return self;
    }

    rett operator*()
    {
      rett p(it->first, std::get<1>(*(it->second)));
      return p;
    }

    bool operator==(const const_iterator &rhs)
    {
      return it==rhs.it;
    }

    bool operator!=(const const_iterator &rhs)
    {
      return it!=rhs.it;
    }

  private:
    typename it_mapt::const_iterator it;
  };

  const_iterator cbegin() const
  {
    return const_iterator(it_map.cbegin());
  }

  const_iterator cend() const
  {
    return const_iterator(it_map.cend());
  }

  const_iterator begin() const
  {
    return cbegin();
  }

  const_iterator end() const
  {
    return cend();
  }

  friend void test1();

private:
  // key must not exist yet
  const_iterator insert_internal(
    const key_type &k,
    const mapped_type &m)
  {
    if(error_check)
      assert(find(k)==end());

    bool r;
    it_listt *it_list;
    entry_itt entry_it;

    size_t hash=Hash()(m);
    r=update_rev_map(m, hash, it_list, entry_it);

    typedef std::pair<typename it_mapt::iterator, bool> rest;
    rest res;

    if(r)
    {
      // create mapping to existing mapped value
      res=it_map.insert(std::make_pair(k, entry_it));
      assert(res.second);
    }
    else
    {
      // no mapped value yet
      entry_list.push_back(std::make_tuple(hash, m, 1));
      entry_it=--entry_list.end();

      it_list->push_back(entry_it);
      res=it_map.insert(std::make_pair(k, entry_it));
      assert(res.second);
    }

    return const_iterator(res.first);
  }

  inline void preamble() const
  {
#if 0
    std::cout << "map_one_cont: preamble()" << std::endl;
#endif

    check_old();
    (const_cast<self_type *>(this))->fix();
    (const_cast<self_type *>(this))->verify();
  }

  inline void fix()
  {
    if(!needs_fix)
      return;

    needs_fix=false;

    const mapped_type &m=get_mapped_value(last_entry_it);

    bool r;
    entry_itt existing_entry_it;

    size_t hash=Hash()(m); // recompute hash

    size_t &current_hash=get_hash(last_entry_it);
    current_hash=hash; // update hash

    if(error_check)
    {
      if(needs_erase)
      {
        assert(has_old);
        entry_list.erase(old_entry_it);
      }

      has_old=true;
      needs_erase=false;

      old_hash=hash;
      old_entry_it=last_entry_it;
    }

    it_listt *it_list;
    r=update_rev_map(m, hash, it_list, existing_entry_it);

    if(r)
    {
      // existing entry
      *last_entry_it_ptr=existing_entry_it;

      if(!error_check)
        entry_list.erase(last_entry_it);
      else
        needs_erase=true;
    }
    else
    {
      // no existing entry
      assert(*last_entry_it_ptr==last_entry_it);
      it_list->push_back(last_entry_it);
    }
  }

  void delete_hash(entry_itt entry_it)
  {
    size_t &hash=get_hash(entry_it);

    typename rev_mapt::iterator it=rev_map.find(hash);
    assert(it!=rev_map.end());

    it_listt &it_list=it->second;
    assert(it_list.size()<collision_threshold);

    unsigned n=it_list.size();
    it_list.remove(entry_it);
    assert(it_list.size()==n-1);

    hash=0;

    if(it_list.empty())
      rev_map.erase(it);
  }

  bool update_rev_map(
    const mapped_type &m,
    size_t hash,
    it_listt *&existing_it_list,
    entry_itt &existing_entry_it) // existing entry output
  {
    if(error_check)
      assert(Hash()(m)==hash);

    it_listt &it_list=rev_map[hash]; // create if need be
    assert(it_list.size()<collision_threshold);

    for(typename it_listt::iterator i_it=it_list.begin();
        i_it!=it_list.end(); i_it++)
    {
      entry_itt entry_it=*i_it;

      const mapped_type &me=get_mapped_value(entry_it);
      unsigned &ref_count=get_ref_count(entry_it);

      if(Pred()(m, me))
      {
        existing_entry_it=entry_it;
        ref_count++; // also bump up reference count here
        return true;
      }
    }

    existing_it_list=&it_list;

    return false;
  }

  inline bool update_rev_map(
    const mapped_type &m,
    it_listt *&existing_it_list,
    entry_itt &existing_entry_it)
  {
    size_t hash=Hash()(m);
    return update_index(m, hash, existing_it_list, existing_entry_it);
  }

  // constant time
  inline void check_old() const
  {
    if(!error_check)
      return;

    if(!has_old)
      return;

    const mapped_type &m=get_mapped_value(old_entry_it);
    size_t hash=Hash()(m);
    assert(hash==old_hash);
  }

  // amortized constant time
  inline void verify()
  {
    if(!error_check)
      return;

    num_ops++;

    if(num_ops>it_map.size())
    {
      num_ops=0;

      // verify hash codes
      for(const_entry_itt it=entry_list.begin();
          it!=entry_list.end(); it++)
      {
        const mapped_type &m=get_mapped_value(it);
        unsigned ref_count=get_ref_count(it);
        assert(ref_count>0);
        size_t hash=get_hash(it);
        assert(hash==Hash()(m));
      }
    }
  }

  inline size_t &get_hash(const entry_itt &e_it) const
  {
    return std::get<0>(*e_it);
  }

  inline const size_t &get_hash(
    const const_entry_itt &e_it) const
  {
    return std::get<0>(*e_it);
  }

  inline unsigned &get_ref_count(const entry_itt &e_it) const
  {
    return std::get<2>(*e_it);
  }

  inline const unsigned &get_ref_count(
    const const_entry_itt &e_it) const
  {
    return std::get<2>(*e_it);
  }

  inline mapped_type &get_mapped_value(const entry_itt &e_it) const
  {
    return std::get<1>(*e_it);
  }

  inline const mapped_type &get_mapped_value(
    const const_entry_itt &e_it) const
  {
    return std::get<1>(*e_it);
  }

  it_mapt it_map;
  entry_listt entry_list;
  rev_mapt rev_map;

  bool needs_fix=false;
  entry_itt *last_entry_it_ptr=NULL;
  entry_itt last_entry_it;

  // for error checking
  bool needs_erase=false;
  bool has_old=false;
  size_t old_hash=0;
  entry_itt old_entry_it;

  unsigned num_ops=0;
};

#if 0
// Unit tests
namespace
{

// all assertions should pass both with and without error checking
void test1()
{
  typedef map_one_cont<int, int, std::hash<int>> test_mapt;

  typedef map_one_cont<int, int, std::hash<int>, std::equal_to<int>,
    std::less<int>, true> test_map2t;

  typedef test_mapt testt;
  //typedef test_map2t testt;

  testt m;

  m.insert(std::make_pair(1, 2));
  m.insert(std::make_pair(2, 2));
  assert(m.size()==2);
  assert(m.size_unique()==1);
  assert(m.find(1)!=m.end());
  assert(m.find(3)==m.end());

  assert(m.begin()==m.cbegin());
  assert(m.end()==m.cend());

  m.erase(1);
  assert(m.size()==1);
  assert(m.size_unique()==1);

  int i=m.at(2); // no copy necessary
  assert(i==2);
  assert(m.size_unique()==1);
  assert(!m.empty());
  assert(m.size_unique()==1);

  i=m.value_at(2);
  assert(i==2);
  assert(m.size_unique()==1);

  assert(!m.insert(std::make_pair(2, 3)).second);
  assert(m.insert(std::make_pair(3, 4)).second);
  assert(m.insert(std::make_pair(4, 5)).second);
  assert(m.size()==3);
  assert(m.size_unique()==3);
  // contents at this point: (2, 2), (3, 4), (4, 5)

  testt::const_iterator it=m.cbegin();
  assert(it!=m.cend());
  assert((*it).first==2);
  assert((*it).second==2);
  it++;
  assert(it!=m.cend());
  assert((*it).first==3);
  assert((*it).second==4);
  it++;
  assert(it!=m.cend());
  assert((*it).first==4);
  assert((*it).second==5);
  it++;
  assert(it==m.cend());

  assert(m.insert(std::make_pair(5, 4)).second);
  i=m.at(5); // copy is made
  assert(m.size()==4); // copy is re-integrated
  assert(m.size_unique()==3);
  assert(m.at(5)==4);

  int &j=m.at(4); // no copy
  j=4;
  assert(m.size()==4);
  assert(m.size_unique()==2);

  int &k=m.at(4); // copy is made
  k=8;
  assert(m.size()==4);
  assert(m.size_unique()==3);

  // add 100 more
  for(int i=10; i<110; i++)
    assert(m.insert(std::make_pair(i, i+1)).second);
  assert(m.size()==104);

  m[110]; // expand
  assert(m.size()==105);
  assert(m.size_unique()==104);
  m[111];
  assert(m.size()==106);
  assert(m.size_unique()==104);

  m.erase(111);
  m.erase(110);
  m.erase(109);
  assert(m.size()==103);
}

class Test {
public:
  Test(int a) : a(a) {}
  bool operator==(const Test &other) const { return a==other.a; }
  int a;
};

struct zero_hash {
  size_t operator()(const Test &v) const { return 0; }
};

// assertion with collision_threshold should fail
void test2()
{
  typedef map_one_cont<int, Test, zero_hash> test_mapt;

  test_mapt m;
  for(int i=0; i<10; i++)
    m.insert(std::make_pair(i, Test(i)));
}

// assertion should fail due to object being changed through invalid reference
void test3()
{
  typedef map_one_cont<int, int, std::hash<int>, std::equal_to<int>,
    std::less<int>, true> test_map2t;

  test_map2t m;

  m.insert(std::make_pair(1, 2));
  int &i=m.at(1);
  assert(!m.empty());
  i=3; // write through invalid reference
  assert(!m.empty()); // detected here
}

} // anonymous namespace end

// compile via:
// g++ -x c++ -std=c++11 -Wall -Wno-unused-local-typedefs -Wno-comment
// -Wno-unused-function -o map_one_cont map_one_cont.h
int main()
{
  test1();
  //test2();
  //test3();
  return 0;
}
#endif

#endif
