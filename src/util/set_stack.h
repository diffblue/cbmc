#ifndef CPROVER_SET_STACK_H
#define CPROVER_SET_STACK_H

#include <set>
#include <list>

template <class T>
class set_stack
{
 protected:
  typedef std::multiset<T> sett;
  typedef typename sett::iterator set_iterator;
  typedef typename sett::const_iterator set_const_iterator;
  typedef typename std::list<set_iterator> listt;
  typedef typename listt::size_type list_size_type;

 public:
  typedef typename sett::const_iterator const_iterator;
  
  const T &front() const
  { return *l.front(); }
  
  const T &back() const
  { return *l.back(); }
  
  T &front()
  { return *l.front(); }
  
  T &back()
  { return *l.back(); }
  
  const_iterator begin() const
  { return s.begin(); }
 
  const_iterator end() const
  { return s.end(); }

  set_const_iterator find(const T &e) const
  { return s.find(e); }

  void push_back(const T &e)
  { l.push_back(s.insert(e)); }

  void pop_back()
  {
    s.erase(l.back());
    l.pop_back();
  }
   
  list_size_type size() const
  { return l.size(); }
   
  const T &back() const
  { return *l.back(); }

  void resize(list_size_type s);
  
  bool empty() const
  { return l.empty(); }

 protected:
  sett s;
  listt l;
};

template <class T>
void set_stack<T>::resize(list_size_type s)
{
  if(l.size()>s)
  {
    for(unsigned i=l.size()-s; i!=0; i--)
      pop_back();
  }
  else if(l.size()<s)
  {
    T e;

    for(unsigned i=s-l.size(); i!=0; i--)
      push_back(e);    
  }
}
 
#include <hash_cont.h>

template <class T, class H>
class hash_set_stack
{
 protected:
  typedef typename hash_multiset_cont<T, H> sett;
  typedef typename sett::iterator set_iterator;
  typedef typename sett::const_iterator set_const_iterator;
  typedef typename std::list<set_iterator> listt;
  typedef typename listt::size_type list_size_type;

 public:
  typedef set_const_iterator const_iterator;
  
  const_iterator begin() const
  { return s.begin(); }
 
  const_iterator end() const
  { return s.end(); }

  set_const_iterator find(const T &e) const
  { return s.find(e); }

  void push_back(const T &e)
  { l.push_back(s.insert(e)); }

  void pop_back()
  {
    s.erase(l.back());
    l.pop_back();
  }
   
  list_size_type size() const
  { return l.size(); }
   
  const T &back() const
  { return *l.back(); }

  void resize(list_size_type s);
  
  bool empty() const
  { return l.empty(); }

 protected:
  sett s;
  listt l;
};

template <class T, class H>
void hash_set_stack<T, H>::resize(list_size_type s)
{
  if(l.size()>s)
  {
    for(unsigned i=l.size()-s; i!=0; i--)
      pop_back();
  }
  else if(l.size()<s)
  {
    T e;

    for(unsigned i=s-l.size(); i!=0; i--)
      push_back(e);    
  }
}

#endif
