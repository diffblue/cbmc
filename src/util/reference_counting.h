/*******************************************************************\

Module: Reference Counting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef __REFERENCE_COUNTING_H
#define __REFERENCE_COUNTING_H

#include <assert.h>

#include <iostream>

template<typename T>
class reference_counting
{
public:
  inline reference_counting():d(NULL)
  {
  }
  
  explicit reference_counting(const T &other):d(NULL)
  {
    write()=other;
  }

  // copy constructor
  inline reference_counting(const reference_counting &other):d(other.d)
  {
    if(d!=NULL)
    {
      assert(d->ref_count!=0);
      d->ref_count++;
      #ifdef REFERENCE_COUNTING_DEBUG
      std::cout << "COPY " << d << " " << d->ref_count << std::endl;
      #endif
    }
  }

  inline reference_counting &operator=(const reference_counting &other)
  {
    copy_from(other);
    return *this;
  }

  ~reference_counting()
  {
    remove_ref(d);
    d=NULL;
  }

  void swap(reference_counting &other)
  {
    std::swap(other.d, d);
  }

  void clear()
  {
    remove_ref(d);
    d=NULL;
  }
  
  inline const T &read() const
  {
    if(d==NULL) return T::empty;
    return *d;
  }

  inline T &write()
  {
    detatch();
    return *d;
  }
  
protected:
  class dt:public T
  {
  public:
    unsigned ref_count;

    dt():ref_count(1)
    {
    }
  };
  
  dt *d;

  void remove_ref(dt *old_d);
  
  void detatch();
  
  void copy_from(const reference_counting &other)
  {
    assert(&other!=this); // check if we assign to ourselves

    #ifdef REFERENCE_COUNTING_DEBUG
    std::cout << "COPY " << (&other) << "\n";
    #endif

    remove_ref(d);
    d=other.d;
    if(d!=NULL) d->ref_count++;
  }
  
public:
  inline dt *get_d() const
  {
    return d;
  }
};

template<class T>
void reference_counting<T>::remove_ref(dt *old_d)
{
  if(old_d==NULL) return;

  assert(old_d->ref_count!=0);

  #ifdef REFERENCE_COUNTING_DEBUG
  std::cout << "R: " << old_d << " " << old_d->ref_count << std::endl;
  #endif
  
  old_d->ref_count--;
  if(old_d->ref_count==0)
  {
    #ifdef REFERENCE_COUNTING_DEBUG
    std::cout << "DELETING " << old_d << std::endl;
    old_d->clear();
    std::cout << "DEALLOCATING " << old_d << "\n";
    #endif
    
    delete old_d;

    #ifdef REFERENCE_COUNTING_DEBUG
    std::cout << "DONE\n";
    #endif
  }
}

template<class T>
void reference_counting<T>::detatch()
{
  #ifdef REFERENCE_COUNTING_DEBUG
  std::cout << "DETATCH1: " << d << std::endl;
  #endif

  if(d==NULL)
  {
    d=new dt;

    #ifdef REFERENCE_COUNTING_DEBUG
    std::cout << "ALLOCATED " << d << std::endl;
    #endif
  }
  else if(d->ref_count>1)
  {
    dt *old_d(d);
    d=new dt(*old_d);

    #ifdef REFERENCE_COUNTING_DEBUG
    std::cout << "ALLOCATED " << d << std::endl;
    #endif
    
    d->ref_count=1;
    remove_ref(old_d);
  }
  
  assert(d->ref_count==1);

  #ifdef REFERENCE_COUNTING_DEBUG
  std::cout << "DETATCH2: " << d << std::endl;
  #endif
}

template<class T>
bool operator==(
  const reference_counting<T> &o1,
  const reference_counting<T> &o2)
{
  if(o1.get_d()==o2.get_d()) return true;
  return o1.read()==o2.read();
}
 
template<class T>
inline bool operator!=(
  const reference_counting<T> &i1,
  const reference_counting<T> &i2)
{ return !(i1==i2); }

#endif
