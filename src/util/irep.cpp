/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <ostream>

#include "string2int.h"
#include "irep.h"
#include "i2string.h"
#include "string_hash.h"
#include "irep_hash.h"

#ifdef SUB_IS_LIST
#include <algorithm>
#endif

#ifdef IREP_DEBUG
#include <iostream>
#endif

irept nil_rep_storage;

#ifdef SHARING
irept::dt irept::empty_d;
#endif

/*******************************************************************\

Function: named_subt_lower_bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef SUB_IS_LIST
static inline bool named_subt_order(
  const std::pair<irep_namet, irept> &a,
  const irep_namet &b)
{
  return a.first<b;
}

static inline irept::named_subt::const_iterator named_subt_lower_bound(
  const irept::named_subt &s, const irep_namet &id)
{
  return std::lower_bound(s.begin(), s.end(), id, named_subt_order);
}

static inline irept::named_subt::iterator named_subt_lower_bound(
  irept::named_subt &s, const irep_namet &id)
{
  return std::lower_bound(s.begin(), s.end(), id, named_subt_order);
}
#endif

/*******************************************************************\

Function: get_nil_irep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irept &get_nil_irep()
{
  if(nil_rep_storage.id().empty()) // initialized?
    nil_rep_storage.id(ID_nil);
  return nil_rep_storage;
}

/*******************************************************************\

Function: irept::detach

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef SHARING
void irept::detach()
{
  #ifdef IREP_DEBUG
  std::cout << "DETATCH1: " << data << std::endl;
  #endif

  if(data==&empty_d)
  {
    data=new dt;

    #ifdef IREP_DEBUG
    std::cout << "ALLOCATED " << data << std::endl;
    #endif
  }
  else if(data->ref_count>1)
  {
    dt *old_data(data);
    data=new dt(*old_data);

    #ifdef IREP_DEBUG
    std::cout << "ALLOCATED " << data << std::endl;
    #endif
    
    data->ref_count=1;
    remove_ref(old_data);
  }
  
  assert(data->ref_count==1);

  #ifdef IREP_DEBUG
  std::cout << "DETATCH2: " << data << std::endl;
  #endif
}
#endif

/*******************************************************************\

Function: irept::recursive_detach

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef SHARING
void irept::recursive_detach()
{
  detach();
  
  for(named_subt::iterator
      it=data->named_sub.begin();
      it!=data->named_sub.end();
      it++)
    it->second.recursive_detach();
    
  for(named_subt::iterator
      it=data->comments.begin();
      it!=data->comments.end();
      it++)
    it->second.recursive_detach();
    
  for(subt::iterator
      it=data->sub.begin();
      it!=data->sub.end();
      it++)
    it->recursive_detach();
}
#endif

/*******************************************************************\

Function: irept::remove_ref

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef SHARING
void irept::remove_ref(dt *old_data)
{
  if(old_data==&empty_d) return;
  
  #if 0
  nonrecursive_destructor(old_data);
  #else

  assert(old_data->ref_count!=0);

  #ifdef IREP_DEBUG
  std::cout << "R: " << old_data << " " << old_data->ref_count << std::endl;
  #endif
  
  old_data->ref_count--;
  if(old_data->ref_count==0)
  {
    #ifdef IREP_DEBUG
    std::cout << "D: " << pretty() << std::endl;
    std::cout << "DELETING " << old_data->data 
              << " " << old_data << std::endl;
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
#endif

/*******************************************************************\

Function: irept::nonrecursive_destructor

  Inputs:

 Outputs:

 Purpose: Does the same as remove_ref, but
          using an explicit stack instead of recursion.

\*******************************************************************/

#ifdef SHARING
void irept::nonrecursive_destructor(dt *old_data)
{
  std::vector<dt *> stack(1, old_data);
  
  while(!stack.empty())
  {
    dt *d=stack.back();
    stack.erase(--stack.end());
    if(d==&empty_d) continue;
    
    assert(d->ref_count!=0);
    d->ref_count--;

    if(d->ref_count==0)
    {
      stack.reserve(stack.size()+
                    d->named_sub.size()+
                    d->comments.size()+
                    d->sub.size());

      for(named_subt::iterator
          it=d->named_sub.begin();
          it!=d->named_sub.end();
          it++)
      {
        stack.push_back(it->second.data);
        it->second.data=&empty_d;
      }
      
      for(named_subt::iterator
          it=d->comments.begin();
          it!=d->comments.end();
          it++)
      {
        stack.push_back(it->second.data);
        it->second.data=&empty_d;
      }
      
      for(subt::iterator
          it=d->sub.begin();
          it!=d->sub.end();
          it++)
      {
        stack.push_back(it->data);
        it->data=&empty_d;
      }
      
      // now delete, won't do recursion
      delete d;
    }    
  }
}
#endif

/*******************************************************************\

Function: irept::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irept::clear()
{
  #ifdef SHARING
  remove_ref(data);
  data=&empty_d;
  #else
  data.clear();
  #endif
}

/*******************************************************************\

Function: irept::move_to_named_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irept::move_to_named_sub(const irep_namet &name, irept &irep)
{
  #ifdef SHARING
  detach();
  #endif
  add(name).swap(irep);
  irep.clear();
}

/*******************************************************************\

Function: irept::move_to_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irept::move_to_sub(irept &irep)
{
  #ifdef SHARING
  detach();
  #endif
  get_sub().push_back(get_nil_irep());
  get_sub().back().swap(irep);
}

/*******************************************************************\

Function: irept::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt &irept::get(const irep_namet &name) const
{
  const named_subt &s=
    is_comment(name)?get_comments():get_named_sub();

  #ifdef SUB_IS_LIST
  named_subt::const_iterator it=named_subt_lower_bound(s, name);

  if(it==s.end() ||
     it->first!=name)
  {
    const static irep_idt empty;
    return empty;
  }
  #else
  named_subt::const_iterator it=s.find(name);
  
  if(it==s.end())
  {
    const static irep_idt empty;
    return empty;
  }
  #endif

  return it->second.id();
}

/*******************************************************************\

Function: irept::get_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool irept::get_bool(const irep_namet &name) const
{
  return unsafe_string2int(get_string(name))!=0;
}

/*******************************************************************\

Function: irept::get_int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int irept::get_int(const irep_namet &name) const
{
  return unsafe_string2int(get_string(name));
}

/*******************************************************************\

Function: irept::get_unsigned_int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned int irept::get_unsigned_int(const irep_namet &name) const
{
  return unsafe_string2unsigned(get_string(name));
}

/*******************************************************************\

Function: irept::get_long_long

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

long long irept::get_long_long(const irep_namet &name) const
{
  return unsafe_string2signedlonglong(get_string(name));
}

/*******************************************************************\

Function: irept::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irept::set(const irep_namet &name, const long long value)
{
  add(name).id(i2string(value));
}  

/*******************************************************************\

Function: irept::remove

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irept::remove(const irep_namet &name)
{
  named_subt &s=
    is_comment(name)?get_comments():get_named_sub();

  #ifdef SUB_IS_LIST
  named_subt::iterator it=named_subt_lower_bound(s, name);

  if(it!=s.end() && it->first==name) s.erase(it);
  #else
  s.erase(name);
  #endif
}  

/*******************************************************************\

Function: irept::find

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irept &irept::find(const irep_namet &name) const
{
  const named_subt &s=
    is_comment(name)?get_comments():get_named_sub();

  #ifdef SUB_IS_LIST
  named_subt::const_iterator it=named_subt_lower_bound(s, name);

  if(it==s.end() ||
     it->first!=name)
    return get_nil_irep();
  #else
  named_subt::const_iterator it=s.find(name);

  if(it==s.end())
    return get_nil_irep();
  #endif

  return it->second;
}

/*******************************************************************\

Function: irept::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irept &irept::add(const irep_namet &name)
{
  named_subt &s=
    is_comment(name)?get_comments():get_named_sub();

  #ifdef SUB_IS_LIST
  named_subt::iterator it=named_subt_lower_bound(s, name);

  if(it==s.end() ||
     it->first!=name)
    it=s.insert(it, std::make_pair(name, irept()));

  return it->second;
  #else
  return s[name];
  #endif
}

/*******************************************************************\

Function: irept::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irept &irept::add(const irep_namet &name, const irept &irep)
{
  named_subt &s=
    is_comment(name)?get_comments():get_named_sub();

  #ifdef SUB_IS_LIST
  named_subt::iterator it=named_subt_lower_bound(s, name);

  if(it==s.end() ||
     it->first!=name)
    it=s.insert(it, std::make_pair(name, irep));
  else
    it->second=irep;

  return it->second;
  #else
  std::pair<named_subt::iterator, bool> entry=
    s.insert(std::make_pair(name, irep));

  if(!entry.second)
    entry.first->second=irep;

  return entry.first->second;
  #endif
}

/*******************************************************************\

Function: operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef IREP_HASH_STATS
unsigned long long irep_cmp_cnt=0;
unsigned long long irep_cmp_ne_cnt=0;
#endif

bool operator==(const irept &i1, const irept &i2)
{
  #ifdef IREP_HASH_STATS
  ++irep_cmp_cnt;
  #endif
  #ifdef SHARING
  if(i1.data==i2.data) return true;
  #endif

  if(i1.id()!=i2.id() ||
     i1.get_sub()!=i2.get_sub() || // recursive call
     i1.get_named_sub()!=i2.get_named_sub()) // recursive call
  {
    #ifdef IREP_HASH_STATS
    ++irep_cmp_ne_cnt;
    #endif
    return false;
  }

  // comments are NOT checked

  return true;
}

/*******************************************************************\

Function: full_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool full_eq(const irept &i1, const irept &i2)
{
  #ifdef SHARING
  if(i1.data==i2.data) return true;
  #endif

  if(i1.id()!=i2.id()) return false;

  const irept::subt &i1_sub=i1.get_sub();
  const irept::subt &i2_sub=i2.get_sub();
  const irept::named_subt &i1_named_sub=i1.get_named_sub();
  const irept::named_subt &i2_named_sub=i2.get_named_sub();
  const irept::named_subt &i1_comments=i1.get_comments();
  const irept::named_subt &i2_comments=i2.get_comments();

  if(i1_sub.size()      !=i2_sub.size()) return false;
  if(i1_named_sub.size()!=i2_named_sub.size()) return false;
  if(i1_comments.size() !=i2_comments.size()) return false;

  for(unsigned i=0; i<i1_sub.size(); i++)
    if(!full_eq(i1_sub[i], i2_sub[i]))
      return false;

  {
    irept::named_subt::const_iterator i1_it=i1_named_sub.begin();
    irept::named_subt::const_iterator i2_it=i2_named_sub.begin();
    
    for(; i1_it!=i1_named_sub.end(); i1_it++, i2_it++)
      if(i1_it->first!=i2_it->first ||
         !full_eq(i1_it->second, i2_it->second))
        return false;
  }
  
  {
    irept::named_subt::const_iterator i1_it=i1_comments.begin();
    irept::named_subt::const_iterator i2_it=i2_comments.begin();
    
    for(; i1_it!=i1_comments.end(); i1_it++, i2_it++)
      if(i1_it->first!=i2_it->first ||
         !full_eq(i1_it->second, i2_it->second))
        return false;
  }

  return true;
}

/*******************************************************************\

Function: irept::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include "lispirep.h"
#include "lispexpr.h"

std::string irept::to_string() const
{
  lispexprt lispexpr;
  irep2lisp(*this, lispexpr);
  return lispexpr.expr2string();
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (std::ostream& out, const irept &irep)
{
  out << irep.to_string();
  return out;
}

/*******************************************************************\

Function: ordering

  Inputs:

 Outputs:

 Purpose: defines ordering on the internal represenation

\*******************************************************************/

bool ordering(const irept &X, const irept &Y)
{
  return X.compare(Y)<0;

  #if 0
  if(X.data<Y.data) return true;
  if(Y.data<X.data) return false;

  if(X.sub.size()<Y.sub.size()) return true;
  if(Y.sub.size()<X.sub.size()) return false;

  {
    irept::subt::const_iterator it1, it2;

    for(it1=X.sub.begin(),
        it2=Y.sub.begin();
        it1!=X.sub.end() && it2!=Y.sub.end();
        it1++,
        it2++)
    {
      if(ordering(*it1, *it2)) return true;
      if(ordering(*it2, *it1)) return false;
    }

    assert(it1==X.sub.end() && it2==Y.sub.end());
  }

  if(X.named_sub.size()<Y.named_sub.size()) return true;
  if(Y.named_sub.size()<X.named_sub.size()) return false;

  {
    irept::named_subt::const_iterator it1, it2;

    for(it1=X.named_sub.begin(),
        it2=Y.named_sub.begin();
        it1!=X.named_sub.end() && it2!=Y.named_sub.end();
        it1++,
        it2++)
    {
      if(it1->first<it2->first) return true;
      if(it2->first<it1->first) return false;

      if(ordering(it1->second, it2->second)) return true;
      if(ordering(it2->second, it1->second)) return false;
    }

    assert(it1==X.named_sub.end() && it2==Y.named_sub.end());
  }

  return false;
  #endif
}

/*******************************************************************\

Function: irept::compare

  Inputs:

 Outputs:

 Purpose: defines ordering on the internal represenation

\*******************************************************************/

int irept::compare(const irept &i) const
{
  int r;

  r=id().compare(i.id());
  if(r!=0) return r;

  const subt::size_type size=get_sub().size(),
        i_size=i.get_sub().size();
  if(size<i_size) return -1;
  if(size>i_size) return 1;

  {
    irept::subt::const_iterator it1, it2;

    for(it1=get_sub().begin(),
        it2=i.get_sub().begin();
        it1!=get_sub().end() && it2!=i.get_sub().end();
        it1++,
        it2++)
    {
      r=it1->compare(*it2);
      if(r!=0) return r;
    }

    assert(it1==get_sub().end() && it2==i.get_sub().end());
  }

  const named_subt::size_type n_size=get_named_sub().size(),
        i_n_size=i.get_named_sub().size();
  if(n_size<i_n_size) return -1;
  if(n_size>i_n_size) return 1;

  {
    irept::named_subt::const_iterator it1, it2;

    for(it1=get_named_sub().begin(),
        it2=i.get_named_sub().begin();
        it1!=get_named_sub().end() && it2!=i.get_named_sub().end();
        it1++,
        it2++)
    {
      r=it1->first.compare(it2->first);
      if(r!=0) return r;

      r=it1->second.compare(it2->second);
      if(r!=0) return r;
    }

    assert(it1==get_named_sub().end() &&
           it2==i.get_named_sub().end());
  }

  // equal
  return 0;
}

/*******************************************************************\

Function: operator<

  Inputs:

 Outputs:

 Purpose: defines ordering on the internal represenation

\*******************************************************************/

bool operator<(const irept &X, const irept &Y)
{
  return ordering(X, Y);
}

/*******************************************************************\

Function: irept::hash

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


#ifdef IREP_HASH_STATS
unsigned long long irep_hash_cnt=0;
#endif

std::size_t irept::hash() const
{
  #ifdef HASH_CODE
  if(read().hash_code!=0)
    return read().hash_code;
  #endif

  const irept::subt &sub=get_sub();
  const irept::named_subt &named_sub=get_named_sub();

  std::size_t result=hash_string(id());

  forall_irep(it, sub) result=hash_combine(result, it->hash());

  forall_named_irep(it, named_sub)
  {
    result=hash_combine(result, hash_string(it->first));
    result=hash_combine(result, it->second.hash());
  }

  result=hash_finalize(result, named_sub.size()+sub.size());

  #ifdef HASH_CODE
  read().hash_code=result;
  #endif
  #ifdef IREP_HASH_STATS
  ++irep_hash_cnt;
  #endif
  return result;
}

/*******************************************************************\

Function: irept::full_hash

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t irept::full_hash() const
{
  const irept::subt &sub=get_sub();
  const irept::named_subt &named_sub=get_named_sub();
  const irept::named_subt &comments=get_comments();

  std::size_t result=hash_string(id());

  forall_irep(it, sub) result=hash_combine(result, it->full_hash());

  forall_named_irep(it, named_sub)
  {
    result=hash_combine(result, hash_string(it->first));
    result=hash_combine(result, it->second.full_hash());
  }

  forall_named_irep(it, comments)
  {
    result=hash_combine(result, hash_string(it->first));
    result=hash_combine(result, it->second.full_hash());
  }

  result=hash_finalize(
    result,
    named_sub.size()+sub.size()+comments.size());

  return result;
}

/*******************************************************************\

Function: indent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void indent_str(std::string &s, unsigned indent)
{
  for(unsigned i=0; i<indent; i++)
    s+=' ';
}

/*******************************************************************\

Function: irept::pretty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string irept::pretty(unsigned indent, unsigned max_indent) const
{
  if (max_indent > 0 && indent > max_indent) 
    return "";

  std::string result;

  if(id()!="")
  {
    result+=id_string();
    indent+=2;
  }

  forall_named_irep(it, get_named_sub())
  {
    result+="\n";
    indent_str(result, indent);

    result+="* ";
    result+=id2string(it->first);
    result+=": ";

    result+=it->second.pretty(indent+2, max_indent);
  }

  forall_named_irep(it, get_comments())
  {
    result+="\n";
    indent_str(result, indent);

    result+="* ";
    result+=id2string(it->first);
    result+=": ";

    result+=it->second.pretty(indent+2, max_indent);
  }

  unsigned count=0;

  forall_irep(it, get_sub())
  {
    result+="\n";
    indent_str(result, indent);

    result+=i2string(count++);
    result+=": ";

    result+=it->pretty(indent+2, max_indent);
  }

  return result;
}

