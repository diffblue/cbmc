/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "irep.h"
#include "irep_hash.h"
#include "string2int.h"
#include "string_hash.h"

#include <cassert>
#include <ostream>

#ifdef SUB_IS_LIST
#include <algorithm>
#endif

#ifdef SHARING
std::shared_ptr<irept::dt> irept::empty=std::make_shared<dt>();
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
  static irept nil_rep_storage;
  if(nil_rep_storage.id().empty()) // initialized?
    nil_rep_storage.id(ID_nil);
  return nil_rep_storage;
}

/*******************************************************************\

Function: irept::move_to_named_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irept::move_to_named_sub(const irep_namet &name, irept &irep)
{
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
    static const irep_idt empty;
    return empty;
  }
  #else
  named_subt::const_iterator it=s.find(name);

  if(it==s.end())
  {
    static const irep_idt empty;
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
  return get(name)==ID_1;
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

Function: irept::get_size_t

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t irept::get_size_t(const irep_namet &name) const
{
  return unsafe_string2size_t(get_string(name));
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
  add(name).id(std::to_string(value));
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

  if(it!=s.end() && it->first==name)
    s.erase(it);
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

Function: irept::operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef IREP_HASH_STATS
unsigned long long irep_cmp_cnt=0;
unsigned long long irep_cmp_ne_cnt=0;
#endif

bool irept::operator==(const irept &other) const
{
  #ifdef IREP_HASH_STATS
  ++irep_cmp_cnt;
  #endif
  #ifdef SHARING
  if(data==other.data)
    return true;
  #endif

  if(id()!=other.id() ||
     get_sub()!=other.get_sub() || // recursive call
     get_named_sub()!=other.get_named_sub()) // recursive call
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

Function: irept::full_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool irept::full_eq(const irept &other) const
{
  #ifdef SHARING
  if(data==other.data)
    return true;
  #endif

  if(id()!=other.id())
    return false;

  const irept::subt &i1_sub=get_sub();
  const irept::subt &i2_sub=other.get_sub();
  const irept::named_subt &i1_named_sub=get_named_sub();
  const irept::named_subt &i2_named_sub=other.get_named_sub();
  const irept::named_subt &i1_comments=get_comments();
  const irept::named_subt &i2_comments=other.get_comments();

  if(i1_sub.size()!=i2_sub.size() ||
     i1_named_sub.size()!=i2_named_sub.size() ||
     i1_comments.size()!=i2_comments.size())
    return false;

  for(std::size_t i=0; i<i1_sub.size(); i++)
    if(!i1_sub[i].full_eq(i2_sub[i]))
      return false;

  {
    irept::named_subt::const_iterator i1_it=i1_named_sub.begin();
    irept::named_subt::const_iterator i2_it=i2_named_sub.begin();

    for(; i1_it!=i1_named_sub.end(); i1_it++, i2_it++)
      if(i1_it->first!=i2_it->first ||
         !i1_it->second.full_eq(i2_it->second))
        return false;
  }

  {
    irept::named_subt::const_iterator i1_it=i1_comments.begin();
    irept::named_subt::const_iterator i2_it=i2_comments.begin();

    for(; i1_it!=i1_comments.end(); i1_it++, i2_it++)
      if(i1_it->first!=i2_it->first ||
         !i1_it->second.full_eq(i2_it->second))
        return false;
  }

  return true;
}

/*******************************************************************\

Function: irept::ordering

  Inputs:

 Outputs:

 Purpose: defines ordering on the internal represenation

\*******************************************************************/

bool irept::ordering(const irept &other) const
{
  return compare(other)<0;

  #if 0
  if(X.data<Y.data)
    return true;
  if(Y.data<X.data)
    return false;

  if(X.sub.size()<Y.sub.size())
    return true;
  if(Y.sub.size()<X.sub.size())
    return false;

  {
    irept::subt::const_iterator it1, it2;

    for(it1=X.sub.begin(),
        it2=Y.sub.begin();
        it1!=X.sub.end() && it2!=Y.sub.end();
        it1++,
        it2++)
    {
      if(ordering(*it1, *it2))
        return true;
      if(ordering(*it2, *it1))
        return false;
    }

    assert(it1==X.sub.end() && it2==Y.sub.end());
  }

  if(X.named_sub.size()<Y.named_sub.size())
    return true;
  if(Y.named_sub.size()<X.named_sub.size())
    return false;

  {
    irept::named_subt::const_iterator it1, it2;

    for(it1=X.named_sub.begin(),
        it2=Y.named_sub.begin();
        it1!=X.named_sub.end() && it2!=Y.named_sub.end();
        it1++,
        it2++)
    {
      if(it1->first<it2->first)
        return true;
      if(it2->first<it1->first)
        return false;

      if(ordering(it1->second, it2->second))
        return true;
      if(ordering(it2->second, it1->second))
        return false;
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
  if(r!=0)
    return r;

  const subt::size_type size=get_sub().size(),
        i_size=i.get_sub().size();
  if(size<i_size)
    return -1;
  if(size>i_size)
    return 1;

  {
    irept::subt::const_iterator it1, it2;

    for(it1=get_sub().begin(),
        it2=i.get_sub().begin();
        it1!=get_sub().end() && it2!=i.get_sub().end();
        it1++,
        it2++)
    {
      r=it1->compare(*it2);
      if(r!=0)
        return r;
    }

    assert(it1==get_sub().end() && it2==i.get_sub().end());
  }

  const named_subt::size_type n_size=get_named_sub().size(),
        i_n_size=i.get_named_sub().size();
  if(n_size<i_n_size)
    return -1;
  if(n_size>i_n_size)
    return 1;

  {
    irept::named_subt::const_iterator it1, it2;

    for(it1=get_named_sub().begin(),
        it2=i.get_named_sub().begin();
        it1!=get_named_sub().end() && it2!=i.get_named_sub().end();
        it1++,
        it2++)
    {
      r=it1->first.compare(it2->first);
      if(r!=0)
        return r;

      r=it1->second.compare(it2->second);
      if(r!=0)
        return r;
    }

    assert(it1==get_named_sub().end() &&
           it2==i.get_named_sub().end());
  }

  // equal
  return 0;
}

/*******************************************************************\

Function: irept::operator<

  Inputs:

 Outputs:

 Purpose: defines ordering on the internal represenation

\*******************************************************************/

bool irept::operator<(const irept &other) const
{
  return ordering(other);
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
  if(max_indent>0 && indent>max_indent)
    return "";

  std::string result;

  if(!id().empty())
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

    result+=std::to_string(count++);
    result+=": ";

    result+=it->pretty(indent+2, max_indent);
  }

  return result;
}
