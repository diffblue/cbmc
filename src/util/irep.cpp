/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Internal Representation

#include "irep.h"

#include <ostream>

#include "string2int.h"
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

const irept &get_nil_irep()
{
  if(nil_rep_storage.id().empty()) // initialized?
    nil_rep_storage.id(ID_nil);
  return nil_rep_storage;
}

#ifdef SHARING
void irept::detach()
{
  #ifdef IREP_DEBUG
  std::cout << "DETACH1: " << data << '\n';
  #endif

  if(data==&empty_d)
  {
    data=new dt;

    #ifdef IREP_DEBUG
    std::cout << "ALLOCATED " << data << '\n';
    #endif
  }
  else if(data->ref_count>1)
  {
    dt *old_data(data);
    data=new dt(*old_data);

    #ifdef IREP_DEBUG
    std::cout << "ALLOCATED " << data << '\n';
    #endif

    data->ref_count=1;
    remove_ref(old_data);
  }

  POSTCONDITION(data->ref_count==1);

  #ifdef IREP_DEBUG
  std::cout << "DETACH2: " << data << '\n';
  #endif
}
#endif

#ifdef SHARING
void irept::remove_ref(dt *old_data)
{
  if(old_data==&empty_d)
    return;

  #if 0
  nonrecursive_destructor(old_data);
  #else

  PRECONDITION(old_data->ref_count!=0);

  #ifdef IREP_DEBUG
  std::cout << "R: " << old_data << " " << old_data->ref_count << '\n';
  #endif

  old_data->ref_count--;
  if(old_data->ref_count==0)
  {
    #ifdef IREP_DEBUG
    std::cout << "D: " << pretty() << '\n';
    std::cout << "DELETING " << old_data->data
              << " " << old_data << '\n';
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

/// Does the same as remove_ref, but using an explicit stack instead of
/// recursion.
#ifdef SHARING
void irept::nonrecursive_destructor(dt *old_data)
{
  std::vector<dt *> stack(1, old_data);

  while(!stack.empty())
  {
    dt *d=stack.back();
    stack.erase(--stack.end());
    if(d==&empty_d)
      continue;

    INVARIANT(d->ref_count!=0, "All contents of the stack must be in use");
    d->ref_count--;

    if(d->ref_count==0)
    {
      stack.reserve(stack.size()+
                    d->named_sub.size()+
                    d->sub.size());

      for(named_subt::iterator
          it=d->named_sub.begin();
          it!=d->named_sub.end();
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

void irept::move_to_named_sub(const irep_namet &name, irept &irep)
{
  #ifdef SHARING
  detach();
  #endif
  add(name).swap(irep);
  irep.clear();
}

void irept::move_to_sub(irept &irep)
{
  #ifdef SHARING
  detach();
  #endif
  get_sub().push_back(get_nil_irep());
  get_sub().back().swap(irep);
}

const irep_idt &irept::get(const irep_namet &name) const
{
  const named_subt &s = get_named_sub();

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

bool irept::get_bool(const irep_namet &name) const
{
  return get(name)==ID_1;
}

int irept::get_int(const irep_namet &name) const
{
  return unsafe_string2int(get_string(name));
}

unsigned int irept::get_unsigned_int(const irep_namet &name) const
{
  return unsafe_string2unsigned(get_string(name));
}

std::size_t irept::get_size_t(const irep_namet &name) const
{
  return unsafe_string2size_t(get_string(name));
}

long long irept::get_long_long(const irep_namet &name) const
{
  return unsafe_string2signedlonglong(get_string(name));
}

void irept::set(const irep_namet &name, const long long value)
{
  add(name).id(std::to_string(value));
}

void irept::remove(const irep_namet &name)
{
  named_subt &s = get_named_sub();

#ifdef SUB_IS_LIST
  named_subt::iterator it=named_subt_lower_bound(s, name);

  if(it!=s.end() && it->first==name)
    s.erase(it);
#else
  s.erase(name);
#endif
}

const irept &irept::find(const irep_namet &name) const
{
  const named_subt &s = get_named_sub();

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

irept &irept::add(const irep_namet &name)
{
  named_subt &s = get_named_sub();

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

irept &irept::add(const irep_namet &name, const irept &irep)
{
  named_subt &s = get_named_sub();

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

  if(id() != other.id() || get_sub() != other.get_sub()) // recursive call
  {
    #ifdef IREP_HASH_STATS
    ++irep_cmp_ne_cnt;
    #endif
    return false;
  }

  const auto &this_named_sub = get_named_sub();
  const auto &other_named_sub = other.get_named_sub();

  // walk in sync, ignoring comments, until end of both maps
  named_subt::const_iterator this_it = this_named_sub.begin();
  named_subt::const_iterator other_it = other_named_sub.begin();

  while(this_it != this_named_sub.end() || other_it != other_named_sub.end())
  {
    if(this_it != this_named_sub.end() && is_comment(this_it->first))
    {
      this_it++;
      continue;
    }

    if(other_it != other_named_sub.end() && is_comment(other_it->first))
    {
      other_it++;
      continue;
    }

    if(
      this_it == this_named_sub.end() ||   // reached end of 'this'
      other_it == other_named_sub.end() || // reached the end of 'other'
      this_it->first != other_it->first ||
      this_it->second != other_it->second) // recursive call
    {
#ifdef IREP_HASH_STATS
      ++irep_cmp_ne_cnt;
#endif
      return false;
    }

    this_it++;
    other_it++;
  }

  // reached the end of both
  return true;
}

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

  if(
    i1_sub.size() != i2_sub.size() ||
    i1_named_sub.size() != i2_named_sub.size())
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

  return true;
}

/// defines ordering on the internal representation
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

    INVARIANT(it1==X.sub.end() && it2==Y.sub.end(),
              "Unequal lengths will return before this");
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

    INVARIANT(it1==X.named_sub.end() && it2==Y.named_sub.end(),
              "Unequal lengths will return before this");
  }

  return false;
  #endif
}

/// defines ordering on the internal representation
/// comments are ignored
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

    INVARIANT(it1==get_sub().end() && it2==i.get_sub().end(),
              "Unequal lengths will return before this");
  }

  const auto n_size = number_of_non_comments(get_named_sub()),
             i_n_size = number_of_non_comments(i.get_named_sub());

  if(n_size<i_n_size)
    return -1;
  if(n_size>i_n_size)
    return 1;

  {
    irept::named_subt::const_iterator it1, it2;

    // clang-format off
    for(it1 = get_named_sub().begin(),
        it2 = i.get_named_sub().begin();
        it1 != get_named_sub().end() ||
        it2 != i.get_named_sub().end();
        ) // no iterator increments
    // clang-format on
    {
      if(it1 != get_named_sub().end() && is_comment(it1->first))
      {
        it1++;
        continue;
      }

      if(it2 != i.get_named_sub().end() && is_comment(it2->first))
      {
        it2++;
        continue;
      }

      // the case that both it1 and it2 are .end() is treated
      // by the loop guard; furthermore, the number of non-comments
      // must be the same
      INVARIANT(it1 != get_named_sub().end(), "not at end of get_named_sub()");
      INVARIANT(
        it2 != i.get_named_sub().end(), "not at end of i.get_named_sub()");

      r=it1->first.compare(it2->first);
      if(r!=0)
        return r;

      r=it1->second.compare(it2->second);
      if(r!=0)
        return r;

      it1++;
      it2++;
    }

    INVARIANT(
      it1 == get_named_sub().end() && it2 == i.get_named_sub().end(),
      "Unequal number of non-comments will return before this");
  }

  // equal
  return 0;
}

/// defines ordering on the internal representation
bool irept::operator<(const irept &other) const
{
  return ordering(other);
}

#ifdef IREP_HASH_STATS
unsigned long long irep_hash_cnt=0;
#endif

std::size_t irept::number_of_non_comments(const named_subt &named_sub)
{
  std::size_t result = 0;

  for(const auto &n : named_sub)
    if(!is_comment(n.first))
      result++;

  return result;
}

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

  std::size_t number_of_named_ireps = 0;

  forall_named_irep(it, named_sub)
    if(!is_comment(it->first)) // this variant ignores comments
    {
      result = hash_combine(result, hash_string(it->first));
      result = hash_combine(result, it->second.hash());
      number_of_named_ireps++;
    }

  result = hash_finalize(result, sub.size() + number_of_named_ireps);

#ifdef HASH_CODE
  read().hash_code=result;
#endif
#ifdef IREP_HASH_STATS
  ++irep_hash_cnt;
#endif
  return result;
}

std::size_t irept::full_hash() const
{
  const irept::subt &sub=get_sub();
  const irept::named_subt &named_sub=get_named_sub();

  std::size_t result=hash_string(id());

  forall_irep(it, sub) result=hash_combine(result, it->full_hash());

  // this variant includes all named_sub elements
  forall_named_irep(it, named_sub)
  {
    result=hash_combine(result, hash_string(it->first));
    result=hash_combine(result, it->second.full_hash());
  }

  result = hash_finalize(result, named_sub.size() + sub.size());

  return result;
}

static void indent_str(std::string &s, unsigned indent)
{
  for(unsigned i=0; i<indent; i++)
    s+=' ';
}

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

  std::size_t count=0;

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

irep_pretty_diagnosticst::irep_pretty_diagnosticst(const irept &irep)
  : irep(irep)
{
}
