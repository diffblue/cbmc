/*******************************************************************\

Module: Global dependency analysis (field- and pointer-aware)

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANALYSES_GLOBAL_DEPENDENCY_ANALYSIS_H
#define CPROVER_ANALYSES_GLOBAL_DEPENDENCY_ANALYSIS_H

#include <memory>
#include <iostream>
#include <iterator>
#include <climits>

#include <goto-programs/goto_functions.h>
#include <util/expr.h>
#include <util/type.h>
#include <util/misc_utils.h>

extern const unsigned gda_max_num;
extern const unsigned gda_max_len;

// level of an abstract symbol
class levelt
{
public:

  enum Level
  {
    N, // numeric (>= 0, < gda_max_num)
    A, // top a (>= gda_max_num)
    B, // top b (> 0)
    B0, // top b zero (>= 0)
    END
  };

  levelt() : n(0), l(N)
  {
    assert(END==4);
  }

  explicit levelt(unsigned _n)
  {
    assert(END==4);
    n=_n;
    l=N;
    limit();
  }

  explicit levelt(Level l) : n(0), l(l) {}

  bool valid() const
  {
    return (l==N || n==0) && n<gda_max_num;
  }

  void limit()
  {
    if(n>=gda_max_num)
    {
      assert(l==N);
      n=0;
      l=A;
    }
  }

  // combine level types for use in switch statement cases
  static constexpr unsigned c(Level l1, Level l2)
  {
#if 0
    assert(l1<=3 && l2<=3);
#endif
    return l1<<2 | l2;
  }

  /*
  Addition of levels

  n1  (+) n2  = if n1 + n2 >= gda_max_num then ta else n1 + n2
  ta  (+) ta  = ta
  tb  (+) tb  = tb
  tb0 (+) tb0 = tb0

  n   (+) ta  = ta
  n   (+) tb  = if n >= (gda_max_num-1) then ta else tb
  n   (+) tb0 = if n >= 1 then tb else tb0
  ta  (+) tb  = ta
  ta  (+) tb0 = ta
  tb  (+) tb0 = tb
  */
  levelt operator+(const levelt &o) const
  {
    assert(valid());
    assert(o.valid());

    unsigned n1=n;
    unsigned n2=o.n;

    switch(c(l, o.l))
    {
    // same level types
    case c(N, N):
      return levelt(n1+n2);
      break;
    case c(A, A):
      return la;
      break;
    case c(B, B):
      return lb;
      break;
    case c(B0, B0):
      return lb0;
      break;

    // different level types
    case c(N, A):
      return la;
      break;
    case c(N, B):
      return n1>=(gda_max_num-1) ? la : lb;
      break;
    case c(N, B0):
      return n1>=1 ? lb : lb0;
      break;
    case c(A, B):
      return la;
      break;
    case c(A, B0):
      return la;
      break;
    case c(B, B0):
      return lb;
      break;

    // switch order and call again
    default:
      return o+(*this);
      break;
    };

    assert(false);
    return levelt();
  }

  /*
  Subtraction of levels

  n1  (-) n2  = n1 - n2
  ta  (-) ta  = tb0
  tb  (-) tb  = tb0
  tb0 (-) tb0 = tb0

  n   (-) ta  = assert false
  ta  (-) n   = if n == 0 then ta else if n <= 9 then tb else tb0

  n   (-) tb  = tb0
  tb  (-) n   = if n == 0 then tb else tb0

  n   (-) tb0 = tb0
  tb0 (-) n   = tb0

  ta  (-) tb  = tb0
  tb  (-) ta  = tb0

  ta  (-) tb0 = tb0
  tb0 (-) ta  = tb0

  tb  (-) tb0 = tb0
  tb0 (-) tb  = tb0
   */
  levelt operator-(const levelt &o) const
  {
    assert(valid());
    assert(o.valid());

    assert(o.can_affect(*this));

    unsigned n1=n;
    unsigned n2=o.n;

    switch(c(l, o.l))
    {
    // same level types
    case c(N, N):
      assert(n1>=n2);
      return levelt(n1-n2);
      break;
    case c(A, A):
    case c(B, B):
    case c(B0, B0):
      return lb0;
      break;

    // different level types
    case c(N, A):
      assert(false);
      break;
    case c(A, N):
      return n==0 ? la : lb;
      break;

    case c(N, B):
      return lb0;
      break;
    case c(B, N):
      return n==0 ? lb : lb0;
      break;

    case c(N, B0):
    case c(B0, N):
    case c(A, B):
    case c(B, A):
    case c(A, B0):
    case c(B0, A):
    case c(B, B0):
    case c(B0, B):
      return lb0;
      break;

    default:
      assert(false);
      break;
    }

    assert(false);
    return levelt();
  }

  bool operator==(const levelt &o) const
  {
    return n==o.n && l==o.l;
  }

  bool operator<(const levelt &o) const
  {
    return n<o.n || (n==o.n && l<o.l);
  }

  bool takes_address(const levelt &o) const
  {
    assert(valid());
    assert(o.valid());

    unsigned n1=n;
    unsigned n2=o.n;

    switch(c(l, o.l))
    {
    case c(N, N):
      return n1<n2;
      break;
    case c(A, N):
      return false;
      break;
    case c(B, N):
      return n2>1;
      break;
    case c(B0, N):
      return n2>0;
      break;
    default:
      break;
    }

    return true;
  }

  bool can_affect(const levelt &o) const
  {
    assert(valid());
    assert(o.valid());

    unsigned n1=n;
    unsigned n2=o.n;

    switch(c(l, o.l))
    {
    case c(N, N):
      return n1<=n2;
      break;
    case c(A, N):
      return false;
      break;
    case c(B, N):
      return n2>=1;
      break;
    case c(B0, N):
      return n2>=0;
      break;
    default:
      break;
    }

    return true;
  }

  bool overlap(const levelt &o) const
  {
    return can_affect(o) && o.can_affect(*this);
  }

  bool address() const
  {
    return l==N && n==0;
  }

  unsigned n; // numeric level
  Level l;

  static levelt la;
  static levelt lb;
  static levelt lb0;
};

std::ostream &operator<<(
  std::ostream &out,
  const levelt &level);

class elementt
{
public:
  typedef irep_idt idt;

  elementt(bool top=false) : is_top_element(top) {}

  elementt(idt id, levelt level, bool top=false) :
    id(id), level(level), is_top_element(top) {}

  bool operator==(const elementt &o) const
  {
    return id==o.id && level==o.level;
  }

  bool takes_address(const elementt &o) const
  {
    return is_top() || o.is_top() || (id==o.id && level.takes_address(o.level));
  }

  bool can_affect(const elementt &o) const
  {
    return is_top() || o.is_top() || (id==o.id && level.can_affect(o.level));
  }

  bool operator<(const elementt &o) const
  {
    return id<o.id || (id==o.id && level<o.level);
  }

  bool well_formed() const
  {
    return !is_top_element || (id.empty() && level.l==levelt::N && level.n==0);
  }

  void limit()
  {
    level.limit();
  }

  bool is_top() const
  {
    return is_top_element;
  }

  // might not be a dereference
  bool no_deref() const
  {
    return is_top() || level.can_affect(levelt(1));
  }

  // definitely takes address
  bool address() const
  {
    return !is_top() && level.address();
  }

  bool overlap(const elementt &o) const
  {
    return is_top() || o.is_top() || (id==o.id && level.overlap(o.level));
  }

  void output(std::ostream &out) const
  {
    out << "(";
    if(is_top_element)
    {
      out << "<t>";
    }
    else
    {
      out << id2string(id);
    }
    out << ", " << level << ")";
  }

  idt id;
  levelt level;

  bool is_top_element;

  static elementt top;
};

class abstract_symbolt
{
public:
  typedef std::list<elementt> element_listt;
  typedef irep_idt idt;

  abstract_symbolt() : expr(ID_nil) {}

  abstract_symbolt(idt id, levelt level) : expr(ID_nil)
  {
    push_back(id, level);
  }

  abstract_symbolt(idt id, unsigned level) : expr(ID_nil)
  {
    assert(level>=0 && level<10);
    push_back(id, level);
  }

  abstract_symbolt(const elementt &element) : expr(ID_nil)
  {
    push_back(element);
  }

  void set_expr(const exprt &_expr)
  {
    expr=_expr;
  }

  void del_expr()
  {
    set_expr(exprt(ID_nil));
  }

  bool has_expr() const
  {
    return expr.id()!=ID_nil;
  }

  void clear()
  {
    del_expr();
    element_list.clear();
  }

  // correct format
  bool well_formed() const
  {
    if(empty())
      return true;

    element_listt::const_iterator it=element_list.begin();

    // first element is never top
    if(it->is_top())
      return false;

    for(; it!=--element_list.end(); it++)
    {
      if(!it->well_formed())
        return false;

      if(it->address()) // definitely takes address?
        return false;
    }

    // we are at the last element
    return it->well_formed();
  }

  // well formed and limited
  bool limited() const
  {
    return well_formed() && length()<=gda_max_len;
  }

  bool empty() const
  {
    return element_list.empty();
  }

  size_t length() const
  {
    return element_list.size();
  }

  // last element becomes top if longer than gda_max_len
  void limit()
  {
    if(length()>gda_max_len)
    {
      element_list.resize(gda_max_len-1);
      element_list.push_back(elementt::top);
    }

    for(element_listt::iterator it=element_list.begin();
        it!=element_list.end(); it++)
    {
      it->limit();
    }
  }

  const elementt &front() const
  {
    return element_list.front();
  }

  const elementt &back() const
  {
    return element_list.back();
  }

  bool operator==(const abstract_symbolt &o) const
  {
    return element_list==o.element_list;
  }

  bool operator<(const abstract_symbolt &o) const
  {
    return element_list<o.element_list;
  }

  bool takes_address(const abstract_symbolt &o) const
  {
    if(empty() || o.empty())
      return false;

    size_t n1=length();
    size_t n2=o.length();

    if(n1<=n2)
    {
      element_listt::const_iterator it1=element_list.begin();
      element_listt::const_iterator it2=o.element_list.begin();

      while(it1!=--element_list.end())
      {
        if(!it1->overlap(*it2))
          return false;

        it1++;
        it2++;
      }

      if(!it1->takes_address(*it2))
        return false;
    }
    else
    {
      assert(n1>n2);

      element_listt::const_iterator it1=element_list.begin();
      element_listt::const_iterator it2=o.element_list.begin();

      while(it2!=o.element_list.end())
      {
        if(!it1->overlap(*it2))
          return false;

        it1++;
        it2++;
      }

      while(it1!=--element_list.end())
      {
        if(!it1->no_deref())
          return false;

        it1++;
      }

      if(!it1->is_top() && !it1->level.can_affect(levelt(0)))
        return false;
    }

    return true;
  }

  bool can_affect(const abstract_symbolt &o) const
  {
    if(empty() || o.empty())
      return false;

    size_t n1=length();
    size_t n2=o.length();

    if(n1<=n2)
    {
      element_listt::const_iterator it1=element_list.begin();
      element_listt::const_iterator it2=o.element_list.begin();

      while(it1!=--element_list.end())
      {
        if(!it1->overlap(*it2))
          return false;

        it1++;
        it2++;
      }

      if(!it1->can_affect(*it2))
        return false;
    }
    else
    {
      assert(n1>n2);

      element_listt::const_iterator it1=element_list.begin();
      element_listt::const_iterator it2=o.element_list.begin();

      while(it2!=o.element_list.end())
      {
        if(!it1->overlap(*it2))
          return false;

        it1++;
        it2++;
      }

      while(it1!=element_list.end())
      {
        if(!it1->no_deref())
          return false;

        it1++;
      }
    }

    return true;
  }

  // attach
  abstract_symbolt add(levelt level, const abstract_symbolt &o) const
  {
    assert(!empty());
    assert(limited());

    if(element_list.back().is_top())
    {
      return *this;
    }
    else
    {
      abstract_symbolt as(*this);
      assert(as==*this);

      // retrieve last
      elementt element=as.element_list.back();
      as.element_list.pop_back();

      // rewrite last
      element.level=element.level+level;
      as.element_list.push_back(element);

      // concatenate
      as.element_list.insert(
        as.element_list.end(),
        o.element_list.begin(),
        o.element_list.end());

      return as;
    }
  }

  // difference (*this minus other)
  std::pair<levelt, abstract_symbolt> operator-(const abstract_symbolt &o) const
  {
    assert(!empty());

    assert(limited());
    assert(o.limited());

    const abstract_symbolt &t=*this;
    assert(o.can_affect(t));

    size_t n1=length();
    size_t n2=o.length();

    if(n1<=n2)
    {
      element_listt::const_iterator it=o.element_list.begin();
      std::advance(it, n1-1); // last common element

      if(back().is_top())
      {
        abstract_symbolt as;
        as.push_back(elementt::top);
        return std::make_pair(levelt::lb0, as);
      }
      else if(it->is_top())
      {
        assert(!back().is_top());
        assert(n1==n2);
        return std::make_pair(back().level, abstract_symbolt());
      }
      else
      {
        assert(!back().is_top() && !it->is_top());
        levelt level_diff=back().level-it->level;
        return  std::make_pair(level_diff, abstract_symbolt());
      }
    }
    else
    {
      assert(n1>n2);
      if(o.back().is_top())
      {
        abstract_symbolt as;
        as.push_back(elementt::top);
        return std::make_pair(levelt::lb0, as);
      }
      else
      {
        assert(!o.back().is_top());

        element_listt::const_iterator it=element_list.begin();
        std::advance(it, n2-1); // last common element

        assert(!it->is_top());

        abstract_symbolt as;
        assert(as.empty());
        assert(as.element_list.begin()==as.element_list.end());

        levelt level_diff=it->level-o.back().level;

        it++;
        as.element_list.insert(
          as.element_list.begin(),
          it, element_list.end());

        assert(as.front().is_top() || as.limited());
        return std::make_pair(level_diff, as);
      }
    }

    return std::make_pair(levelt(), abstract_symbolt());
  }

  void push_back(idt id, unsigned level)
  {
    push_back(id, levelt(level));
  }

  void push_back(idt id, levelt level)
  {
    element_list.push_back(elementt(id, level));
  }

  void push_back(const elementt &element)
  {
    element_list.push_back(element);
  }

  bool can_add(levelt level, const abstract_symbolt as) const
  {
    return true;
  }

  // output abstract symbol
  void output(std::ostream &out) const
  {
    out << "[";
    for(element_listt::const_iterator it=element_list.begin();
        it!=element_list.end();)
    {
      it->output(std::cout);
      if(++it!=element_list.end())
      {
        out << ", ";
      }
    }
    out << "]";
  }

  // output abstract symbol and expression
  void output(std::ostream &out, const namespacet &ns) const
  {
    output(out);
    out << " ### { ";
    if(expr.id()!=ID_nil)
    {
      out << from_expr(ns, "", expr);
    }
    out << " }";
  }

  element_listt element_list;
  exprt expr; // expression this abstract symbol originates from
};

// graph is only updated if mapping does not exist yet
class propagation_grapht
{
public:
  propagation_grapht() {}

  enum Reason {
    R_BASE,     // base case
    R_LHS_PROP, // left-hand side affected symbols
    R_RHS_PROP, // right-hand side took address
    R_LHS_SYM,  // left-hand side symbol co-occurence
    R_RHS_SYM   // right-hand side symbol co-occurence
  };

  typedef std::set<abstract_symbolt> as_sett;

  typedef std::tuple<
    Reason,
    abstract_symbolt, // lhs
    abstract_symbolt, // rhs
    abstract_symbolt> // global
  valuet;

  typedef std::map<
    abstract_symbolt,
    valuet> grapht;

  bool empty() const
  {
    return graph.empty();
  }

  // all base
  bool is_base() const
  {
    for(grapht::const_iterator it=graph.begin(); it!=graph.end(); it++)
    {
      if(std::get<0>(it->second)!=R_BASE)
        return false;
    }
    return true;
  }

  void add_base(const abstract_symbolt &as)
  {
    graph.insert(std::make_pair(as,
      std::make_tuple(R_BASE, abstract_symbolt(), abstract_symbolt(),
        abstract_symbolt())));
  }

  void add_lhs_prop(
    const abstract_symbolt &new_as,
    const abstract_symbolt &lhs,
    const abstract_symbolt &rhs,
    const abstract_symbolt &global_as)
  {
    graph.insert(std::make_pair(new_as,
        std::make_tuple(R_LHS_PROP, lhs, rhs, global_as)));
  }

  void add_rhs_prop(
    const abstract_symbolt &new_as,
    const abstract_symbolt &lhs,
    const abstract_symbolt &rhs,
    const abstract_symbolt &global_as)
  {
    graph.insert(std::make_pair(new_as,
        std::make_tuple(R_RHS_PROP, lhs, rhs, global_as)));
  }

  void add_lhs_sym(
    const abstract_symbolt &as)
  {
    graph.insert(std::make_pair(as,
        std::make_tuple(R_LHS_SYM, abstract_symbolt(), abstract_symbolt(),
          abstract_symbolt())));
  }

  void add_rhs_sym(
    const abstract_symbolt &as)
  {
    graph.insert(std::make_pair(as,
        std::make_tuple(R_RHS_SYM, abstract_symbolt(), abstract_symbolt(),
          abstract_symbolt())));
  }

  void indent(std::ostream &out, unsigned level) const
  {
    unsigned i=0;
    while(i++<level)
      out << " ";
  }

  void output(std::ostream &out, const abstract_symbolt &as) const
  {
    out << "Propagation graph: \n";
    output(out, 0, as);
  }

  void output(std::ostream &out, unsigned level, const abstract_symbolt &as)
    const
  {
    grapht::const_iterator g_it=graph.find(as);
    assert(g_it!=graph.end());

    indent(out, level);
    as.output(out);
    out << "\n";
    level+=2;

    indent(out, level);

    const valuet &value=g_it->second;

    Reason r=std::get<0>(value);

    switch(r)
    {
    case R_BASE:
      out << "R_BASE";
      break;
    case R_LHS_PROP:
      out << "R_LHS_PROP";
      break;
    case R_RHS_PROP:
      out << "R_RHS_PROP";
      break;
    case R_LHS_SYM:
      out << "R_LHS_SYM";
      break;
    case R_RHS_SYM:
      out << "R_RHS_SYM";
      break;
    default:
      assert(false);
      break;
    }

    if(r==R_LHS_PROP || r==R_RHS_PROP)
    {
      out << "\n";
      indent(out, level);
      std::get<1>(value).output(out); // lhs

      out << "\n";
      indent(out, level);
      std::get<2>(value).output(out); // rhs

      // continue with global
      out << "\n";
      output(out, level, std::get<3>(value));
    }
  }

  grapht graph;
};

class abstract_symbolst
{
public:
  typedef irep_idt idt;

  typedef std::set<abstract_symbolt> as_sett;
  as_sett as_set;

  const namespacet &ns;

  const abstract_symbolst *feasible; // for debugging

  propagation_grapht prop_graph;

  abstract_symbolst(const namespacet &ns) : ns(ns), feasible(NULL) {}

  abstract_symbolst(const exprt &expr, const namespacet &ns) :
    ns(ns), feasible(NULL)
  {
    from_expr(expr);
  }

  abstract_symbolst(const namespacet &ns, const abstract_symbolst *feasible) :
    ns(ns), feasible(feasible) {}

  abstract_symbolst(
    const exprt &expr,
    const namespacet &ns,
    const abstract_symbolst *feasible) :
      ns(ns),
      feasible(feasible)
  {
    from_expr(expr);
  }

  void set_feasible(const abstract_symbolst *_feasible)
  {
    feasible=_feasible;
  }

  // set expression for all symbols
  void set_expr(exprt expr)
  {
    abstract_symbolst tmp(ns);

    for(as_sett::iterator it=as_set.begin(); it!=as_set.end(); it++)
    {
      abstract_symbolt as=*it;
      as.set_expr(expr);
      tmp.add(as);
    }

    as_set.clear();
    as_set.insert(tmp.as_set.begin(), tmp.as_set.end());
  }

  // delete expression for all symbols
  void del_expr()
  {
    set_expr(exprt(ID_nil));
  }

  void limit()
  {
    abstract_symbolst tmp(ns);

    for(as_sett::iterator it=as_set.begin(); it!=as_set.end(); it++)
    {
      abstract_symbolt as=*it;
      as.limit();
      tmp.add(as);
    }

    as_set.clear();
    as_set.insert(tmp.as_set.begin(), tmp.as_set.end());
  }

  // all abstract symbols are well-formed
  bool well_formed() const
  {
    for(as_sett::iterator it=as_set.begin(); it!=as_set.end(); it++)
    {
      if(!it->well_formed())
        return false;
    }

    return true;
  }

  // all abstract symbols are limited
  bool limited() const
  {
    for(as_sett::iterator it=as_set.begin(); it!=as_set.end(); it++)
    {
      if(!it->limited())
        return false;
    }

    return true;
  }

  size_t size() const
  {
    return as_set.size();
  }

  bool empty() const
  {
    return as_set.empty();
  }

  void clear()
  {
    feasible=NULL;
    as_set.clear();
  }

  void add(const abstract_symbolt &as)
  {
    as_set.insert(as);
  }

  // merge other abstract symbols into this set
  void merge(const abstract_symbolst &abstract_symbols)
  {
    as_set.insert(
      abstract_symbols.as_set.begin(),
      abstract_symbols.as_set.end());

    prop_graph.graph.insert(
      abstract_symbols.prop_graph.graph.begin(),
      abstract_symbols.prop_graph.graph.end());
  }

  // merge other non-redundant abstract symbols into this set
  void merge_non_redundant(const abstract_symbolst &abstract_symbols)
  {
    for(as_sett::const_iterator it=abstract_symbols.as_set.begin();
        it!=abstract_symbols.as_set.end(); it++)
    {
      abstract_symbolst tmp(ns);
      tmp.add(*it);

      if(!tmp.exists_affects(*this))
      {
        as_set.insert(*it);
        prop_graph.graph.insert(std::make_pair(
          *it,
          abstract_symbols.prop_graph.graph.at(*it)));
      }
    }
  }

  // print abstract symbol
  void print_as(const std::string &tag, const abstract_symbolt &as)
  {
    const unsigned cw=32; // column width

    size_t n=tag.length();
    assert(n<=cw);

    std::cout << tag;

    unsigned i=n;
    while(i++<cw)
      std::cout << " ";

    std::cout << ": ";
    as.output(std::cout, ns);
    std::cout << std::endl;
  }

  bool handle_lhs(
    const abstract_symbolst &abstract_symbols1, // lhs symbols
    const abstract_symbolst &abstract_symbols2) // rhs symbols
  {
    assert(!empty());

    abstract_symbolst new_symbols(ns);

    if(abstract_symbols1.exists(*this, can_affect_pred))
    {
      // for lhs symbols
      for(as_sett::const_iterator it1=abstract_symbols1.as_set.begin();
          it1!=abstract_symbols1.as_set.end(); it1++)
      {
        abstract_symbolst tmp(ns);
        gather(*it1, can_affect_pred, tmp); // gather affected from global

        if(tmp.empty())
        {
          new_symbols.add(*it1); // add abstract symbol as is
          new_symbols.prop_graph.add_lhs_sym(*it1); // record symbol
        }
        else
        {
          // for affected from global
          for(as_sett::const_iterator it2=tmp.as_set.begin();
              it2!=tmp.as_set.end(); it2++)
          {
            // compute difference
            std::pair<levelt, abstract_symbolt> p=(*it2)-(*it1);

            // now add rhs symbols
            for(as_sett::const_iterator it3=abstract_symbols2.as_set.begin();
                it3!=abstract_symbols2.as_set.end(); it3++)
            {
              // attach difference
              abstract_symbolt new_as(*it3);
              new_as.del_expr();

              assert(new_as.can_add(p.first, p.second));
              new_as=new_as.add(p.first, p.second);
              new_as.limit();

              new_symbols.add(new_as);
              new_symbols.prop_graph.add_lhs_prop(
                new_as, // new
                *it1,   // lhs
                *it3,   // rhs
                *it2);  // global
            }
          }
        }
      }

      size_t n=size();
      // single point of insertion of new elements into global
      new_symbols.del_expr();
      new_symbols.limit();
      //merge(new_symbols);
      merge_non_redundant(new_symbols);
      if(size()!=n)
        return true;
    }

    return false;
  }

  bool handle_rhs(
    const abstract_symbolst &abstract_symbols1, // lhs symbols
    const abstract_symbolst &abstract_symbols2) // rhs symbols
  {
    assert(!empty());

    abstract_symbolst new_symbols(ns);

    if(abstract_symbols2.exists(*this, takes_address_pred))
    {
      // for rhs symbols
      for(as_sett::const_iterator it1=abstract_symbols2.as_set.begin();
          it1!=abstract_symbols2.as_set.end(); it1++)
      {
        abstract_symbolst tmp(ns);

        // gather address taken from global
        gather(*it1, takes_address_pred, tmp);

        if(tmp.empty())
        {
          new_symbols.add(*it1); // add abstract symbol as is
          new_symbols.prop_graph.add_rhs_sym(*it1); // record symbol
        }
        else
        {
          // for address taken from global
          for(as_sett::const_iterator it2=tmp.as_set.begin();
              it2!=tmp.as_set.end(); it2++)
          {
            // compute difference
            std::pair<levelt, abstract_symbolt> p=(*it2)-(*it1);

            // now add lhs symbols
            for(as_sett::const_iterator it3=abstract_symbols1.as_set.begin();
                it3!=abstract_symbols1.as_set.end(); it3++)
            {
              // attach difference
              abstract_symbolt new_as(*it3);
              new_as.del_expr();

              assert(new_as.can_add(p.first, p.second));
              new_as=new_as.add(p.first, p.second);
              new_as.limit();

              new_symbols.add(new_as);
              new_symbols.prop_graph.add_rhs_prop(
                new_as, // new
                *it3,   // lhs
                *it1,   // rhs
                *it2);  // global
            }
          }
        }
      }

      size_t n=size();
      // single point of insertion of new elements into global
      new_symbols.del_expr();
      new_symbols.limit();
      //merge(new_symbols);
      merge_non_redundant(new_symbols);
      if(size()!=n)
        return true;
    }

    return false;
  }

  static bool can_affect_pred(
    const abstract_symbolt &as1,
    const abstract_symbolt &as2)
  {
    return as1.can_affect(as2);
  }

  static bool takes_address_pred(
    const abstract_symbolt &as1,
    const abstract_symbolt &as2)
  {
    return as1.takes_address(as2);
  }

  // internal
  void from_expr(
    const exprt &expr,
    unsigned level, // numeric level
    abstract_symbolst &abstract_symbols) // where symbols are put
  {
    assert(level>=0);

    irep_idt id=expr.id();
    abstract_symbolst tmp(ns); // abstract symbols of subexpressions

    if(id==ID_symbol)
    {
      const symbol_exprt &symbol_expr=to_symbol_expr(expr);
      abstract_symbolt as(symbol_expr.get_identifier(), level);
      assert(as.length()==1);
      assert(as.well_formed());
      tmp.add(as);
    }
    else if(id==ID_dereference)
    {
      const dereference_exprt &dereference_expr=to_dereference_expr(expr);
      from_expr(dereference_expr.pointer(), level+1, tmp);
    }
    else if(id==ID_address_of)
    {
      const address_of_exprt &address_of_expr=to_address_of_expr(expr);
      assert(level>=0);
      from_expr(address_of_expr.object(), level-1, tmp);
    }
    else if(id==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(expr);
      const exprt &array=index_expr.array();
      const exprt &index=index_expr.index();
      from_expr(array, level+1, tmp);
      from_expr(index, level+1, tmp);
    }
    else if(id==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(expr);
      const exprt &compound=member_expr.compound();
      irep_idt component=member_expr.get_component_name();
      from_expr(compound, 1, tmp);

      abstract_symbolst tmp2(ns);

      for(as_sett::iterator it=tmp.as_set.begin();
          it!=tmp.as_set.end(); it++)
      {
        abstract_symbolt abstract_symbol=*it;
        abstract_symbol.push_back(component, level);
        assert(abstract_symbol.well_formed());
        tmp2.add(abstract_symbol);
      }

      tmp.clear();
      tmp.as_set.insert(tmp2.as_set.begin(), tmp2.as_set.end());
    }
    else
    {
      forall_operands(it, expr)
      {
        from_expr(*it, level, tmp);
      }
    }

    for(as_sett::iterator it=tmp.as_set.begin();
        it!=tmp.as_set.end(); it++)
    {
      assert(it->well_formed());
    }

    abstract_symbols.merge(tmp); // finally update symbol set
  }

  // indicate that current abstract symbols are base symbols
  void set_base()
  {
    assert(prop_graph.empty());
    for(as_sett::const_iterator it=as_set.begin(); it!=as_set.end(); it++)
    {
      prop_graph.add_base(*it);
    }
  }

  void from_expr(const exprt &expr)
  {
    assert(empty());
    abstract_symbolst abstract_symbols(ns);
    from_expr(expr, 1, abstract_symbols);
    abstract_symbols.set_expr(expr);
    abstract_symbols.set_base();
    abstract_symbols.limit();
    assert(abstract_symbols.limited());
    merge(abstract_symbols); // merge into current empty set
  }

  void add_expr(const exprt &expr)
  {
    abstract_symbolst abstract_symbols(ns);
    from_expr(expr, 1, abstract_symbols);
    abstract_symbols.set_expr(expr);
    abstract_symbols.set_base(); // added expressions are always base
    abstract_symbols.limit();
    assert(abstract_symbols.limited());
    merge(abstract_symbols); // merge into current set
  }

  bool exists(
    const abstract_symbolst &other,
    bool (*pred)(const abstract_symbolt &as1, const abstract_symbolt &as2))
    const
  {
    for(as_sett::const_iterator it1=as_set.begin();
        it1!=as_set.end(); it1++)
    {
      // new element to speed up search
      elementt element=it1->front();
      element.level=levelt();
      abstract_symbolt start(element);

      idt id=element.id;

      as_sett::const_iterator it2=other.as_set.lower_bound(start);
      if(it2==other.as_set.end())
      {
        // move forward until next id
        it1++;
        while(it1!=as_set.end() && it1->front().id==id)
          it1++;

        it1--; // continue will lead to an increment
        continue;
      }

      while(it2!=other.as_set.end() && it2->front().id==id)
      {
        if(pred(*it1, *it2))
        {
          return true;
        }
        it2++;
      }
    }

    return false;
  }

  bool exists_affects(const abstract_symbolst &other) const
  {
    return exists(other, can_affect_pred);
  }

  bool exists_takes_address(const abstract_symbolst &other) const
  {
    return exists(other, takes_address_pred);
  }

  void gather(
    const abstract_symbolt &as,
    bool (*pred)(const abstract_symbolt &as1, const abstract_symbolt &as2),
    abstract_symbolst &abstract_symbols) // output
  {
    assert(abstract_symbols.empty());

    // new element to speed up search
    elementt element=as.front();
    element.level=levelt();
    abstract_symbolt start(element);

    idt id=element.id;

    as_sett::const_iterator it=as_set.lower_bound(start);
    if(it==as_set.end())
      return;

    while(it!=as_set.end() && it->front().id==id)
    {
      if(pred(as, *it))
        abstract_symbols.add(*it);
      it++;
    }
  }

  // output all symbols
  void output(std::ostream &out) const
  {
    for(as_sett::const_iterator it=as_set.begin();
        it!=as_set.end();)
    {
      it->output(out, ns);
      if(++it!=as_set.end())
      {
        out << "\n";
      }
    }
  }
};

class global_dependency_analysist
{
public:
  global_dependency_analysist(
    const goto_functionst &goto_functions,
    const namespacet &ns,
    bool ignore_indices=true) :
      goto_functions(goto_functions),
      ns(ns),
      ignore_indices(ignore_indices),
      num_its(0)
  {
    assert(gda_max_num>=3);
    assert(gda_max_len>=2);

    assert(gda_max_num<=20);
    assert(gda_max_len<=10);

#if 1
    // do unit tests (cheap)
    test1();
    test2();
    test3();
    test4();
#endif
  }

  typedef std::vector<exprt> expr_vect;

  typedef goto_programt::const_targett locationt;
  typedef std::set<locationt> location_sett;

  typedef std::set<irep_idt> id_sett;
  typedef std::vector<exprt> argumentst;

  typedef goto_functionst::goto_functiont goto_functiont;

  // unit tests
  void test1();
  void test2();
  void test3();
  void test4();

  // do dependency analysis
  void operator()(
    const expr_vect &expr_vec, // input
    location_sett &location_set); // output

  bool is_handled(irep_idt id);

  bool handle_thread_create(
    locationt l,
    const argumentst &args,
    location_sett &other_locations,
    abstract_symbolst &global);

  bool handle_function_call(
    irep_idt id,
    locationt l,
    const exprt &lhs,
    const argumentst &args,
    location_sett &other_locations,
    abstract_symbolst &global);

  // get ids of functions that could be used as threads
  void get_thread_functions(id_sett &funcs);

  // get the expressions used in returns
  void get_returns(
    const goto_programt &goto_program,
    expr_vect &expr_vec,
    location_sett &location_set);

  void postprocess(
    location_sett &location_set, // dependent locations so far
    abstract_symbolst &global);

  // abstract symbols in expressions in assignments and functions
  void compute_feasible(abstract_symbolst &abstract_symbols);

protected:
  const goto_functionst &goto_functions;
  const namespacet &ns;
  bool ignore_indices;

  unsigned num_its; // number of fixpoint iterations used
};

#endif
