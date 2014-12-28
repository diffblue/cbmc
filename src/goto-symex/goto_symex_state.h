/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H

#include <cassert>

#include <util/guard.h>
#include <util/std_expr.h>
#include <util/i2string.h>

#include <pointer-analysis/value_set.h>
#include <goto-programs/goto_functions.h>

#include "symex_target.h"

// central data structure: state
class goto_symex_statet
{
public:
  goto_symex_statet();

  // distance from entry
  unsigned depth;

  guardt guard;
  symex_targett::sourcet source;
  symex_targett *symex_target;

  void initialize(const goto_functionst &goto_functions);

  // we have a two-level renaming

  typedef std::map<irep_idt, irep_idt> original_identifierst;

  // we remember all L1 renamings
  typedef std::set<irep_idt> l1_historyt;
  l1_historyt l1_history; 
  
  struct renaming_levelt
  {
  public:
    virtual irep_idt current_name(const irep_idt &identifier) const=0;
    virtual irep_idt name(const irep_idt &identifier, unsigned count) const=0;
    virtual ~renaming_levelt() { }

    typedef std::map<irep_idt, unsigned> current_namest;
    current_namest current_names;
    
    void remove(const irep_idt &identifier) { current_names.erase(identifier); }
    const irep_idt &get_original_name(const irep_idt &identifier) const;
    void get_original_name(exprt &expr) const;
    void get_original_name(typet &type) const;
    void print(std::ostream &out) const;
    unsigned current_count(const irep_idt &identifier) const;
    
    irep_idt operator()(const irep_idt &identifier)
    {
      // see if it's already renamed
      if(is_renamed(identifier)) return identifier;

      // record
      irep_idt i=current_name(identifier);
      original_identifiers[i]=identifier;
      return i;
    }

    inline void operator()(symbol_exprt &expr)
    {
      expr.set_identifier(operator()(expr.get_identifier()));
    }
    
    irep_idt rename_identifier(const irep_idt &identifier, unsigned count)
    {
      current_names[identifier]=count;
      irep_idt new_name=name(identifier, count);
      original_identifiers[new_name]=identifier;
      return new_name;
    }
    
    irep_idt increase_counter(const irep_idt &identifier)
    {
      return rename_identifier(identifier, current_names[identifier]+1);
    }
    
    inline bool is_renamed(const irep_idt &identifier) const
    {
      return original_identifiers.find(identifier)!=original_identifiers.end();
    }
    
    void restore_from(const current_namest &other)
    {
      for(current_namest::const_iterator
          it=other.begin();
          it!=other.end();
          it++)
      {
        // could be done faster exploing ordering
        current_names[it->first]=it->second;
      }
    }

    void get_variables(std::set<irep_idt> &vars) const
    {
      for(current_namest::const_iterator it=current_names.begin();
          it!=current_names.end();
          it++)
        vars.insert(it->first);
    }

  protected:
    original_identifierst original_identifiers;
  };
  
  // level 0 -- threads!
  // renaming built for one particular interleaving
  struct level0t:public renaming_levelt
  {
  public:
    virtual irep_idt name(const irep_idt &identifier, unsigned thread_nr) const
    {
      return id2string(identifier)+"!"+i2string(thread_nr);
    }

    virtual irep_idt current_name(const irep_idt &identifier) const
    { // never called
      assert(false);
      return irep_idt();
    }

    irep_idt operator()(
      const irep_idt &identifier,
      const namespacet &ns,
      unsigned thread_nr);

    level0t() { }
    virtual ~level0t() { }
  } level0;

  // level 1 -- function frames
  // this is to preserve locality in case of recursion
  
  struct level1t:public renaming_levelt
  {
  public:
    virtual irep_idt name(const irep_idt &identifier, unsigned frame) const
    {
      return id2string(identifier)+"@"+i2string(frame);
    }
    
    virtual irep_idt current_name(const irep_idt &identifier) const
    {
      // see if it's already renamed
      if(is_renamed(identifier))
        return identifier;

      // rename only if needed
      const current_namest::const_iterator it=
        current_names.find(identifier);
    
      if(it==current_names.end())
        return identifier;
      else
        return name(identifier, it->second);
    }

    level1t() { }
    virtual ~level1t() { }
  } level1;
  
  // level 2 -- SSA

  struct level2t:public renaming_levelt
  {
  public:
    virtual irep_idt name(const irep_idt &identifier, unsigned count) const
    {
      return id2string(identifier)+"#"+i2string(count);
    }

    virtual irep_idt current_name(const irep_idt &identifier) const
    {
      // see if it's already renamed
      if(is_renamed(identifier))
        return identifier;

      // _always_ rename
      return name(identifier, current_count(identifier));
    }
    
    level2t() { }
    virtual ~level2t() { }
  } level2;
  
  // this maps L1 names to (L2) constants
  class propagationt
  {
  public:
    typedef std::map<irep_idt, exprt> valuest;
    valuest values;
    void operator()(exprt &expr);

    void remove(const irep_idt &identifier)
    {
      values.erase(identifier);
    }
    
  } propagation;
  
  typedef enum { L0=0, L1=1, L2=2 } levelt;

  // performs renaming _up to_ the given level
  irep_idt rename_identifier(const irep_idt &identifier, const namespacet &ns, levelt level=L2);
  void rename(exprt &expr, const namespacet &ns, levelt level=L2);
  void rename(typet &type, const namespacet &ns, levelt level=L2);
  
  void rename_address(exprt &expr, const namespacet &ns, levelt level);
  
  void assignment(
    symbol_exprt &lhs, // L0/L1
    const exprt &rhs,  // L2
    const namespacet &ns,
    bool record_value);

  // what to propagate
  bool constant_propagation(const exprt &expr) const;
  bool constant_propagation_reference(const exprt &expr) const;

  // undoes all levels of renaming
  const irep_idt &get_original_name(const irep_idt &identifier) const;
  void get_original_name(exprt &expr) const;
  void get_original_name(typet &type) const;
  
  // uses level 1 names, and is used to
  // do dereferencing
  value_sett value_set;

  class goto_statet
  {
  public:
    unsigned depth;
    level2t::current_namest level2_current_names;
    value_sett value_set;
    guardt guard;
    propagationt propagation;
    unsigned atomic_section_id;
    
    explicit goto_statet(const goto_symex_statet &s):
      depth(s.depth),
      level2_current_names(s.level2.current_names),
      value_set(s.value_set),
      guard(s.guard),
      propagation(s.propagation),
      atomic_section_id(s.atomic_section_id)
    {
    }

    // the below replicate levelt2 member functions
    void level2_get_variables(std::set<irep_idt> &vars) const
    {
      for(level2t::current_namest::const_iterator
          it=level2_current_names.begin();
          it!=level2_current_names.end();
          it++)
        vars.insert(it->first);
    }

    unsigned level2_current_count(const irep_idt &identifier) const
    {
      level2t::current_namest::const_iterator it=
        level2_current_names.find(identifier);
      return it==level2_current_names.end()?0:it->second;
    }

    irep_idt level2_current_name(const irep_idt &identifier) const
    {
      return id2string(identifier)+"#"+i2string(level2_current_count(identifier));
    }
  };

  // gotos
  typedef std::list<goto_statet> goto_state_listt;
  typedef std::map<goto_programt::const_targett, goto_state_listt> goto_state_mapt;

  // stack frames -- these are used for function calls and
  // for exceptions
  class framet
  {
  public:
    // function calls  
    irep_idt function_identifier;
    goto_state_mapt goto_state_map;
    symex_targett::sourcet calling_location;

    goto_programt::const_targett end_of_function;
    exprt return_value;
    bool hidden_function;

    renaming_levelt::current_namest old_level1;
    
    typedef std::set<irep_idt> local_variablest;
    local_variablest local_variables;
    
    framet():
      return_value(nil_exprt()),
      hidden_function(false)
    {
    }

    // exceptions
    typedef std::map<irep_idt, goto_programt::targett> catch_mapt;
    catch_mapt catch_map;

    // loop and recursion unwinding
    struct loop_infot
    {
      loop_infot():
        count(0),
        is_recursion(false)
      {
      }

      unsigned count;
      bool is_recursion;
    };
    typedef hash_map_cont<irep_idt, loop_infot, irep_id_hash>
      loop_iterationst;
    loop_iterationst loop_iterations;
  };

  typedef std::vector<framet> call_stackt;

  inline call_stackt &call_stack()
  {
    assert(source.thread_nr<threads.size());
    return threads[source.thread_nr].call_stack;
  }
  
  inline const call_stackt &call_stack() const
  {
    assert(source.thread_nr<threads.size());
    return threads[source.thread_nr].call_stack;
  }
  
  inline framet &top()
  {
    assert(!call_stack().empty());
    return call_stack().back();
  }

  inline const framet &top() const
  {
    assert(!call_stack().empty());
    return call_stack().back();
  }
  
  inline framet &new_frame() { call_stack().push_back(framet()); return top(); }
  inline void pop_frame() { call_stack().pop_back(); }
  inline const framet &previous_frame() { return *(--(--call_stack().end())); }

  // threads
  unsigned atomic_section_id;
  typedef std::pair<unsigned, std::list<guardt> > a_s_r_entryt;
  typedef hash_map_cont<symbol_exprt, a_s_r_entryt, irep_hash> read_in_atomic_sectiont;
  typedef std::list<guardt> a_s_w_entryt;
  typedef hash_map_cont<symbol_exprt, a_s_w_entryt, irep_hash> written_in_atomic_sectiont;
  read_in_atomic_sectiont read_in_atomic_section;
  written_in_atomic_sectiont written_in_atomic_section;
  
  class threadt
  {
  public:
    goto_programt::const_targett pc;
    guardt guard;
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id;

    threadt():
      atomic_section_id(0)
    {
    }
  };

  typedef std::vector<threadt> threadst;
  threadst threads;
  
  bool l2_thread_read_encoding(symbol_exprt &expr, const namespacet &ns);
  bool l2_thread_write_encoding(const symbol_exprt &expr, const namespacet &ns);

  void switch_to_thread(unsigned t);
  bool record_events;
};

#endif
