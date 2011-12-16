/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H

#include <assert.h>

#include <guard.h>

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
  
  void initialize(const goto_functionst &goto_functions);

  // we have a two-level renaming

  typedef std::map<irep_idt, irep_idt> original_identifierst;
  typedef std::set<irep_idt> declaration_historyt;

  // we remember all declarations
  declaration_historyt declaration_history; 
  
  struct renaming_levelt
  {
  public:
    typedef std::map<irep_idt, unsigned> current_namest;
    current_namest current_names;

    virtual void remove(const irep_idt &identifier) { current_names.erase(identifier); }

    virtual const irep_idt &get_original_name(const irep_idt &identifier) const;
    virtual void get_original_name(exprt &expr) const;
    virtual void get_original_name(typet &type) const;

    virtual void operator()(exprt &expr, const namespacet &ns)=0;
    virtual void operator()(typet &type, const namespacet &ns);
    virtual std::string operator()(const irep_idt &identifier) const=0;
    
    virtual ~renaming_levelt() { }
    
    virtual void print(std::ostream &out) const { }

  protected:
    original_identifierst original_identifiers;
  };
  
  // level 0 -- threads!
  // renaming built for one particular interleaving

  #if 0
  struct level0t:public renaming_levelt
  {
  public:
    std::string name(
      const irep_idt &identifier,
      unsigned thread_nr) const;

    virtual void rename(irep_idt& identifier, const namespacet& ns, unsigned thread_nr);
    virtual void operator()(exprt &expr, const namespacet &ns) { assert(false); }
    virtual std::string operator()(const irep_idt &identifier) const;

    level0t() { }
    virtual ~level0t() { }

    virtual void print(std::ostream &out) const;
  } level0;
  #endif

  // level 1 -- function frames
  // this is to preserve locality in case of recursion
  
  struct level1t:public renaming_levelt
  {
  public:
    std::string name(
      const irep_idt &identifier,
      unsigned frame) const;
      
    using renaming_levelt::operator();

    virtual void operator()(exprt &expr, const namespacet &ns);
    virtual std::string operator()(const irep_idt &identifier) const;
    
    void rename(const irep_idt &identifier, unsigned frame)
    {
      current_names[identifier]=frame;
      original_identifiers[name(identifier, frame)]=identifier;
    }

    level1t() { }
    virtual ~level1t() { }

    virtual void print(std::ostream &out) const;
  };
  
  // level 2 -- SSA

  struct level2t:public renaming_levelt
  {
  public:
    using renaming_levelt::operator();

    virtual void operator()(exprt &expr, const namespacet &ns);
    virtual std::string operator()(const irep_idt &identifier) const;
    virtual void remove(const irep_idt &identifier) { current_names.erase(identifier); }

    std::string name(
      const irep_idt &identifier,
      unsigned count) const;

    struct valuet
    {
      unsigned count;
      exprt constant;
      
      valuet():
        count(0),
        constant(static_cast<const exprt &>(get_nil_irep()))
      {
      }
    };
    
    typedef std::map<irep_idt, valuet> current_namest;
    current_namest current_names;
    
    void rename(const irep_idt &identifier, unsigned count)
    {
      valuet &entry=current_names[identifier];
      entry.count=count;
      original_identifiers[name(identifier, entry.count)]=identifier;
    }

    void get_variables(std::set<irep_idt> &vars) const
    {
      for(current_namest::const_iterator it=current_names.begin();
          it!=current_names.end();
          it++)
        vars.insert(it->first);
    }

    unsigned current_number(const irep_idt &identifier) const;

    level2t() { }
    virtual ~level2t() { }

    virtual void print(std::ostream &out) const;
  } level2;
  
  typedef enum { L1, L2 } levelt;

  void rename(exprt &expr, const namespacet &ns, levelt level=L2);
  void rename_address(exprt &expr, const namespacet &ns);
  void rename(typet &type, const namespacet &ns);
  
  void assignment(
    symbol_exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    bool record_value);

  // what to propagate
  bool constant_propagation(const exprt &expr) const;
  bool constant_propagation_reference(const exprt &expr) const;

  // undoes all levels of renaming
  const irep_idt &get_original_name(const irep_idt &identifier) const;
  void get_original_name(exprt &expr) const;
  void get_original_name(typet &type) const;
  
  // does all levels of renaming
  std::string current_name(
      const namespacet &ns,
      const irep_idt &identifier) const
  {
    return current_name(level2, ns, identifier);
  }

  std::string current_name(
    const level2t &level2,
    const namespacet &ns,
    const irep_idt &identifier) const
  {
    return level2(top().level1(identifier));
    //return level2(top().level1(level0(identifier, ns, source.thread_nr)));
  }
  
  // uses level 1 names, and is used to
  // do dereferencing
  value_sett value_set;

  class goto_statet
  {
  public:
    unsigned depth;
    level2t level2;
    value_sett value_set;
    guardt guard;
    
    explicit goto_statet(const goto_symex_statet &s):
      depth(s.depth),
      level2(s.level2),
      value_set(s.value_set),
      guard(s.guard)
    {
    }
  };

  std::string current_name(
    const goto_statet &goto_state,
    const namespacet &ns,
    const irep_idt &identifier) const
  {
    return current_name(goto_state.level2, ns, identifier);
  }
  
  // gotos
  typedef std::list<goto_statet> goto_state_listt;
  typedef std::map<goto_programt::const_targett, goto_state_listt> goto_state_mapt;

  // function calls
  class framet
  {
  public:
    irep_idt function_identifier;
    goto_state_mapt goto_state_map;
    level1t level1;
    symex_targett::sourcet calling_location;

    goto_programt::const_targett end_of_function;
    exprt return_value;
    
    typedef std::set<irep_idt> local_variablest;
    local_variablest local_variables;
    
    framet():
      return_value(static_cast<const exprt &>(get_nil_irep()))
    {
    }
  };
  
  typedef std::vector<framet> call_stackt;
  call_stackt call_stack;
  
  inline framet &top()
  {
    assert(!call_stack.empty());
    return call_stack.back();
  }

  inline const framet &top() const
  {
    assert(!call_stack.empty());
    return call_stack.back();
  }

  inline framet &new_frame() { call_stack.push_back(framet()); return call_stack.back(); }
  inline void pop_frame() { call_stack.pop_back(); }
  inline const framet &previous_frame() { return *(--(--call_stack.end())); }
};

#endif
