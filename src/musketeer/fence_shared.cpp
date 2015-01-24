/*******************************************************************\

Module:

Author: Vincent Nimal

\*******************************************************************/

#include <iostream>
#include <sstream>
#include <fstream>
#include <list>
#include <vector>
#include <set>

#include <util/i2string.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/location.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/message.h>

#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_functions.h>
#include <goto-instrument/wmm/goto2graph.h>
#include <goto-instrument/rw_set.h>
//#include <goto-instrument/nondet_volatile.h>

#include "fence_shared.h"

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#endif

#define OUTPUT(s,fence,file,line,id,type)  s<<fence<<"|"<<file<<"|"<<line<<"|"\
  <<id<<"|"<<type<<std::endl

class simple_insertiont {
protected:
  messaget& message;
  value_setst& value_sets;
  const symbol_tablet& symbol_table;
  const namespacet ns;
  const goto_functionst& goto_functions;

  struct { 
    std::list<symbol_exprt> writes;
    std::list<symbol_exprt> reads;
  } fenced_edges;

  virtual void compute()=0;

  /* prints final results */
  void print_to_file() const
  {
    source_locationt emptyloc;

    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;

    for(std::list<symbol_exprt>::const_iterator it=fenced_edges.writes.begin();
      it!=fenced_edges.writes.end();
      ++it)
    {
      std::ostringstream s;

      if(it->location().as_string().empty()) continue;

      OUTPUT(s, "fence", it->location().get_file(), it->location().get_line(),
        ns.lookup(it->get_identifier()).base_name, "Write");
      non_redundant_display.insert(s.str());
    }

    for(std::list<symbol_exprt>::const_iterator it=fenced_edges.reads.begin();
      it!=fenced_edges.reads.end();
      ++it)
    {
      std::ostringstream s;

      if(it->location().as_string().empty()) continue;

      OUTPUT(s, "fence", it->location().get_file(), it->location().get_line(),
        ns.lookup(it->get_identifier()).base_name, "Read");
      non_redundant_display.insert(s.str());
    }

    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

public:
  explicit simple_insertiont (
    messaget& _message,
    value_setst& _value_sets,
    const symbol_tablet& _symbol_table,
    const goto_functionst& _goto_functions)
    :message(_message), value_sets(_value_sets), symbol_table(_symbol_table),
      ns(_symbol_table), goto_functions(_goto_functions)
  {}

  virtual ~simple_insertiont() {}

  void do_it() {
    compute();
    print_to_file();
  }
};

/* fence insertion for all shared accesses */
class fence_all_sharedt:public simple_insertiont
{
protected:
  void compute();

public:
  fence_all_sharedt (
    messaget& _message,
    value_setst& _value_sets,
    const symbol_tablet& _symbol_table,
    const goto_functionst& _goto_functions)
    :simple_insertiont(_message, _value_sets,_symbol_table,_goto_functions)
  {}
}; 

/* fence insertion for all shared accesses */
class fence_all_shared_aegt:public fence_all_sharedt
{
protected:
  void compute();
  std::set<irep_idt> visited_functions;
  void fence_all_shared_aeg_explore(const goto_programt& code
#ifdef LOCAL_MAY
  , local_may_aliast& local_may
#endif
);

public:
  fence_all_shared_aegt (
    messaget& _message,
    value_setst& _value_sets,
    const symbol_tablet& _symbol_table,
    const goto_functionst& _goto_functions)
    :fence_all_sharedt(_message, _value_sets, _symbol_table, _goto_functions)
  {}
}; 

/* fence insertion for volatile accesses (a la MSVC) */
class fence_volatilet:public simple_insertiont
{
protected:
  void compute();
  bool is_volatile(const typet& src) const;

public:
  fence_volatilet (
    messaget& _message,
    value_setst& _value_sets,
    const symbol_tablet& _symbol_table,
    const goto_functionst& _goto_functions)
    :simple_insertiont(_message, _value_sets, _symbol_table, _goto_functions)
  {}
};

/*******************************************************************\

Function: is_volatile

  Inputs:

 Outputs:

 Purpose: we can determine whether an access is volatile just by looking at 
   the type of the variables involved in the expression. We assume that the
   program is correctly typed (i.e., volatile-marked)

\*******************************************************************/

bool fence_volatilet::is_volatile (const typet &src) const
{
  if(src.get_bool(ID_C_volatile)) return true;

//  std::cout << "type: " << src << " has sub: " << src.subtypes().empty() /*src.has_subtypes()*/ <<  std::endl;
  if(src.id()==ID_symbol)
  {
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(to_symbol_type(src).get_identifier());
    assert(s_it!=symbol_table.symbols.end());
    return is_volatile(s_it->second.type);
  }
  else if(src.has_subtype())
  {
    /* if a pointer points to a volatile variable, then any access through this
       pointer has also to be considered as volatile (conservative) */
    if(is_volatile(src.subtype()))
      return true;
  }
  else if(src.has_subtypes()) 
  {
    /* if a pointer points to a volatile variable, then any access through this
       pointer has also to be considered as volatile (conservative) */
    bool vol=false;
    for(typet::subtypest::const_iterator it=src.subtypes().begin();
      it!=src.subtypes().end();
      ++it)
    {
      std::cout << *it << std::endl;
      vol|=is_volatile(*it);
      if(vol)
        break;
    }
    return vol;
  }

  return false;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_volatilet::compute()
{
  std::cout << "--------" << std::endl;

  forall_goto_functions(f_it, goto_functions)
  {
    #ifdef LOCAL_MAY
    local_may_aliast local_may(f_it->second);
    #endif

    forall_goto_program_instructions(i_it, f_it->second.body) {
        rw_set_loct rw_set(ns, value_sets, i_it
        #ifdef LOCAL_MAY
        , local_may
        #endif
        );
        forall_rw_set_w_entries(w_it, rw_set)
        {
          if(has_prefix(id2string(w_it->second.object), CPROVER_PREFIX))
            continue;

          try {
            message.debug() << "debug: " 
              << id2string(w_it->second.object) << messaget::eom;
            const symbolt& var=ns.lookup(w_it->second.object);
            if(is_volatile(var.type))
            {
              message.debug() << "volatile: "
                << id2string(w_it->second.object) << messaget::eom; 
              fenced_edges.writes.push_front(w_it->second.symbol_expr); 
            }
          } catch (std::string s) { 
            message.warning() << "failed to find" << s 
              << messaget::eom; 
            continue; 
          }
        }
        forall_rw_set_r_entries(r_it, rw_set)
        {
          if(has_prefix(id2string(r_it->second.object), CPROVER_PREFIX))
            continue;

          try {
            message.debug() << "debug: " 
              << id2string(r_it->second.object) << messaget::eom;
            const symbolt& var=ns.lookup(r_it->second.object);
 	    #if 0
            if(var.is_volatile && !var.is_thread_local)
            #endif
            if(is_volatile(var.type))
            {
              message.debug() << "volatile: " 
                << id2string(r_it->second.object) << messaget::eom; 
              fenced_edges.reads.push_front(r_it->second.symbol_expr); 
            }
          } catch (std::string s) { 
            message.warning() << "failed to find" << s 
              << messaget::eom; 
            continue; 
          }
        }
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_all_sharedt::compute()
{
  std::cout << "--------" << std::endl;

  forall_goto_functions(f_it, goto_functions)
  {
#ifdef LOCAL_MAY
    local_may_aliast local_may(f_it->second);
#endif

    forall_goto_program_instructions(i_it, f_it->second.body) {
        if(i_it->is_function_call())
          continue;

        rw_set_with_trackt rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
        , local_may
#endif
        );
        forall_rw_set_w_entries(w_it, rw_set)
        {
          if(has_prefix(id2string(w_it->second.object), CPROVER_PREFIX))
            continue;

          try {
            const symbolt& var=ns.lookup(w_it->second.object);
            message.debug() << "debug: " 
              << id2string(w_it->second.object) << " shared: " << var.is_shared()
              << " loc: " << w_it->second.symbol_expr.source_location() 
              << messaget::eom;
            if(var.is_shared()) 
            {
              /* this variable has perhaps been discovered after dereferencing
                 a pointer. We want to report this pointer */
              std::map<const irep_idt, const irep_idt>& ref=
                rw_set.dereferenced_from;
              if(ref.find(w_it->second.object)!=ref.end())
              {
                const irep_idt from=ref[w_it->second.object];
                const rw_set_baset::entryt& entry= ( 
                  rw_set.set_reads.find(from)!=rw_set.set_reads.end() ?
                  rw_set.r_entries[from] :
                  rw_set.w_entries[from]
                );
                message.debug() << "shared: (through "
                  << id2string(w_it->second.object) << ") " << entry.object
                  << messaget::eom;
                fenced_edges.writes.push_front(entry.symbol_expr);
              }
              else {
                message.debug() << "shared: "
                  << id2string(w_it->second.object) << " -> " 
                  << w_it->second.object << messaget::eom;
                fenced_edges.writes.push_front(w_it->second.symbol_expr);
              }
            }
          } catch (std::string s) { 
            message.warning() << "failed to find" << s 
              << messaget::eom; 
            continue; 
          }
        }
        forall_rw_set_r_entries(r_it, rw_set)
        {
          if(has_prefix(id2string(r_it->second.object), CPROVER_PREFIX))
            continue;

          try {
            const symbolt& var=ns.lookup(r_it->second.object);
            message.debug() << "debug: " 
              << id2string(r_it->second.object) << " shared: "
              << var.is_shared() << " loc: " 
              << r_it->second.symbol_expr.location() << messaget::eom;
            if(var.is_shared()) 
            {
              /* this variable has perhaps been discovered after dereferencing
                 a pointer. We want to report this pointer */
              std::map<const irep_idt, const irep_idt>&
                ref=rw_set.dereferenced_from;
              if(ref.find(r_it->second.object)!=ref.end())
              {
                const irep_idt from=ref[r_it->second.object];
                const rw_set_baset::entryt& entry=(
                  rw_set.set_reads.find(from)!=rw_set.set_reads.end() ?
                  rw_set.r_entries[from] :
                  rw_set.w_entries[from]
                );

                message.debug() << "shared: (through "
                  << id2string(r_it->second.object) << ") " << entry.object
                  << messaget::eom;
                fenced_edges.reads.push_front(entry.symbol_expr);
              }
              else {
                message.debug() << "shared: " 
                  << id2string(r_it->second.object) << " -> " 
                  << r_it->second.object << messaget::eom;
                fenced_edges.reads.push_front(r_it->second.symbol_expr);
              }
            }
          } catch (std::string s) { 
            message.warning() << "failed to find" << s 
              << messaget::eom; 
            continue; 
          }
       }
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_all_shared_aegt::compute()
{
  message.status() << "--------" << messaget::eom;

  const goto_functionst::goto_functiont& main=
    goto_functions.function_map.find(goto_functionst::entry_point())->second;
  #ifdef LOCAL_MAY
  local_may_aliast local_may(main);
  #endif

  fence_all_shared_aeg_explore(main.body
#ifdef LOCAL_MAY
  , local_may
#endif
  );
}

void fence_all_shared_aegt::fence_all_shared_aeg_explore(const goto_programt& code
#ifdef LOCAL_MAY
  , local_may_aliast& local_may
#endif
) 
{
  forall_goto_program_instructions(i_it, code) {
    if(i_it->is_function_call())
    {
      const exprt& fun=to_code_function_call(i_it->code).function();

      if(fun.id()!=goto_functionst::entry_point()) continue;

      const irep_idt& fun_id=to_symbol_expr(fun).get_identifier();

      if(visited_functions.find(fun_id)!=visited_functions.end())
        continue;

      visited_functions.insert(fun_id);
      fence_all_shared_aeg_explore(goto_functions.function_map.find(fun_id)->second.body
#ifdef LOCAL_MAY
        , local_may
#endif
      );
      visited_functions.erase(fun_id);
    }

    rw_set_with_trackt rw_set(ns, value_sets, i_it
      #ifdef LOCAL_MAY
      , local_may
      #endif
    );
    forall_rw_set_w_entries(w_it, rw_set)
    {
      if(has_prefix(id2string(w_it->second.object), CPROVER_PREFIX))
        continue;

      try {
        const symbolt& var=ns.lookup(w_it->second.object);
        message.debug() << "debug: " 
          << id2string(w_it->second.object) << " shared: "
          << var.is_shared() << " loc: " 
          << w_it->second.symbol_expr.location() << messaget::eom;
        if(var.is_shared()) 
        {
          /* this variable has perhaps been discovered after dereferencing
             a pointer. We want to report this pointer */
          std::map<const irep_idt, const irep_idt>&
            ref=rw_set.dereferenced_from;
          if(ref.find(w_it->second.object)!=ref.end())
          {
            const irep_idt from=ref[w_it->second.object];
            const rw_set_baset::entryt& entry=(
                rw_set.set_reads.find(from)!=rw_set.set_reads.end() ?
                rw_set.r_entries[from] :
                rw_set.w_entries[from]
            );

            message.debug() << "shared: (through "
              << id2string(w_it->second.object) << ") " << entry.object
              << messaget::eom;
            fenced_edges.writes.push_front(entry.symbol_expr);
          }
          else {
            message.debug() << "shared: "
              << id2string(w_it->second.object) << " -> " 
              << w_it->second.object << messaget::eom;
            fenced_edges.writes.push_front(w_it->second.symbol_expr);
          }
        }
      } catch (std::string s) { 
        message.warning() << "failed to find" << s 
          << messaget::eom; 
        continue; 
      }
    }
    forall_rw_set_r_entries(r_it, rw_set)
    {
      if(has_prefix(id2string(r_it->second.object), CPROVER_PREFIX))
        continue;

      try {
        const symbolt& var=ns.lookup(r_it->second.object);
        message.debug() << "debug: " 
          << id2string(r_it->second.object) << " shared: "
          <<var.is_shared() << " loc: " 
          << r_it->second.symbol_expr.source_location() << messaget::eom;
        if(var.is_shared() && var.type.id()!=ID_code) 
        {
          /* this variable has perhaps been discovered after dereferencing
             a pointer. We want to report this pointer */
          std::map<const irep_idt, const irep_idt>&
            ref=rw_set.dereferenced_from;
          if(ref.find(r_it->second.object)!=ref.end())
          {
            const irep_idt from=ref[r_it->second.object];
            const rw_set_baset::entryt& entry=(
              rw_set.set_reads.find(from)!=rw_set.set_reads.end() ?
              rw_set.r_entries[from] :
              rw_set.w_entries[from]
            );

            message.debug() << "shared: (through "
              << id2string(r_it->second.object) << ") " << entry.object
              << messaget::eom;
            fenced_edges.reads.push_front(entry.symbol_expr);
          }
          else {
            message.debug() << "shared: "
              << id2string(r_it->second.object) << " -> " 
              << r_it->second.object << messaget::eom;
            fenced_edges.reads.push_front(r_it->second.symbol_expr);
          }
        }
      } catch (std::string s) { 
        message.warning() << "failed to find" << s 
          << messaget::eom; 
        continue; 
      }
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_all_shared(
  message_handlert& message_handler,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  messaget message(message_handler);
  fence_all_sharedt instrumenter(message, value_sets, symbol_table, 
    goto_functions);
  instrumenter.do_it();
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_all_shared_aeg(
  message_handlert& message_handler,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  messaget message(message_handler);
  fence_all_shared_aegt instrumenter(message, value_sets, symbol_table, 
    goto_functions);
  instrumenter.do_it();
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_volatile(
  message_handlert& message_handler,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  messaget message(message_handler);
  fence_volatilet instrumenter(message, value_sets, symbol_table, 
    goto_functions);
  instrumenter.do_it();
}
