/*******************************************************************\

Module: Sharing and Race Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com
        Peter Schrammel

\*******************************************************************/

#include <cassert>
#include <ostream>

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/xml_expr.h>
#include <util/xml.h>

#include <langapi/language_util.h>

#include "sharing_analysis.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: sharing_analysist::is_shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool sharing_analysist::is_shared(const exprt& expr)
{
  bool result=false;

  if(expr.id()==ID_unknown)
  {
    // we don't know, so let's be safe
    result = true;
  }
  else if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    const irep_idt &identifier=symbol_expr.get_identifier();

    const std::string id_string(id2string(identifier));

    // exclude internal
    if(has_prefix(id_string, "__CPROVER_thread"))
    {
      return false;
    }

    if(identifier=="")
      return false;

    const symbolt &var=
      ns.lookup(identifier);

    if(var.is_shared())
    {
      return true;
    }
  }
  else
  {
    if(expr.has_operands())
      for(exprt::operandst::const_iterator
          it=expr.operands().begin();
      	  it!=expr.operands().end();
          ++it)
      {
        result = result || is_shared(*it);
      }
  }

  return result;
}


/*******************************************************************\

Function: sharing_analysist::add_access

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void
sharing_analysist::add_access(object_idt object_id,
                              const const_targett &t,
                              accesst::typet type)
{
  exprt o = value_sett::object_numbering[object_id];

  bool shared=is_shared(o);
  bool is_symbol=o.id()==ID_symbol;

#ifdef DEBUG
  std::cout << "   "  
	    << (!t->code.is_nil() ? from_expr(ns, "", t->code) : 
		from_expr(ns, "", t->guard))
	    << " " << from_expr(ns, "", o) << " "
	    << (shared ? "SHARED" : "") << " "
	    << (is_symbol ? "SYMBOL" : "") 
	    << std::endl;
#endif

  if(!shared)
    return;

  if(is_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(o);
    const irep_idt &identifier=symbol_expr.get_identifier();

    const std::string id_string(id2string(identifier));

    // exclude thread id (symmetry argument)
    if(symbol_expr.source_location().get_hide()
       || has_prefix(id2string(identifier), "__CPROVER"))
    {
      return;
    }
  }

  // TODO: not reporting would not be sound

  // we don't report accesses to unknown
  //  if(o.id()==ID_unknown)
  //    return;

  accesst access (type, t);
  accesses[object_id].push_back (access);
}

/*******************************************************************

 Function: sharing_analysist::reads

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
sharing_analysist::reads (const exprt &expr,
                          std::set<exprt> &dest)
{
  //TODO: This does not look sound to me as we might miss 
  //      pointers to intermediate objects in the deref chain

  if(expr.id()==ID_symbol
/*   || expr.id()==ID_member
     || expr.id()==ID_index
     || expr.id()==ID_dereference*/
    )
  {
    dest.insert(expr);
  }

  forall_operands(it, expr)
    reads(*it, dest);
}


/*******************************************************************

 Function: sharing_analysist::update_writes

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
sharing_analysist::update (const exprt &expr, const const_targett &t,
                           accesst::typet type)
{
  value_sett::object_mapt objects;

#ifdef DEBUG
  std::cout << "===" << as_string(ns, *t) << std::endl;
  std::cout << (type==accesst::READ ? "read" : "write")
    << " " << from_expr(ns, "", expr) << std::endl;

#endif

  if(type==accesst::READ)
  {
    std::set<exprt> read_exprs;

    reads(expr, read_exprs);

    for(std::set<exprt>::const_iterator
	      it=read_exprs.begin();
	      it!=read_exprs.end();
	      ++it)
    {
      const exprt &e = *it;

#ifdef DEBUG
      std::cout << "---" << from_expr(ns, "", e) << std::endl;
#endif
      get_value_set (t).get_reference_set (e, objects, ns);

      // traverse the objects and record them
      const value_sett::object_map_dt &objects_dt = objects.read ();

      for (value_sett::object_map_dt::const_iterator a_it = objects_dt.begin ();
          a_it != objects_dt.end (); a_it++)
      {
      	add_access(a_it->first, t, type);
      } // for
    }

  }
  else
  {
    get_value_set (t).get_reference_set (expr, objects, ns);

    // traverse the objects and record them
    const value_sett::object_map_dt &objects_dt = objects.read ();

    for (value_sett::object_map_dt::const_iterator 
         a_it = objects_dt.begin ();
	       a_it != objects_dt.end (); 
	       ++a_it)
    {
      add_access(a_it->first, t, type);
    } // for
  }
}

/*******************************************************************

 Function: sharing_analysist::visit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
sharing_analysist::visit (const_targett t)
{
  const goto_program_instruction_typet &type = t->type;
  const codet &code = t->code;

  if(!which_threads.is_threaded(t))
    return;

  if(code.source_location().get_hide())
    return;

  // find out if shared
  if (type == ASSIGN)
  {
    const code_assignt &code_assign = to_code_assign (code);

    update (code_assign.lhs (), t, accesst::WRITE);
    update (code_assign.rhs (), t, accesst::READ);
  }
  else if (type == GOTO)
  {
    update (t->guard, t, accesst::READ);
  }
  else if (type == ASSUME)
  {
    update (t->guard, t, accesst::READ);
    update (t->guard, t, accesst::WRITE);
  }

}

/*******************************************************************
 Function: sharing_analysist::visit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
sharing_analysist::visit (const goto_programt &program)
{
  forall_goto_program_instructions(it, program){
  	visit(it);
  }
}

/*******************************************************************

 Function: sharing_analysist::sharing_analysist

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

sharing_analysist::sharing_analysist (
  const namespacet &_ns, const goto_functionst &goto_functions,
  const value_set_analysist &_value_set_analysis,
  const lock_set_analysist &_lock_set_analysis) :
  ns (_ns), value_set_analysis (_value_set_analysis),
  lock_set_analysis(_lock_set_analysis),
  which_threads(goto_functions)
{
  typedef goto_functionst::function_mapt function_mapt;

  // compute reads and writes
  for (function_mapt::const_iterator it = goto_functions.function_map.begin ();
       it != goto_functions.function_map.end (); it++)
  {
    if(it->first=="__CPROVER_initialize")
      continue;

    if (it->second.body_available())
    {
      visit (it->second.body);
    }
  }

  // now analyse conflicts
  for(access_mapt::const_iterator 
	it = accesses.begin ();
      it != accesses.end (); 
      ++it)
  {
    const std::vector<accesst> &accesses = it->second;
    const exprt &o = value_sett::object_numbering[it->first];
    
    // let us not report failed symbols
    std::string object_id=from_expr (ns, "", o);
    if(object_id.find("$object")!=std::string::npos)
      continue;

    for(unsigned i=0; i<accesses.size(); ++i)
    {
      const accesst &access1=accesses[i];
      bool w1=access1.type == accesst::WRITE;
      const lock_set_domaint
        &lock_set1=lock_set_analysis[access1.target];

      for(unsigned j=i; j<accesses.size(); ++j)
      {
	const accesst &access2=accesses[j];
	bool w2=access2.type == accesst::WRITE;

#ifdef DEBUG
	std::cout << "object: " << object_id << std::endl;
	std::cout << access1.target->function << " --- " 
		  << access2.target->function << std::endl;
	std::cout << (w1 ? "W" : "R") << " --- " 
		  << (w2 ? "W" : "R") << std::endl;
	std::cout << from_expr(ns,"",(!access1.target->code.is_nil() ? 
				      access1.target->code : 
				      access1.target->guard)) << " --- " 
		  << from_expr(ns,"",(!access2.target->code.is_nil() ? 
				      access2.target->code : 
				      access2.target->guard)) << std::endl;
#endif

        // no race between identical targets unless
        //   instruction can be executed by multiple threads 
        if(access1.target == access2.target &&
	   !which_threads.is_shared(access1.target))
          continue;

        // no race between different targets unless
        //   instruction can be executed by different threads
        if(!which_threads.are_concurrent(access1.target, access2.target))
          continue;
          
	// if either is a write
	if(w1 || w2)
	{
	  const lock_set_domaint
	    &lock_set2=lock_set_analysis[access2.target];

          bool inconclusive=false;

          bool common_lock=
            value_sett::overlap(
              lock_set1.object_map, 
              lock_set2.object_map, 
              inconclusive);

          race_entryt e(
            YES,
            NO,
            YES,
            i,
            j);

          if(!common_lock)
	  {
	    race_map[it->first].push_back(e);
          }
          else if(inconclusive) 
          {    
            e.status=INCONCLUSIVE;
            e.lock_protection=INCONCLUSIVE;
	    race_map[it->first].push_back(e);
	  }
	}
      }
    }
  }
}

/*******************************************************************\

Function: sharing_analysist::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void sharing_analysist::output(std::ostream &out) const
{

  unsigned 
    nr_shared = 0,                  // nr of tracked shared obj
    nr_race_free = 0,               // race-free shared objects
    nr_races = 0,                   // races
    nr_potential_races = 0,         // possible races
    nr_potential_races_lock = 0,    // imprecision due to lock
    nr_potential_races_object = 0;  // imprecision due to object

  for(access_mapt::const_iterator 
      it = accesses.begin ();
      it != accesses.end (); 
      ++it)
  {
    ++nr_shared;
  
    // race-free memory object?
    race_mapt::const_iterator 
      r_it=race_map.find(it->first);
      
    if(r_it==race_map.end())
    {
      ++nr_race_free;
    }
    else
    {
      const std::vector<race_entryt> 
        &race_vec=r_it->second;
        
      for(unsigned i=0; i<race_vec.size(); ++i)
      {
        const race_entryt &e=race_vec[i];
      
        switch(e.status)
        {
          case YES:
            ++nr_races;
            break;
          case INCONCLUSIVE:
            ++nr_potential_races;
            break;
          case NO:
            break;
        }
      
        switch(e.lock_protection)
        {
          case YES:
            break;
          case INCONCLUSIVE:
            ++nr_potential_races_lock;
            break;
          case NO:
            break;
        }
      
        switch(e.same_object)
        {
          case YES:
            break;
          case NO:
            break;
          case INCONCLUSIVE:
            ++nr_potential_races_object;
            break;
        }
      }
    }
  }

  out << "Sharing and Race analysis\n";
  out << "* tracked shared objects " << nr_shared << "\n";
  out << "* race-free objects      " << nr_race_free << "\n";
  out << "* races                  " << nr_races << "\n";
  out << "* potential races        " << nr_potential_races << "\n";
  out << "* potential race (lock?) " << nr_potential_races_lock << "\n";
  out << "* potential race (obj?)  " << nr_potential_races_object << "\n";
}

/*******************************************************************\

Function: sharing_analysist::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void sharing_analysist::convert(xmlt &dest) const
{
  dest=xmlt("sharing-and-race-analysis");

  // traverse access map

  for(access_mapt::const_iterator 
      it = accesses.begin ();
      it != accesses.end (); 
      ++it)
  {
    const std::vector<accesst> &accesses = it->second;

    const exprt &o = value_sett::object_numbering[it->first];

    xmlt &f=dest.new_element("shared-memory-object");

    std::string object_id=from_expr (ns, "", o);

    f.new_element("id").data=object_id;

    // race-free memory object?
    race_mapt::const_iterator 
      r_it=race_map.find(it->first);
      
    if(r_it==race_map.end())
    {
    }
    else
    {
      const std::vector<race_entryt> 
        &race_vec=r_it->second;
        
      for(unsigned i=0; i<race_vec.size(); ++i)
      {
        const race_entryt &e=race_vec[i];
      
        xmlt &r=f.new_element("race");
        r.new_element("status").data=
          e.status==YES ? "YES" : 
          e.status==NO ? "NO" : "INCONCLUSIVE";
        r.new_element("lock-protection").data=
          e.lock_protection == YES ? "YES" :
          e.lock_protection == NO ? "NO" : "INCONCLUSIVE";
        r.new_element("same-object").data=
          e.same_object == YES ? "YES" :
          e.same_object == NO ? "NO" : "INCONCLUSIVE";
        
        const accesst &a1=accesses[e.access1];
        const accesst &a2=accesses[e.access2]; 
        
        const std::string 
          access_type1= (a1.type==accesst::READ) ? "read" : "write";
          
        const std::string 
          access_type2= ( a2.type==accesst::READ) ? "read" : "write";
          
               
        r.new_element(access_type1 + "-access").data=
          (*accesses[e.access1].target).source_location.as_string();
        r.new_element(access_type2 + "-access").data=
          (*accesses[e.access2].target).source_location.as_string();
      }
    }
  }
}

/*******************************************************************\

Function: show_sharing_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_sharing_analysis(
  ui_message_handlert::uit ui,
  const sharing_analysist &sharing_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      sharing_analysis.convert(xml);
      std::cout << xml << std::endl;
    }
    break;
    
  case ui_message_handlert::PLAIN:
    sharing_analysis.output(std::cout);
    break;
      
  default:;
  }
}


