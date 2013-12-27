/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#if 0
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/prefix.h>

#include <solvers/prop/prop_conv.h>

#include <util/i2string.h>
#include <util/replace_expr.h>
#include <util/find_symbols.h>

#include <langapi/language_util.h>

#include <goto-programs/goto_functions.h>

#include <path-symex/locs.h>
#endif

#include "path_symex_state.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

path_symex_statet initial_state(
  var_mapt &var_map,
  const locst &locs)
{
  path_symex_statet s(var_map, locs);
  
  // create one new thread
  s.add_thread().pc=locs.entry_loc;
  s.set_current_thread(0);

  return s;
}

/*******************************************************************\

Function: path_symex_statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_statet::output(const threadt &thread, std::ostream &out) const
{
  out << "  PC: " << thread.pc << std::endl;
  out << "  Stack:";
  for(call_stackt::const_iterator
      it=thread.call_stack.begin();
      it!=thread.call_stack.end();
      it++)
    out << " " << it->return_location << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: path_symex_statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex_statet::output(std::ostream &out) const
{
  for(unsigned t=0; t<threads.size(); t++)
  {
    out << "*** Thread " << t << std::endl;
    output(threads[t], out);
    out << std::endl;
  }
}

/*******************************************************************\

Function: path_symex_statet::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::read(const exprt &src)
{

  #ifdef DEBUG
  //std::cout << "path_symex_statet::read " << src.pretty() << std::endl;
  #endif

  exprt tmp=instantiate_rec(src, "", src.type(), true, false);
  simplify(tmp, var_map.ns);

  #ifdef DEBUG
  //std::cout << " ==> " << tmp.pretty() << std::endl;
  #endif
  return tmp;
}

/*******************************************************************\

Function: path_symex_statet::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::read_no_propagate(const exprt &src)
{
  #ifdef DEBUG
  std::cout << "path_symex_statet::read_no_propagate " << src.pretty() << std::endl;
  #endif

  exprt tmp=instantiate_rec(src, "", src.type(), false, false);
  simplify(tmp, var_map.ns); // trade-off here, speed-up may not justify this

  #ifdef DEBUG
  std::cout << " ==> " << tmp.pretty() << std::endl;
  #endif

  return tmp;
}
  

/*******************************************************************\

Function: path_symex_statet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt path_symex_statet::instantiate_rec(
  const exprt &src,
  const std::string &suffix,
  const typet& suffix_type,
  bool propagate,
  bool is_address)
{
  if(is_address)
  {
    if(src.id()==ID_symbol)
    {
      return src;
    } 
    else if(src.id()==ID_index)
    {
      assert(src.operands().size()==2);
      exprt tmp=src;
      tmp.op0()=instantiate_rec(src.op0(), suffix, suffix_type, propagate, true);
      tmp.op1()=instantiate_rec(src.op1(), suffix, suffix_type, propagate, false);
      return tmp;
    }
    else if(src.id()==ID_dereference)
    {
      assert(src.operands().size()==1);
      exprt tmp=src;
      tmp.op0()=instantiate_rec(src.op0(), suffix, suffix_type, propagate, false);
      return tmp;
    }
    else {
      if(!src.has_operands())
        return src;

      exprt tmp=src;
  
      Forall_operands(it, tmp)
      {
        exprt tmp2=instantiate_rec(*it, suffix, suffix_type, propagate, true);
        *it=tmp2;
      }

      return tmp;
    }
  } 
  else if(src.id()==ID_address_of)
  {
    return instantiate_rec(src, suffix, suffix_type, propagate, true);
  }
  else if(src.id()==ID_sideeffect)
  {
    #if 0
    const irep_idt &statement=to_side_effect_expr(src).get_statement();
    
    if(statement==ID_nondet)
    {        
      irep_idt id="symex::nondet"+i2string(var_map.nondet_count);

      if(propagate)
        ++var_map.nondet_count;

      return symbol_exprt(id, src.type());
    }
    else
      throw "instantiate_rec: unexpected side effect "+id2string(statement);
    #endif
  }
  else if(src.id()==ID_member)
  {
    #if 0
    const member_exprt &member_expr=to_member_expr(src);
	const irep_idt& component_name=member_expr.get_component_name();
    const exprt &struct_op=member_expr.struct_op();
	typet struct_op_type=var_map.ns.follow(struct_op.type());
	
	if(struct_op_type.id()!=ID_struct)
	{
		return nil_exprt();
	}

    const struct_typet &struct_type=to_struct_type(var_map.ns.follow(struct_op.type()));

	if(!struct_type.has_component(component_name))
	{
		throw "No component " + id2string(component_name) + " in member expr ";
	}

	typet new_suffix_type=suffix.size() ? suffix_type : var_map.ns.follow(struct_type.component_type(component_name));

    // add to suffix
	const std::string new_suffix=
      "."+id2string(component_name)+suffix;

    return instantiate_rec(struct_op, new_suffix, new_suffix_type, propagate, is_address);
    #endif
  }
  else if(src.id()==ID_symbol)
  {
    #if 0

	  // special nondeterminism symbol
	  if(var_map.is_nondet(src)) {
		  return src;
	  }

    const symbol_exprt &symbol_expr=to_symbol_expr(src);
    const irep_idt &identifier=symbol_expr.get_identifier();

    const typet& symbol_type=suffix.size() ? suffix_type : src.type();

	  var_mapt::var_infot& var_info=var_map(identifier, suffix, symbol_type);

		var_path_symex_statet &var_state=get_var_state(var_info);

		// 'src' is symbol.member    
		if(var_state.identifier==irep_idt())
		{
		  // never used before
		  var_state.identifier=var_info.ssa_identifier(get_current_thread());

		  return symbol_exprt(var_state.identifier, symbol_type);
		}
		else if(propagate && var_state.value.is_not_nil())
		{
		  return var_state.value;
		}
		else
		  return symbol_exprt(var_state.identifier, symbol_type);
    #endif
  }

  if(!src.has_operands())
    return src;

  // recursive calls on structure of 'src'
  exprt tmp=src;
  
  Forall_operands(it, tmp)
  {
    exprt tmp2=instantiate_rec(*it, suffix, suffix_type, propagate, false);
    *it=tmp2;
  }
  
  return tmp;
}

/*******************************************************************\

Function: path_symex_statet::original_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
exprt path_symex_statet::original_name(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    const std::string &identifier=id2string(to_symbol_expr(src).get_identifier());
    std::size_t pos=identifier.rfind('#');
    if(pos==std::string::npos) return src;
    std::string new_identifier(identifier, 0, pos);    
    return symbol_exprt(new_identifier, src.type());
  }
  
  if(!src.has_operands()) return src;
  
  exprt tmp=src;
  
  Forall_operands(it, tmp)
  {
    exprt tmp2=original_name(*it);
    *it=tmp2;
  }
  
  return tmp;
}
#endif

/*******************************************************************\

Function: path_symex_statet::ssa_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
exprt path_symex_statet::ssa_name(const exprt &src)
{
  if(src.is_true() || src.is_false())
    return src;

  exprt result(src);

  typedef hash_set_cont<irep_idt, irep_id_hash> symbol_sett;
  symbol_sett depends;

  find_symbols(src,depends);
  
  replace_mapt replace_map;

  assert(ancestor->parent);

  nodet* parent=ancestor->parent;

  bool start_recording=false;

  // replace the symbols in src by the suitable SSA assignments
  for(historyt::reverse_iterator 
      h_rit=history.rbegin();
      h_rit!=history.rend() 
      &&!depends.empty();
      ++h_rit)
  {
    stept& step=*h_rit;

	if(step.node == parent)
		start_recording=true;
    
	if(!start_recording)
		continue;

    if(step.ssa_lhs.is_not_nil())
    {
      exprt original_expr=original_name(step.ssa_lhs);

      symbol_sett::iterator s_it=depends.find(to_symbol_expr(original_expr).get_identifier());
      if(s_it!=depends.end())
      {
        // remove symbol from depends
        depends.erase(s_it);
        
        // replace the expression in src
        replace_map[original_expr]=step.ssa_lhs;
      }
    }
  }

  replace_expr(replace_map, result);

  return result;
}
#endif

/*******************************************************************\

Function: path_symex_statet::ssa_eval

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
exprt path_symex_statet::ssa_eval(const exprt &src, path_symex_statet::historyt::reverse_iterator rit)
{
  if(src.is_true() || src.is_false())
    return src;

  exprt result(src);

  typedef hash_set_cont<irep_idt, irep_id_hash> symbol_sett;
  symbol_sett depends;

  find_symbols(src,depends);
  
  replace_mapt replace_map;

  // replace the symbols in src by the suitable SSA assignments
  for(path_symex_statet::historyt::reverse_iterator 
      h_rit=rit+1;
      h_rit!=history.rend() 
      &&!depends.empty();
      ++h_rit)
  {
    stept& step=*h_rit;
    
    if(step.ssa_lhs.is_not_nil())
    {
      symbol_sett::iterator s_it=depends.find(to_symbol_expr(step.ssa_lhs).get_identifier());

      if(s_it!=depends.end())
      {
        // remove symbol from depends
        depends.erase(s_it);

        // replace the expression in src
        replace_map[step.ssa_lhs]=step.ssa_rhs;
      }
    }
  }

  replace_expr(replace_map, result);

  return result;
}
#endif

/*******************************************************************\

Function: path_symex_statet::record_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
path_symex_statet::stept &path_symex_statet::record_step()
{
  history.push_back(path_symex_stept());
  path_symex_stept &step=history.back();
  step.get_pc_vector(*this);
  step.thread_nr=current_thread;
  return step;
}
#endif

/*******************************************************************\

Function: path_symex_statet::ssa_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void path_symex_statet::ssa_constraints(std::vector<exprt>& constraints, 
                             bool prop) const
{
	bool reached_ancestor=false;

	for(path_symex_statet::historyt::const_iterator
		  h_it=history.begin();
		  h_it!=history.end();
		  h_it++)
	{
		const stept &step=*h_it;
		
		reached_ancestor=reached_ancestor || step.node==ancestor;


		if(!reached_ancestor || step.ignore) continue;


		const exprt& guard = prop ? step.guard : step.guard_no_prop;
		const exprt& lhs   = step.ssa_lhs;
		const exprt& rhs   = prop ? step.ssa_rhs : step.ssa_rhs_no_prop;

		if(guard.is_not_nil() && !guard.is_true())
			constraints.push_back(guard);

		if(lhs.is_not_nil())
		{
	    constraints.push_back(equal_exprt(lhs, rhs.is_nil() ? lhs : rhs));
		}

	}
}
#endif

/*******************************************************************\

Function: path_symex_statet::ssa_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void path_symex_statet::ssa_constraints(prop_conv_solvert &dest, 
                             std::map<exprt,exprt>& activation,
                             bool prop) const
{
  unsigned activation_counter=0;

  bool reached_ancestor=false;

  int i=0; // counter for debugging purposes

  for(path_symex_statet::historyt::const_iterator
      h_it=history.begin();
      h_it!=history.end();
      h_it++)
  {
    const stept &step=*h_it;
    
    reached_ancestor=reached_ancestor||step.node==ancestor;

    if(!reached_ancestor) continue;
    
    if( step.guard.is_not_nil() && !step.guard_no_prop.is_true())
    {
      ++i;
    }

    if(step.lhs.is_not_nil())
      ++i;




    if(step.ignore) continue; 

    const exprt& guard = prop ? step.guard : step.guard_no_prop;
    const exprt& lhs   = step.ssa_lhs;
    const exprt& rhs   = prop ? step.ssa_rhs : step.ssa_rhs_no_prop;



    try {

    if(guard.is_not_nil() &&
       !guard.is_true())
    {
      symbol_exprt av("activation::var"+i2string(activation_counter),bool_typet());
      equal_exprt equality(av, guard);
      activation[guard]=av;

      dest.equality_propagation=false;
      dest.set_to(equality, true);
      dest.equality_propagation=true;

      ++activation_counter;
    }      

    if(step.lhs.is_not_nil())
    {
      dest.set_to(equal_exprt(lhs, rhs.is_nil() ? lhs : rhs), true);
    }

    }

    catch (std::string s)
    {
      throw "path_symex_statet::ssa_constraints: {" + i2string(i) + "} : " + s; 
    }
   
    catch (char const* c)
    {
      throw "path_symex_statet::ssa_constraints: {" + i2string(i) + "} : " + c; 
    }

  }

}
#endif

/*******************************************************************\

Function: path_symex_statet::shared_accesses

  Inputs: expr

 Outputs: shared accesses of most recent instruction 

 Purpose: e.g., usable for backtracking in Dynamic Partial Order Reduction

\*******************************************************************/

#if 0
bool path_symex_statet::shared_accesses(const stept& step,
							 std::set<exprt>& reads, 
					         std::set<exprt>& writes)
{
	if(step.lhs.is_not_nil())
	{
		shared_accesses(step.ssa_lhs,writes,true);
	}

	if(step.ssa_rhs.is_not_nil())
	{
	  shared_accesses(step.ssa_rhs_no_prop,reads,true);
	}

	if(step.guard.is_not_nil())
	{
	  shared_accesses(step.guard_no_prop,reads,true);
	}

	return !reads.empty() || !writes.empty();
}
#endif

#if 0
bool path_symex_statet::last_shared_accesses(std::set<exprt>& reads, 
					         std::set<exprt>& writes)
{
	nodet* parent_node = node->parent;

	if(parent_node==NULL)
		return false;

	for(historyt::const_reverse_iterator 
		it=history.rbegin(); 
		it!=history.rend() && it->node == parent_node; 
	    ++it)
	{
		shared_accesses(*it, reads, writes);
	}

	return !reads.empty() || !writes.empty();
}
#endif

/*******************************************************************\

Function: path_symex_statet::shared_accesses

  Inputs: expr

 Outputs: check if the expression only uses thread-local data,
          if not sure, return no, to be on the safe side

 Purpose:

\*******************************************************************/

#if 0
bool path_symex_statet::shared_accesses(
  const exprt& expr,
  std::set<exprt>& accesses,
  bool record
)
{
  return shared_accesses(expr,std::string(),accesses,record);
}



bool path_symex_statet::shared_accesses(
  const exprt& expr,
  const std::string &suffix,
  std::set<exprt>& accesses,
  bool record)
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    const irep_idt &identifier=symbol_expr.get_identifier();
    var_mapt::var_infot &var_info=
      var_map(identifier, suffix, expr.type());
     
    bool shared = var_info.is_shared();
 
    if(record && shared)
    accesses.insert(expr);

    return shared;
  }
  else if (expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    return shared_accesses(member_expr.struct_op(),suffix,accesses,record);
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);

    //std::cout << "path_symex_statet::shared_accesses " << from_expr(index_expr.array()) << std::endl;

    return shared_accesses(index_expr.array(),suffix,accesses,record);
  }
  else if(expr.id()==ID_dereference)
  {

    try {
      exprt tmp=dereference(expr);
      return shared_accesses(tmp,suffix,accesses,record);
    }

    catch(...)
    {
      // TODO: is this conservative?
      return false;
    }

  }
  else if(expr.has_operands())
  {
    bool result=false;
    forall_operands(it, expr)
      result = shared_accesses(*it,suffix,accesses,record) || result;
    return result;
  }
  else {
    return false;
  }
}
#endif

/*******************************************************************\

Function: path_symex_statet::show_vcc

  Inputs: show verification condition

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void path_symex_statet::show_vcc(
  nodet* ancestor,
  const exprt& start, 
  const exprt& cond,
  bool prop,
  std::ostream &out)
{
  unsigned step_nr=0;
  unsigned count=1;

  bool reached_ancestor=false;

  out << "0:" << from_expr(var_map.ns, "", ssa_name(start,ancestor)) << "\n";
  
  for(path_symex_statet::historyt::const_iterator
      h_it=history.begin();
      h_it!=history.end();
      h_it++, ++step_nr)
  {
    const stept &step=*h_it;
    
    reached_ancestor=reached_ancestor||step.node==ancestor;

    if(!reached_ancestor) continue;
    
    if( step.guard.is_not_nil() && !step.guard_no_prop.is_true())
    {
      out << (count++) << ":" << step_nr << ":"
          << step.node->number 
          << "T"<<step.thread_nr << " "
          << (step.ignore ? "    //":"")
                          << "[" << from_expr(var_map.ns, "", step.guard ) << "]" 
          << (step.guard_no_prop!=step.guard ? 
                "("+from_expr(var_map.ns, "", step.guard_no_prop)+")" 
                : "") 
          << "\n";
    }

    if(step.lhs.is_not_nil())
    {
      std::string constraint;

      if(step.ssa_rhs.is_nil())
        constraint=from_expr(var_map.ns, "", step.ssa_lhs) + " := "+from_expr(var_map.ns, "", step.ssa_lhs);
      else
        constraint=from_expr(step.ssa_lhs) + " := " 
                  + from_expr(var_map.ns, "",step.ssa_rhs) 
                  + ( step.ssa_rhs_no_prop != step.ssa_rhs ? 
                      " ( " + from_expr(var_map.ns, "", step.ssa_rhs_no_prop) + ")" : 
                    " ");

      out << (count++) << ":" << step_nr << ": " << step.node->number 
          << "T" <<step.thread_nr << " " 
          << (step.ignore ? "    //":"") << constraint << "\n";
    }
  }
  
  out << "|--------------------------" << "\n";
  out << "{1} " << from_expr(var_map.ns, "", read(cond)) 
      << " ( " << from_expr(var_map.ns, "", read_no_propagate(cond)) << " ) " << "\n";
}
#endif
