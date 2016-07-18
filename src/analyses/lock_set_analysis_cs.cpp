/*******************************************************************\

Module: Lock Set Analysis (context-sensitive)

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#include "lock_set_analysis_cs.h"

unsigned may_lock_set_domain_cst::num_lock_case1=0;
unsigned may_lock_set_domain_cst::num_lock_case2=0;

unsigned must_lock_set_domain_cst::num_all_case=0;
unsigned must_lock_set_domain_cst::num_lock_case1=0;
unsigned must_lock_set_domain_cst::num_lock_case2=0;

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::valid_maps() const
{
  // same size
  if (object_map.read().size()!=places_map.size())
    return false;

  // same entries
  for(object_map_dt::const_iterator it=object_map.read().begin();
      it!=object_map.read().end(); it++)
  {
    unsigned n=it->first;
    if(places_map.find(n)==places_map.end())
      return false;
  }

  // maximum one entry with ID_unknown
  for(object_map_dt::const_iterator it=object_map.read().begin();
      it!=object_map.read().end(); it++)
  {
    bool found_unknown=false;
    unsigned n=it->first;
    assert(n<value_sett::object_numbering.size());

    if(value_sett::object_numbering[n].id()==ID_unknown)
    {
      const objectt object=it->second;
      assert(!object.offset_is_set);
      if(found_unknown)
        return false;
      else
        found_unknown=true;
    }
  }

  return true;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::has_top(const object_mapt &object_map) const
{
  for(object_map_dt::const_iterator it=object_map.read().begin();
      it!=object_map.read().end(); it++)
  {
    unsigned n=it->first;
    assert(n<value_sett::object_numbering.size());
    const exprt &expr=value_sett::object_numbering[n];
    if(expr.id()==ID_unknown)
      return true;
  }
  return false;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::has_nonempty_intersection(
  const object_mapt &other) const
{
  assert(!has_top(object_map));
  assert(!has_top(other));

  for(object_map_dt::const_iterator it=object_map.read().begin();
      it!=object_map.read().end(); it++)
  {
    unsigned n=it->first;
    const objectt object=it->second;

    object_map_dt::const_iterator o_it=other.read().find(n);
    if(o_it!=other.read().end())
    {
      const objectt other_object=o_it->second;

      bool b1=object.offset_is_set==other_object.offset_is_set;
      bool b2=object.offset_is_set && object.offset==other_object.offset;
      bool b3=!object.offset_is_set;

      if(b1 && (b2 || b3))
        return true;
    }
  }

  return false;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lock_set_domain_base_cst::get_value_set(
  const ai_cs_stackt &stack,
  locationt l,
  const exprt &arg,
  const namespacet &ns,
  object_mapt &object_map) const // result
{
  assert(object_map.read().empty());

  const value_set_analysis_cst &vsa=*value_set_analysis_cs;
  unsigned stack_number=vsa.get_stack_number(stack);

  ai_cs_baset::placet place(stack, l);
  assert(vsa.has(place));
  const value_sett &value_set=vsa[place].base.value_set;

  value_set.get_value_set(arg, object_map, ns, false, stack_number);
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::merge_places(const places_mapt &other)
{
  bool changed=false;

  // add new places
  for(object_map_dt::const_iterator it=object_map.read().begin();
      it!=object_map.read().end(); it++)
  {
    unsigned n=it->first;
    places_mapt::const_iterator p_it=other.find(n);
    if (p_it!=other.end())
    {
      const placest &places=p_it->second;
      unsigned size=places_map[n].size();
      places_map[n].insert(places.begin(), places.end());
      if(places_map[n].size()>size)
        changed=true;
    }
  }

  // remove old entries
  for(places_mapt::const_iterator it=places_map.begin();
      it!=places_map.end();)
  {
    unsigned n=it->first;
    object_map_dt::const_iterator o_it=object_map.read().find(n);
    if(o_it==object_map.read().end())
    {
      it=places_map.erase(it);
      changed=true;
    }
    else
      it++;
  }

  return changed;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::merge_values(const object_mapt &other)
{
  bool changed=false;

  for(object_map_dt::const_iterator it=other.read().begin();
      it!=other.read().end(); it++)
  {
    unsigned n=it->first;
    const objectt object=it->second;
    object_map_dt::const_iterator entry=object_map.read().find(n);

    if(entry==object_map.read().end())
    {
      // new
      object_map.write()[n]=object;
      changed=true;
    }
    else if(!entry->second.offset_is_set ||
            (object.offset_is_set && entry->second.offset==object.offset))
      ; // no change
    else
    {
      object_map.write()[n].offset_is_set=false;
      changed=true;
    }
  }

  return changed;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::intersect_values(const object_mapt &other)
{
  assert(!has_top(object_map));
  assert(!has_top(other));

  bool changed=false;

  for(object_map_dt::const_iterator it=object_map.read().begin();
      it!=object_map.read().end(); it++)
  {
    unsigned n=it->first;
    const objectt object=it->second;

    object_map_dt::const_iterator entry=other.read().find(n);
    if(entry==other.read().end())
    {
      object_map.write().erase(n);
      changed=true;
      continue;
    }
    const objectt other_object=entry->second;
    if(object.offset_is_set!=other_object.offset_is_set ||
       (object.offset_is_set && object.offset!=other_object.offset))
    {
      object_map.write().erase(n);
      changed=true;
    }
  }

  return changed;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lock_set_domain_base_cst::subtract_values(const object_mapt &other)
{
  assert(!has_top(object_map));

  bool changed=false;

  for(object_map_dt::const_iterator it=other.read().begin();
      it!=other.read().end(); it++)
  {
    unsigned n=it->first;
    const exprt &expr=value_sett::object_numbering[n];
    if(expr.id()==ID_unknown)
    {
      object_map.write().clear();
      changed=true;
      break;
    }
    object_map.write().erase(n);
  }

  return changed;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lock_set_domain_base_cst::output(
  std::ostream &out,
  const ai_cs_baset &ai,
  const namespacet &ns) const
{
  assert(valid_maps());

  // output as value set
  out << "Lockset:\n";
  value_sett::output(ns, out, object_map);
  out << "\n\n";

  // output places
  out << "Places of lockset entries:\n";

  for(places_mapt::const_iterator it=places_map.begin();
      it!=places_map.end(); it++)
  {
    unsigned n=it->first;
    assert(n<value_sett::object_numbering.size());
    const exprt &o=value_sett::object_numbering[n];
    std::string result;
    result=from_expr(ns, "", o);

    out << result << ":\n";

    const placest &places=it->second;
    assert(!places.empty());

    for(placest::const_iterator p_it=places.begin();
        p_it!=places.end(); p_it++)
    {
      const ai_cs_stackt &stack=p_it->first;
      locationt loc=p_it->second;

      out << "Stack: " << stack << "\n";
      out << "Location number: " << loc->location_number << "\n";
    }
  }
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool may_lock_set_domain_cst::merge(
  const lock_set_domain_base_cst &other,
  locationt from,
  locationt to,
  const ai_cs_stackt &stack)
{
  assert(valid_maps());
  assert(other.valid_maps());

  bool new_values;
  new_values=merge_values(other.object_map);

  if(merge_places(other.places_map))
    new_values=true;

  assert(valid_maps());
  return new_values;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void may_lock_set_domain_cst::transform(
  locationt from_l,
  locationt to_l,
  const ai_cs_stackt &stack,
  ai_cs_baset &ai,
  const namespacet &ns)
{
  // clear sets on thread entry and exit
  if((from_l->is_function_call() || from_l->is_end_function()) &&
     from_l->function!=to_l->function)
  {
    ai_cs_stackt::stack_elementt se=stack.frames.back();
    if(std::get<2>(se)==ai_cs_stackt::SE_THREAD_CREATE)
    {
      object_map.write().clear();
      places_map.clear();
      return;
    }
  }

  if(!from_l->is_function_call())
    return;

  const code_function_callt &code = to_code_function_call(from_l->code);
  exprt arg;
  if(code.arguments().size()>=1)
    arg=code.arguments()[0];

  irep_idt id=misc::get_function_name(from_l);
  if(id.empty())
    return;

  std::string name=id2string(id);

  if(name==config.ansi_c.lock_function)
  {
    assert(code.arguments().size()>=1);

    object_mapt lock_objects;
    get_value_set(stack, from_l, arg, ns, lock_objects);
    assert(!lock_objects.read().empty());

    bool b1=false;
    bool b2=false;

    // determine stats
    if(lock_objects.read().size()==1)
    {
      unsigned n=lock_objects.read().begin()->first;
      assert(n<value_sett::object_numbering.size());
      const exprt &expr=value_sett::object_numbering[n];

      if(expr.id()==ID_unknown)
        b1=true;
    }
    else if(object_map.read().size()==1)
    {
      unsigned n=object_map.read().begin()->first;
      assert(n<value_sett::object_numbering.size());
      const exprt &expr=value_sett::object_numbering[n];

      if(expr.id()==ID_unknown)
        b2=true;
    }

    if(b1 || b2)
    {
      num_lock_case2++;
    }
    else
    {
      num_lock_case1++;
    }

    // update lockset
    merge_values(lock_objects);

    // update places
    placest places;
    placet place(stack, from_l);
    places.insert(place);
    places_mapt new_places_map;

    for(object_map_dt::const_iterator it=lock_objects.read().begin();
        it!=lock_objects.read().end(); it++)
    {
      new_places_map[it->first].insert(place);
    }

    merge_places(new_places_map);
  }
  else if(name==config.ansi_c.unlock_function)
  {
    assert(code.arguments().size()>=1);

    object_mapt lock_objects;
    get_value_set(stack, from_l, arg, ns, lock_objects);

    if(lock_objects.read().size()==1)
    {
      unsigned n=lock_objects.read().begin()->first;
      assert(n<value_sett::object_numbering.size());
      const exprt &expr=value_sett::object_numbering[n];

      if(expr.id()!=ID_unknown)
      {
        object_map.write().erase(n);
        places_map.erase(n);
      }
    }
  }
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool must_lock_set_domain_cst::merge(
  const lock_set_domain_base_cst &other,
  locationt from,
  locationt to,
  const ai_cs_stackt &stack)
{
  assert(valid_maps());
  assert(other.valid_maps());

  bool new_values;

  if(all)
  {
    const must_lock_set_domain_cst &o
      =static_cast<const must_lock_set_domain_cst &>(other);
    if(o.all)
      return false;
    all=false;
    // segfauls otherwise, can't see a bug in reference_counting
    object_map.write()=other.object_map.read();
    places_map=other.places_map;
    return true;
  }

  assert(!all);
  const must_lock_set_domain_cst &o
    =static_cast<const must_lock_set_domain_cst &>(other);
  if(o.all)
    return false;

  new_values=intersect_values(other.object_map);

  if(merge_places(other.places_map))
    new_values=true;

  assert(valid_maps());
  return new_values;
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void must_lock_set_domain_cst::transform(
  locationt from_l,
  locationt to_l,
  const ai_cs_stackt &stack,
  ai_cs_baset &ai,
  const namespacet &ns)
{
  // clear sets on thread entry and exit
  if((from_l->is_function_call() || from_l->is_end_function()) &&
     from_l->function!=to_l->function)
  {
    ai_cs_stackt::stack_elementt se=stack.frames.back();
    if(std::get<2>(se)==ai_cs_stackt::SE_THREAD_CREATE)
    {
      object_map.write().clear();
      places_map.clear();
      return;
    }
  }

  if(!from_l->is_function_call())
    return;

  if(all)
  {
    num_all_case++;
    return;
  }

  const code_function_callt &code = to_code_function_call(from_l->code);
  exprt arg;
  if(code.arguments().size()>=1)
    arg=code.arguments()[0];

  irep_idt id=misc::get_function_name(from_l);
  if(id.empty())
    return;

  std::string name=id2string(id);

  if(name==config.ansi_c.lock_function)
  {
    assert(code.arguments().size()>=1);

    object_mapt lock_objects;
    get_value_set(stack, from_l, arg, ns, lock_objects);

    if(lock_objects.read().size()==1)
    {
      unsigned n=lock_objects.read().begin()->first;
      const objectt object=lock_objects.read().begin()->second;
      assert(n<value_sett::object_numbering.size());
      const exprt &expr=value_sett::object_numbering[n];

      if(expr.id()!=ID_unknown)
      {
        num_lock_case1++;

        object_map.write().insert(std::make_pair(n, object));
        placet place(stack, from_l);
        places_map[n].insert(place);
      }
      else
      {
        num_lock_case2++;
      }
    }
    else
    {
      num_lock_case2++;
    }
  }
  else if(name==config.ansi_c.unlock_function)
  {
    assert(code.arguments().size()>=1);

    object_mapt lock_objects;
    get_value_set(stack, from_l, arg, ns, lock_objects);

    subtract_values(lock_objects);

    const places_mapt places_map; // empty
    merge_places(places_map);
  }
}

/*******************************************************************

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_lock_operations(
  const goto_functionst &goto_functions,
  std::vector<exprt> &exprs,
  std::set<goto_programt::const_targett> &lock_locations)
{
  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body_available())
      continue;

    const goto_programt &goto_program=f_it->second.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_function_call())
      {
        irep_idt id=misc::get_function_name(i_it);
        if(id.empty())
	      continue;

        std::string name=id2string(id);
        if(name==config.ansi_c.lock_function ||
           name==config.ansi_c.unlock_function)
        {
          const code_function_callt &code=to_code_function_call(i_it->code);
          const exprt &expr=code.op2();
          exprs.push_back(expr);
          lock_locations.insert(i_it);
        }
      }
    }
  }
}
