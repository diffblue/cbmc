/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/xml_expr.h>
#include <util/xml.h>

#include <langapi/language_util.h>

#include "value_set_analysis.h"

/*******************************************************************\

Function: value_set_analysist::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysist::convert(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  xmlt &dest) const
{
  source_locationt previous_location;

  forall_goto_program_instructions(i_it, goto_program)
  {
    const source_locationt &location=i_it->source_location;
    
    if(location==previous_location) continue;

    if(location.is_nil() || location.get_file()==irep_idt())
      continue;

    // find value set
    const value_sett &value_set=(*this)[i_it].value_set;

    xmlt &i=dest.new_element("instruction");
    i.new_element()=::xml(location);
    
    for(value_sett::valuest::const_iterator
        v_it=value_set.values.begin();
        v_it!=value_set.values.end();
        v_it++)
    {
      xmlt &var=i.new_element("variable");
      var.new_element("identifier").data=
        id2string(v_it->first);

      const value_sett::object_map_dt 
        &object_map=v_it->second.object_map.read();
      
      for(value_sett::object_map_dt::const_iterator
          o_it=object_map.begin();
          o_it!=object_map.end();
          o_it++)
      {
        const exprt &o=value_sett::object_numbering[o_it->first];
        
        std::string result;

        if(o.id()==ID_invalid || o.id()==ID_unknown)
          result=from_expr(ns, "", o);
        else
        {
          result="<"+from_expr(ns, "", o)+", ";
        
          if(o_it->second.offset_is_set)
          	result+=integer2string(o_it->second.offset)+"";
          else
          	result+='*';

          if(o.type().is_nil())
          	result+=", ?";
          else
          	result+=", "+from_type(ns, "", o.type());

          result+='>';
        }

        std::stringstream ss;
        
        xmlt::escape(result, ss);
        
        var.new_element("value").data=
          ss.str();
      }
    }
  }
}
/*******************************************************************\

Function: value_set_analysist::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysist::convert(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  xmlt &dest)
{
  dest=xmlt("value_set_analysis");

  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    xmlt &f=dest.new_element("function");
    f.new_element("identifier").data=id2string(f_it->first);    
    convert(ns, f_it->second.body, f_it->first, f);
  }
}

/*******************************************************************\

Function: value_set_analysist::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysist::convert(
  const namespacet &ns,
  const goto_programt &goto_program,
  xmlt &dest)
{
  dest=xmlt("value_set_analysis");
  
  convert(
    ns,
    goto_program,
    "",
    dest.new_element("program"));
}


/*******************************************************************\

Function: value_set_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysist::statistics(
    std::ostream &out) const
{
  struct value_set_statisticst
  {
  
   value_set_statisticst ()
   : tracked_lval (0), 
     one_root_offset (0), 
     one_root (0), 
     multiple_root_one_offset (0), 
     unknown (0), 
     invalid (0)
    {
    }
  
    // number of tracked l-values (variables / objects)
    unsigned tracked_lval;
    // number: l-value maps to only one root object with a precise offset
    unsigned one_root_offset;
    // number: l-value maps to only one root object
    unsigned one_root;
    // number: l-value maps to multiple objects with precise offset
    unsigned multiple_root_one_offset;
    // number: l-value maps to unknown
    unsigned unknown;
    // number: l-value maps to invalid  
    unsigned invalid;
  
    void output(std::ostream& out)
    {
      out << " - number of tracked l-values (variables / objects): " 
        << tracked_lval << "\n";

      float den=100 / (float) tracked_lval;

      out << " - root object with a precise offset "
        << one_root_offset * den << " % \n";
      out << " - only one root object " 
        << one_root * den << " % \n";
      out << " - multiple objects with precise offset "
        << multiple_root_one_offset * den << " % \n";
      out << " - unknown value " 
        << unknown * den << " % \n";
      out << " - invalid value " 
        << invalid * den << " % \n";    
    }
  };
  
  value_set_statisticst
    all_statistics,
    array_statistics,
    non_array_statistics;

  for(state_mapt::const_iterator
      it=state_map.begin();
      it!=state_map.end();
      ++it)
  {
  
    const value_set_domaint &dom=it->second;

    for(value_sett::valuest::const_iterator
        v_it=dom.value_set.values.begin();
        v_it!=dom.value_set.values.end();
        v_it++)
    {
      
      irep_idt identifier, display_name;
      
      const value_sett::entryt &e=v_it->second;
    
      if(has_prefix(id2string(e.identifier), "value_set::dynamic_object"))
      {
        display_name=id2string(e.identifier)+id2string(e.suffix);
        identifier="";
      }
      else if(e.identifier=="value_set::return_value")
      {
        display_name="RETURN_VALUE"+id2string(e.suffix);
        identifier="";
      }
      else
      {
        #if 0
        const symbolt &symbol=ns.lookup(e.identifier);
        display_name=symbol.display_name()+id2string(e.suffix);
        identifier=symbol.name;
        #else
        identifier=id2string(e.identifier);
        display_name=id2string(identifier)+id2string(e.suffix);
        #endif
      }
      
      bool have_array=false;
      
      if(id2string(display_name).find("[]")!=std::string::npos)
      {
        have_array=true;
      }
      
      const value_sett::object_map_dt 
        &object_map=e.object_map.read();

      bool have_precise=true;
      bool have_unknown=false;
      bool have_invalid=false;

      for(value_sett::object_map_dt::const_iterator
          o_it=object_map.begin();
          o_it!=object_map.end();
          o_it++)
      {
        const exprt 
          &o=value_sett::object_numbering[o_it->first];

        if(o.id()==ID_invalid)
        {
          have_invalid=true;
        }
        else if(o.id()==ID_unknown)
        {
          have_unknown=true;
        }
        else
        {
          if(!o_it->second.offset_is_set)
          {
          	have_precise=false;
          }
        }
      }

      ++all_statistics.tracked_lval;
    
      ++(have_array ? 
        array_statistics.tracked_lval : 
        non_array_statistics.tracked_lval);

      if(have_precise)
      {
        if(object_map.size()==1)
        {
          if(!have_unknown)
          {
            ++all_statistics.one_root_offset;
            ++all_statistics.one_root;

            ++(have_array ? 
              array_statistics.one_root_offset : 
              non_array_statistics.one_root_offset);
              
            ++(have_array ? 
              array_statistics.one_root : 
              non_array_statistics.one_root);  
          }
        }
        else
        {
          ++all_statistics.multiple_root_one_offset;

          ++(have_array ? 
            array_statistics.multiple_root_one_offset : 
            non_array_statistics.multiple_root_one_offset);  
        }
      }
      else
      {
        if(object_map.size()==1)
        {
          ++all_statistics.one_root;
          
          ++(have_array ? 
            array_statistics.one_root : 
            non_array_statistics.one_root);  
        }
        else
        {
          // nothing
        }    
      }
      
      if(have_unknown)
      {
        ++all_statistics.unknown;
        
        ++(have_array ? 
          array_statistics.unknown : 
          non_array_statistics.unknown);  
      } 
        
      if(have_invalid)
      {
        ++all_statistics.invalid;
      
        ++(have_array ? 
          array_statistics.invalid : 
          non_array_statistics.invalid);  
      }
    }
  }
  
  out << "Statistics \n";
  all_statistics.output(out);
  
  out << "Non-array content \n";
  non_array_statistics.output(out);

  out << "Array content \n";
  array_statistics.output(out);
}
