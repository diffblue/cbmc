/*******************************************************************\
 
Module: Convert goto programs to xml structures and back.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#include <sstream>
#include <iostream>

#include <xml_irep.h>

#include "xml_goto_program.h"

/*******************************************************************\
 
Function: convert
 
  Inputs: goto program, namespace and an xml structure to fill
 
 Outputs: none
 
 Purpose: constructs the xml structure according to the goto program
          and the namespace into the given xml object.
 
\*******************************************************************/

void convert(const goto_programt &goto_program,
             xmlt &xml)
{
  std::stringstream tmp;
  // std::cout << "TNO: " << goto_program.target_numbers.size() << std::endl;

  const goto_programt::instructionst &instructions =
    goto_program.instructions;
  goto_programt::instructionst::const_iterator ins_it =
    instructions.begin();
  for (;ins_it!=instructions.end();ins_it++)
  {
    xmlt &ins = xml.new_element("instruction");

    if (!ins_it->location.is_nil())
    {
      convert(ins_it->location, ins.new_element("location"));      
    }

    if(!ins_it->labels.empty())
    {
      xmlt &lbl = ins.new_element("labels");
      for(goto_programt::instructiont::labelst::const_iterator
          l_it=ins_it->labels.begin();
          l_it!=ins_it->labels.end();
          l_it++)
      {
        lbl.new_element("label").set_attribute("name", id2string(*l_it));
      }
    }


    if(ins_it->target_number!=0)
    {
      // std::cout << "Targetlabel found!" << std::endl;
      tmp.str("");
      tmp << ins_it->target_number;
      ins.set_attribute("targetlabel",tmp.str());
    }

    switch(ins_it->type)
    {
        case GOTO:
        {
          ins.name = "goto";
          if (!ins_it->guard.is_true())
          {
            xmlt &g = ins.new_element("guard");
            convert(ins_it->guard, g);
          }
          xmlt &tgt = ins.new_element("targets");
          for(goto_programt::instructiont::targetst::const_iterator
              gt_it=ins_it->targets.begin();
              gt_it!=ins_it->targets.end();
              gt_it++)
          {
            tmp.str("");
            tmp << (*gt_it)->target_number;
            tgt.new_element("target").data = tmp.str();
          }
          break;
        }

        case ASSUME:
        {
          ins.name = "assume";
          xmlt &g = ins.new_element("guard");
          convert(ins_it->guard, g);

          const irep_idt &comment=ins_it->location.get("comment");

          if(comment!="")
            ins.new_element("comment").data=id2string(comment);

          break;
        }

        case ASSERT:
        {
          ins.name = "assert";
          xmlt &g = ins.new_element("guard");
          convert(ins_it->guard, g);
          const irep_idt &comment=ins_it->location.get("comment");

          if(comment!="")
            ins.new_element("comment").data=id2string(comment);

          break;
        }

        case SKIP:
        ins.name = "skip";
        break;

        case END_FUNCTION:
        ins.name = "end_function";
        break;

        case LOCATION:
        ins.name = "location";
        break;

        case DEAD:
        ins.name = "dead";
        break;

        case ATOMIC_BEGIN:
        ins.name = "atomic_begin";
        break;

        case ATOMIC_END:
        ins.name = "atomic_end";
        break;

        case RETURN:
        {
          ins.name = "return";
          xmlt &c = ins.new_element("code");
          convert(ins_it->code, c);
          break;
        }
        
        case OTHER:
        {
          ins.name = "instruction";
          xmlt &c = ins.new_element("code");
          convert(ins_it->code, c);
          break;
        }
        
        case ASSIGN: 
        {
          ins.name = "assign";
          xmlt &c = ins.new_element("code");
          convert(ins_it->code, c);
          break;
        }
        
        case FUNCTION_CALL:
        {
          ins.name = "functioncall";
          xmlt &c = ins.new_element("code");
          convert(ins_it->code, c);
          break;
        }

        case START_THREAD:
        {
          ins.name = "thread_start";
          xmlt &tgt = ins.new_element("targets");
          if(ins_it->targets.size()==1)
          {
            tmp.str("");
            tmp << ins_it->targets.front()->target_number;
            tgt.new_element("target").data = tmp.str();
          }
          break;
        }

        case END_THREAD:
        ins.name = "thread_end";
        break;

        default:
        ins.name = "unknown";
        break;
    }
    
    if (ins_it->function!="")
    {
      xmlt &fnc = ins.new_element("function");
      fnc.data = ins_it->function.as_string();       
    }
  }
}

/*******************************************************************\
 
Function: convert
 
  Inputs: an xml structure, namespace, function symbol
          and a goto program to fill
 
 Outputs: none
 
 Purpose: constructs the goto program according to the xml structure
          and the namespace into the given goto program object.
 
\*******************************************************************/
void convert( const xmlt& xml,
              goto_programt& goto_program)
{
  goto_program.clear();
  goto_programt::instructionst &instructions = goto_program.instructions;

  xmlt::elementst::const_iterator it = xml.elements.begin();
  for (; it != xml.elements.end(); it++)
  {
    goto_programt::targett inst = goto_program.add_instruction();
    inst->targets.clear();

    if (it->name=="goto")
    {
      inst->type = GOTO;
    }
    else if (it->name=="assume")
    {
      inst->type = ASSUME;
    }
    else if (it->name=="assert")
    {
      inst->type = ASSERT;
    }
    else if (it->name=="skip")
    {
      inst->type = SKIP;
    }
    else if (it->name=="end_function")
    {
      inst->type = END_FUNCTION;
    }
    else if (it->name=="location")
    {
      inst->type = LOCATION;
    }
    else if (it->name=="dead")
    {
      inst->type = DEAD;
    }
    else if (it->name=="atomic_begin")
    {
      inst->type = ATOMIC_BEGIN;
    }
    else if (it->name=="atomic_end")
    {
      inst->type = ATOMIC_END;
    }
    else if (it->name=="return")
    {
      inst->make_return();
    }
    else if (it->name=="instruction") // OTHER
    {
      inst->make_other();
    }
    else if (it->name=="assign")
    {
      inst->make_other();
      inst->type=ASSIGN;
    }
    else if (it->name=="functioncall")
    {
      inst->make_other();
      inst->type=FUNCTION_CALL;
    }
    else if (it->name=="thread_start")
    {
      inst->type = START_THREAD;
    }
    else if (it->name=="thread_end")
    {
      inst->type = END_THREAD;
    }
    else
    {
      std::cout << "Unknown instruction type encountered (" << it->name << ")";
      std::cout << std::endl;
      return;
    }

    xmlt::elementst::const_iterator eit = it->elements.begin();
    for (; eit != it->elements.end(); eit++)
    {
      if (eit->name=="location")
      {
        convert(*eit, inst->location);
      }
      else if (eit->name=="variables")
      {
      }
      else if (eit->name=="labels")
      {
        xmlt::elementst::const_iterator lit = eit->elements.begin();
        for (; lit != eit->elements.end(); lit++)
        {
          if (lit->name=="label")
          {
            std::string ls = lit->get_attribute("name");
            inst->labels.push_back(ls);
          }
          else
          {
            std::cout << "Unknown node in labels section." << std::endl;
            return;
          }
        }
      }
      else if (eit->name=="guard")
      {
        inst->guard.remove("value");
        convert(*eit, inst->guard);
      }
      else if (eit->name=="code")
      {
        convert(*eit, inst->code);
      }
      else if (eit->name=="targets")
      {
        // Don't do anything here, we'll need a second run for that
      }
      else if (eit->name=="comment")
      {
        inst->location.set("comment", eit->data);
      }
      else if (eit->name=="function")
      {
        inst->function = eit->data;
      }
    }
  }

  // assign line numbers
  goto_program.compute_location_numbers();

  // second run, for targets
  goto_programt::targett ins_it = instructions.begin();
  it = xml.elements.begin();
  for (; it != xml.elements.end() && ins_it!=instructions.end(); it++)
  {
    xmlt::elementst::const_iterator eit = it->elements.begin();
    for (; eit != it->elements.end(); eit++)
    {
      if (eit->name=="targets")
      {
        xmlt::elementst::const_iterator tit = eit->elements.begin();
        for (; tit != eit->elements.end(); tit++)
        {
          if (tit->name=="target")
          {
            goto_programt::targett tins =
              find_instruction(xml, instructions, tit->data);
            if (tins != instructions.end())
            {
              // Here we insert the iterators that somehow seem
              // to be strange afterwards (see line 87)
              ins_it->targets.push_back(tins);
            }
            else
            {
              std::cout << "Warning: instruction not found when "
              "resolving target links." << std::endl;
            }
          }
          else
          {
            std::cout << "Unknown node in targets section." << std::endl;
            return;
          }
        }
      }
    }
    ins_it++;
  }

  // resolve links
  goto_program.update();

  //std::cout << "TNI: " << goto_program.target_numbers.size() << std::endl;
}

/*******************************************************************\
 
Function: find_instruction
 
  Inputs: a target label string, the instructions list and an xml program
 
 Outputs: iterator to the found instruction or .end()
 
 Purpose: finds the index of the instruction labelled with the given 
          target label in the given xml-program
 
\*******************************************************************/

goto_programt::targett
find_instruction(
  const xmlt &xml,
  goto_programt::instructionst &instructions,
  const irep_idt &label)
{
  goto_programt::targett ins_it=instructions.begin();
  xmlt::elementst::const_iterator it=xml.elements.begin();

  for (; it != xml.elements.end() && ins_it!=instructions.end(); it++)
  {
    if (label==it->get_attribute("targetlabel"))
      return ins_it;

    ins_it++;
  }

  return instructions.end();
}

