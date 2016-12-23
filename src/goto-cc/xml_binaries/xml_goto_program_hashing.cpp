/*******************************************************************\

Module: Convert goto programs to xml structures and back (with irep
        hashing)

Author: CM Wintersteiger

Date: July 2006

\*******************************************************************/

#include <sstream>
#include <iostream>

#include "xml_irep_hashing.h"
#include "xml_goto_program_hashing.h"

/*******************************************************************\

Function: xml_goto_program_convertt::convert

  Inputs: goto program and an xml structure to fill

 Outputs: none

 Purpose: constructs the xml structure according to the goto program
          and the namespace into the given xml object.

\*******************************************************************/

void xml_goto_program_convertt::convert(const goto_programt &goto_program,
                                        xmlt &xml)
{
  std::stringstream tmp;
  // std::cout << "TNO: " << goto_program.target_numbers.size() << std::endl;

  for(const auto &inst : goto_program.instructions)
  {
    xmlt &ins=xml.new_element("instruction");
    if(!inst.location.is_nil())
    {
      irepconverter.reference_convert(inst.location, ins.new_element("location"));
    }

    if(!inst.labels.empty())
    {
      xmlt &lbl = ins.new_element("labels");
      for(goto_programt::instructiont::labelst::const_iterator
          l_it=inst.labels.begin();
          l_it!=inst.labels.end();
          l_it++)
      {
        lbl.new_element("label").set_attribute("name", id2string(*l_it));
      }
    }


    if(inst.target_number!=0)
    {
      // std::cout << "Targetlabel found!" << std::endl;
      tmp.str("");
      tmp << inst.target_number;
      ins.set_attribute("targetlabel",tmp.str());
    }

    switch(inst.type)
    {
    case GOTO:
      {
        ins.name="goto";
        if(!inst.guard.is_true())
        {
          xmlt &g=ins.new_element("guard");
          irepconverter.reference_convert(inst.guard, g);
        }
        xmlt &tgt = ins.new_element("targets");
        for(goto_programt::instructiont::targetst::const_iterator
            gt_it=inst.targets.begin();
            gt_it!=inst.targets.end();
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
        ins.name="assume";
        xmlt &g=ins.new_element("guard");
        irepconverter.reference_convert(inst.guard, g);
        const irep_idt &comment=inst.location.get("comment");
        if(comment!="")
          ins.new_element("comment").data=id2string(comment);
        break;
      }

    case ASSERT:
      {
        ins.name="assert";
        xmlt &g=ins.new_element("guard");
        irepconverter.reference_convert(inst.guard, g);
        const irep_idt &comment=inst.location.get("comment");
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
        ins.name="return";
        xmlt &c=ins.new_element("code");
        irepconverter.reference_convert(inst.code, c);
        break;
      }

    case OTHER:
      {
        ins.name="instruction";
        xmlt &c=ins.new_element("code");
        irepconverter.reference_convert(inst.code, c);
        break;
      }

    case ASSIGN:
      {
        ins.name="assign";
        xmlt &c=ins.new_element("code");
        irepconverter.reference_convert(inst.code, c);
        break;
      }

    case FUNCTION_CALL:
      {
        ins.name="functioncall";
        xmlt &c=ins.new_element("code");
        irepconverter.reference_convert(inst.code, c);
        break;
      }

    case START_THREAD:
      {
        ins.name="thread_start";
        xmlt &tgt=ins.new_element("targets");
        if(inst.targets.size()==1)
        {
          tmp.str("");
          tmp << inst.targets.front()->target_number;
          tgt.new_element("target").data=tmp.str();
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

    if(inst.function!="")
    {
      xmlt &fnc=ins.new_element("function");
      fnc.data=id2string(inst.function);
    }
  }
}

/*******************************************************************\

Function: xml_goto_program_convertt::convert

  Inputs: an xml structure and a goto program to fill

 Outputs: none

 Purpose: constructs the goto program according to the xml structure
          and the namespace into the given goto program object.

\*******************************************************************/
void xml_goto_program_convertt::convert( const xmlt& xml,
              goto_programt& goto_program)
{
  goto_program.clear();
  goto_programt::instructionst &instructions = goto_program.instructions;

  for(const auto &element : xml.elements)
  {
    goto_programt::targett inst = goto_program.add_instruction();
    inst->targets.clear();

    if(element.name=="goto")
    {
      inst->type = GOTO;
    }
    else if(element.name=="assume")
    {
      inst->type = ASSUME;
    }
    else if(element.name=="assert")
    {
      inst->type = ASSERT;
    }
    else if(element.name=="skip")
    {
      inst->type = SKIP;
    }
    else if(element.name=="end_function")
    {
      inst->type = END_FUNCTION;
    }
    else if(element.name=="location")
    {
      inst->type = LOCATION;
    }
    else if(element.name=="dead")
    {
      inst->type = DEAD;
    }
    else if(element.name=="atomic_begin")
    {
      inst->type = ATOMIC_BEGIN;
    }
    else if(element.name=="atomic_end")
    {
      inst->type = ATOMIC_END;
    }
    else if(element.name=="return")
    {
      inst->make_return();
    }
    else if(element.name=="instruction") // OTHER
    {
      inst->make_other();
    }
    else if(element.name=="assign") // OTHER
    {
      inst->make_other();
      inst->type = ASSIGN;
    }
    else if(element.name=="functioncall") // OTHER
    {
      inst->make_other();
      inst->type = FUNCTION_CALL;
    }
    else if(element.name=="thread_start")
    {
      inst->type = START_THREAD;
    }
    else if(element.name=="thread_end")
    {
      inst->type = END_THREAD;
    }
    else
    {
      std::cout << "Unknown instruction type encountered ("
                << element.name << ")";
      std::cout << std::endl;
      return;
    }

    xmlt::elementst::const_iterator eit=element.elements.begin();
    for(const auto &sub : element.elements)
    {
      if(sub.name=="location")
      {
        irepconverter.convert(*eit, inst->location);
        irepconverter.resolve_references(inst->location);
      }
      else if(sub.name=="variables")
      {
      }
      else if(sub.name=="labels")
      {
        xmlt::elementst::const_iterator lit=sub.elements.begin();
        for(; lit != sub.elements.end(); lit++)
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
      else if(sub.name=="guard")
      {
        inst->guard.remove("value");
        irepconverter.convert(*eit, inst->guard);
        irepconverter.resolve_references(inst->guard);
      }
      else if(sub.name=="code")
      {
        irepconverter.convert(*eit, inst->code);
        irepconverter.resolve_references(inst->code);
      }
      else if(sub.name=="targets")
      {
        // Don't do anything here, we'll need a second run for that
      }
      else if(sub.name=="comment")
      {
        inst->location.set("comment", sub.data);
      }
      else if(sub.name=="function")
      {
        inst->function=sub.data;
      }
    }
  }

  // assign line numbers
  goto_program.compute_location_numbers();

  // second run, for targets
  goto_programt::targett ins_it=instructions.begin();
  for(const auto &element : xml.elements)
  {
    if(ins_it==instructions.end())
      break;

    for(const auto &sub : element.elements)
    {
      if(sub.name=="targets")
      {
        for(const auto &t : sub.elements)
        {
          if(t.name=="target")
          {
            goto_programt::targett tins =
              find_instruction(xml, instructions, t.data);
            if(tins!=instructions.end())
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

Function: xml_goto_program_convertt::find_instruction

  Inputs: a target label string, the instructions list and an xml program

 Outputs: iterator to the found instruction or .end()

 Purpose: finds the index of the instruction labelled with the given
          target label in the given xml-program

\*******************************************************************/
goto_programt::targett
xml_goto_program_convertt::find_instruction( const xmlt &xml,
                  goto_programt::instructionst &instructions,
                  const std::string &label)
{
  goto_programt::targett ins_it=instructions.begin();
  for(const auto &element : xml.elements)
  {
    if(ins_it==instructions.end())
      break;

    if(label==element.get_attribute("targetlabel"))
      return ins_it;
    ins_it++;
  }
  return instructions.end();
}
