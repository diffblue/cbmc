/*******************************************************************\

Module: Cycle detection

Author: Vincent Nimal

Date: December 2011

\*******************************************************************/


#include "cycle_detection.h"
#include <sstream>
#include <expr.h>
#include <cprover_prefix.h>
#include <prefix.h>
#include <i2string.h>

std::string tostr(const char a){
  std::stringstream ss;
  std::string s;
  ss << a;
  ss >> s;
  return s;
}

std::string color_map[14] = {"red", "blue", "black", "green", "yellow", 
"orange", "blueviolet", "cyan", "cadetblue", "magenta", "palegreen",
"deeppink", "indigo", "olivedrab"};

// integrates the C cycle detector
// an ugly mix of C and C++

/*******************************************************************\

Function: event_grapht()

  Inputs:
 
 Outputs:
 
 Purpose: constructor

\*******************************************************************/

event_grapht::event_grapht()
{
  graph=NULL;
  poList=NULL;
  poUrfeList=NULL;
  //cycleList=NULL;
  char_var='a'-1;
  unique_id=0;
}

/*******************************************************************\
          
Function: ~event_grapht()
          
  Inputs:
        
 Outputs:
 
 Purpose: desstructor
      
\*******************************************************************/

event_grapht::~event_grapht()
{   
  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
    free(*it);
  
  destroyList(graph);
  destroyList(poList);
  destroyList(poUrfeList);
  //destroyList(cycleList);  

  if(file.is_open())
    close_print_cycle();
}

/*******************************************************************\

Function: event_grapht::add_var

  Inputs:
 
 Outputs:
 
 Purpose: converts goto-program var into cycle detector character

\*******************************************************************/

const char event_grapht::add_var(const irep_idt id)
{
  const map_idt::iterator &it=var_to_char.find(id);
  if(it==var_to_char.end())
  {
    char_var++;
    var_to_char.insert(std::pair<irep_idt,char>(id,char_var));
    char_to_var.insert(std::pair<char,irep_idt>(char_var,id));
    return char_var;
  }
  else
    return it->second;
}

/*******************************************************************\

Function: local

  Inputs:
 
 Outputs:
 
 Purpose: is local variable?

\*******************************************************************/

bool inline local(const irep_idt id)
{
  const std::string identifier=id2string(id);
  return (identifier=="c::__CPROVER_alloc" ||
    identifier=="c::__CPROVER_alloc_size" ||
    identifier=="c::stdin" ||
    identifier=="c::stdout" ||
    identifier=="c::stderr" ||
    identifier=="c::sys_nerr" ||
    has_prefix(id2string(identifier), "__unbuffered_") ||
    has_prefix(id2string(identifier), "c::__unbuffered_")
    || has_infix(id2string(identifier), "$tmp_guard"));
}

/*******************************************************************\

Function: event_grapht::dependence_analysis

  Inputs:
 
 Outputs:
 
 Purpose: basic thread-sensitive dependence analysis working with 
          classes. Note that classes are merged only on the basis
          of local variables, not shared ones (to prevent spurious
          dependencies between some disconnected instructions)

\*******************************************************************/

void event_grapht::aliasest::dependence_analysis(
  const aliast read, 
  const aliast write)
{
  std::set<alias_classt>::iterator class_it;
  aliast read_p;
  aliast write_p;

  if(local(read.first))
    read_p=aliast(read.first,0);
  else
    read_p=read;

  if(local(write.first))
    write_p=aliast(write.first,0);
  else
    write_p=write;

  for(class_it=aliases.begin();
    class_it!=aliases.end();
    class_it++)
  {
    if(local(read_p.first) 
      && class_it->find(read_p)!=class_it->end())
    {
      alias_classt new_class(*class_it);
      new_class.insert(write_p);
      //aliases.erase(class_it);
      aliases.insert(new_class);
      //break;
    }

    if(local(write_p.first) 
      && class_it->find(write_p)!=class_it->end())
    {
      alias_classt new_class(*class_it);
      new_class.insert(read_p);
      //aliases.erase(class_it);
      aliases.insert(new_class);
      //break;
    }
  }

  if(class_it==aliases.end())
  {
    alias_classt new_class;
    new_class.insert(read_p);
    new_class.insert(write_p);
    aliases.insert(new_class);
  }
}

/*******************************************************************\

Function: event_grapht::aliasest::dp

  Inputs:

 Outputs: bool

 Purpose:

\*******************************************************************/

bool event_grapht::aliasest::dp(
  const vertex current,
  const vertex next,
  const map_inv_idt char_to_var,
  const map_vid_loct v_id_to_loc)
{
  aliast current_p;
  aliast next_p;

  const irep_idt id_current=char_to_var.find(current->loc)->second;
  const irep_idt id_next=char_to_var.find(next->loc)->second;

  const unsigned loc_current=v_id_to_loc.find(current->id)->second;
  const unsigned loc_next=v_id_to_loc.find(next->id)->second;

  if(local(id_current))
    current_p=aliast(id_current, 0);
  else
    current_p=aliast(id_current, loc_current);

  if(local(id_next))
    next_p=aliast(id_next, 0);
  else
    next_p=aliast(id_next, loc_next);

  for(std::set<alias_classt>::iterator class_it=aliases.begin();
    class_it!=aliases.end();
    class_it++)
    if( class_it->find( current_p ) !=class_it->end()
      && class_it->find( next_p ) !=class_it->end()
      && next->proc == current->proc && current->loc!=next->loc )
      return true;

  return false;
}

/*******************************************************************\

Function: event_grapht::dp_merge

  Inputs:
 
 Outputs:
 
 Purpose: merges classes of equivalence

\*******************************************************************/

void event_grapht::aliasest::dp_merge()
{
  for(std::set<alias_classt>::iterator class_it=aliases.begin();
    class_it!=aliases.end();
    class_it++)
    for(std::set<alias_classt>::iterator class_it2=class_it;
      class_it2!=aliases.end();
      class_it2++)
    {
      for(alias_classt::iterator el_it=class_it->begin();
        el_it!=class_it->end();
        el_it++)
        if(local(el_it->first) && class_it2->find(*el_it)!=class_it2->end())
        {
          alias_classt new_class(*class_it);
          copy_class(new_class, *class_it2);
          aliases.insert(new_class);
          //aliasest::iterator erase_me=class_it++;
          //aliases.erase(erase_me);
          //erase_me=class_it2++;
          //aliases.erase(erase_me);
          //break;
        }

      for(alias_classt::iterator el_it=class_it2->begin();
        el_it!=class_it2->end();
        el_it++)
        if(local(el_it->first) && class_it->find(*el_it)!=class_it->end())
        {
          alias_classt new_class(*class_it);
          copy_class(new_class, *class_it2);
          aliases.insert(new_class);
          //aliasest::iterator erase_me=class_it++;
          //aliases.erase(erase_me);
          //erase_me=class_it2++;
          //aliases.erase(erase_me);
          //break;
        }
    }
}

/*******************************************************************\

Function: event_grapht::aliasest::print

  Inputs:
 
 Outputs:
 
 Purpose: 

\*******************************************************************/

void event_grapht::aliasest::print()
{
  for(std::set<alias_classt>::iterator class_it=aliases.begin();
    class_it!=aliases.end();
    class_it++)
  {
    std::cout<<"CLASS OF EQUIVALENCE"<<std::endl;
    for(alias_classt::iterator it=class_it->begin();
      it!=class_it->end();
      it++)
    std::cout<<"  "<<it->first<<" #"<<it->second<<std::endl;
  }
}

/*******************************************************************\

Function: event_grapht::copy_class

  Inputs:
 
 Outputs:
 
 Purpose: copies the content of a class into another

\*******************************************************************/

void event_grapht::aliasest::copy_class(
  alias_classt& dest, 
  const alias_classt& to_merge)
{
  for(alias_classt::iterator it=to_merge.begin();
    it!=to_merge.end();
    it++)
    dest.insert(*it);
}

/*******************************************************************\

Function: event_grapht::convert_prg

  Inputs:
 
 Outputs:
 
 Purpose: creates a graph of events from a goto-program

\*******************************************************************/

void event_grapht::convert_prg(
  value_setst &value_sets, 
  contextt &context, 
  goto_functionst &goto_functions,
  modelt model)
{
  typedef std::multimap<const char,vertex> id_to_vertext;
  typedef std::pair<const char,vertex> id_vertex_pairt;
  id_to_vertext r_id_to_vertex, w_id_to_vertex;

  namespacet ns(context);

  // previous instruction by po
  vertex previous;

  Forall_goto_functions(f_it, goto_functions)
  {
    aliasest aliases;
    int proc=0;

    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(f_it->first==CPROVER_PREFIX "initialize") 
      {
        previous=NULL;
        continue;
      }

      goto_programt::instructiont &instruction=*i_it;

      proc=instruction.thread;

      if(instruction.is_start_thread() 
        || instruction.is_end_thread()
        || instruction.is_end_function())
        previous=NULL;

      else if(instruction.is_assign()) // a:=b <=> Rb -po-> Wa
      {
        /* -------- READ -------- */
        
        rw_set_loct rw_set(ns, value_sets, i_it);

        // skip assertions
        // SKIP ASSERTIONS DISABLED -- well, it was actually also skipping CF ^^
        // TO FIX: distinguish assume/if/while and assert in add_temporaries
        /*bool skip_this_instruction;
        forall_rw_set_w_entries(w_it, rw_set)
        {
          const irep_idt identifier = w_it->second.object;
          std::cout<<"skippable: "<<w_it->second.object<<std::endl;

          if(has_infix(id2string(identifier),"$tmp_guard"))
          {
            std::cout<<"skipped"<<std::endl;
            skip_this_instruction = true;
            break;
          }
        }
        if(skip_this_instruction)
          continue;*/

        if(instruction.labels.front()=="ASSERT")
          continue;

        forall_rw_set_r_entries(r_it, rw_set)
        {
          // creates Read
          const char read_var=add_var(r_it->second.object);
          std::cout<<"new R"<<tostr(read_var)<<" @thread"
            <<(2<<instruction.thread)<<"("<<r_it->second.object
            <<","<<instruction.location<<")"<<std::endl;
          const vertex new_read=create(
            'R',
            2 << instruction.thread,
            read_var,
            ++unique_id,
            (void*)&(instruction.location)
          );
          graph=createList(new_read,graph);
          v_id_to_loc.insert( 
            std::pair<int,unsigned>(unique_id, instruction.location_number) );

          // creates ... -po-> Read
          if(previous)
          {
            std::cout<<"R"<<tostr(read_var)<<" <-po- "<<tostr(previous->op)
              <<tostr(previous->loc)<<" by pred"<<std::endl;
            linkPo(previous,new_read);
            poList=createList(previous,poList);
            poUrfeList=createList(previous,poUrfeList);
          }

          r_id_to_vertex.insert(id_vertex_pairt(read_var,new_read));

          previous= new_read;

          // creates Read <-cmp-> Write ...
          const std::pair<id_to_vertext::iterator,id_to_vertext::iterator> 
            with_same_var=w_id_to_vertex.equal_range(read_var);
          for(id_to_vertext::iterator id_it=with_same_var.first; 
            id_it!=with_same_var.second; id_it++)
            if(id_it->second->proc!=new_read->proc)
            {
              linkCmp(new_read,id_it->second);
              linkCmp(id_it->second,new_read);
              std::cout<<"R"<<tostr(read_var)<<" <-cmp-> W"<<tostr(id_it->second->loc)<<std::endl;

              poUrfeList=createList(id_it->second,poUrfeList);
            }
        }

        /* -------- WRITE -------- */
        
        forall_rw_set_w_entries(w_it, rw_set)
        {
          const irep_idt identifier = w_it->second.object;

          // skip local variables
          if(identifier=="c::__CPROVER_alloc" ||
            identifier=="c::__CPROVER_alloc_size" ||
            identifier=="c::stdin" ||
            identifier=="c::stdout" ||
            identifier=="c::stderr" ||
            identifier=="c::sys_nerr" ||
            has_prefix(id2string(identifier), "__unbuffered_") ||
            has_prefix(id2string(identifier), "c::__unbuffered_")
            || has_infix(id2string(identifier), "$tmp_guard"))
            continue;

          // creates Write
          const char write_var=add_var(identifier);
          std::cout<<"new W"<<tostr(write_var)<<" @thread"<<(2<<instruction.thread)
            <<"("<<identifier<<","<<instruction.location<<","<<unique_id+1<<")"<<std::endl;
          vertex new_write=create(
            'W',
            2 << instruction.thread,
            write_var,
            ++unique_id,
            (void*)&(instruction.location)
          );
          graph=createList(new_write,graph);
          v_id_to_loc.insert(
            std::pair<int,unsigned>(unique_id, instruction.location_number) );

          // creates Read -po-> Write
          if(previous)
            // from previous reads, or before (e.g., in immediate x:=1)
          {
            std::cout<<"W"<<tostr(write_var)<<" <-po- "
              <<tostr(previous->op)<<tostr(previous->loc)
                <<std::endl;
              linkPo(previous,new_write);
              poList=createList(previous,poList);
              poUrfeList=createList(previous,poUrfeList);
          }

          previous=new_write;

          // creates Write <-cmp-> Read
          const std::pair<id_to_vertext::iterator,id_to_vertext::iterator>
            r_with_same_var=r_id_to_vertex.equal_range(write_var);
          for(id_to_vertext::iterator idr_it=r_with_same_var.first;
            idr_it!=r_with_same_var.second; idr_it++)
            if(idr_it->second->proc!=new_write->proc)
            {
              linkCmp(new_write,idr_it->second);
              linkCmp(idr_it->second,new_write);
              std::cout<<"W"<<tostr(write_var)<<" <-cmp-> R"<<tostr(idr_it->second->loc)<<idr_it->second->id<<std::endl;

              poUrfeList=createList(new_write,poUrfeList);
            }
 
          // creates Write <-cmp-> Write
          const std::pair<id_to_vertext::iterator,id_to_vertext::iterator>
            w_with_same_var=w_id_to_vertex.equal_range(write_var);
          for(id_to_vertext::iterator idw_it=w_with_same_var.first;
            idw_it!=w_with_same_var.second; idw_it++)
            if(idw_it->second->proc!=new_write->proc)
            {
              linkCmp(new_write,idw_it->second);
              linkCmp(idw_it->second,new_write);
              std::cout<<"W"<<tostr(write_var)<<" <-cmp-> W"<<tostr(idw_it->second->loc)<<std::endl;
            }
 
          w_id_to_vertex.insert(id_vertex_pairt(write_var,new_write));
        }

        // dependencies -- alias analysis -- EXPERIMENTAL
        forall_rw_set_w_entries(write_it, rw_set)
          forall_rw_set_r_entries(read_it, rw_set)
          {
            std::cout<<"alias: "<<write_it->second.object<<read_it->second.object<<std::endl;

            const aliast read_p(read_it->second.object, instruction.location_number);
            const aliast write_p(write_it->second.object, instruction.location_number);

            aliases.dependence_analysis(read_p, write_p);
          }
        aliases.dp_merge();
      }
      else if(instruction.is_fence()) 
      {
        const vertex new_fence=create(
          'F',
          2 << instruction.thread,
          0,
          ++unique_id,
          (void*)&(instruction.location)
        );
        graph=createList(new_fence,graph);

        if(previous)
        {
          std::cout<<"Fence <-po- "<<tostr(previous->op)
            <<tostr(previous->loc)<<" by pred"<<std::endl;
          linkPo(previous,new_fence);
          poList=createList(previous,poList);
          poUrfeList=createList(previous,poUrfeList);
        }

        previous=new_fence;
      }
      else if(model!=TSO && instruction.is_lwfence())
      {
        const vertex new_fence=create(
          'f',
          2 << instruction.thread,
          0,
          ++unique_id,
          (void*)&(instruction.location)
        );
        graph=createList(new_fence,graph);
 
        if(previous)
        {
          std::cout<<"Lwfence <-po- "<<tostr(previous->op)
            <<tostr(previous->loc)<<" by pred"<<std::endl;
          linkPo(previous,new_fence);
          poList=createList(previous,poList);
          poUrfeList=createList(previous,poUrfeList);
        }

        previous=new_fence;
      }
    }

    std::pair<int,aliasest> new_aliases(2 << proc, aliases);
    map_aliases.insert(new_aliases);
    aliases.print();

    previous=NULL;//
  }  

  //exit(0);
}  

/*******************************************************************\

Function: event_grapht::collect_cycles_{tso,pso,rmo}

  Inputs:
 
 Outputs:
 
 Purpose: collects the cycles for TSO in the graph of events

\*******************************************************************/

void event_grapht::collect_cycles_tso(bool one_partition)
{
  cycleList=collectCycles(poList,one_partition);
}

void event_grapht::collect_cycles_pso(bool one_partition)
{
  cycleList=collectCycles(poList,one_partition);
}

void event_grapht::collect_cycles_rmo(bool one_partition)
{
  cycleList=collectCycles(poList,one_partition);
}

/*******************************************************************\

Function: event_grapht::collect_cycles_power

  Inputs:
     
 Outputs:
       
Purpose: collects the cycles for Power in the graph of events

\*******************************************************************/

void event_grapht::collect_cycles_power(bool one_partition)
{
  cycleList=collectCycles(poUrfeList,one_partition);
}

/*******************************************************************\

Function: event_grapht::not_local

  Inputs:
    
 Outputs:
      
 Purpose: is this variable a local register?

\*******************************************************************/

bool event_grapht::not_local(const vertex v)
{
  std::map<char,irep_idt>::const_iterator it=char_to_var.find(v->loc);
  if(it==char_to_var.end())
    return false;
  const irep_idt id=it->second;
  //std::cout<<id2string(id)<<std::endl;
  const std::string identifier=id2string(id);
  return !(identifier=="c::__CPROVER_alloc" ||
            identifier=="c::__CPROVER_alloc_size" ||
            identifier=="c::stdin" ||
            identifier=="c::stdout" ||
            identifier=="c::stderr" ||
            identifier=="c::sys_nerr" ||
            has_prefix(id2string(identifier), "__unbuffered_") ||
            has_prefix(id2string(identifier), "c::__unbuffered_")
            || has_infix(id2string(identifier), "$tmp_guard"));
}

/*******************************************************************\

Function: event_grapht::po_order

  Inputs:
    
 Outputs:
      
 Purpose: 1 if a -po-> b, 0 if a <-po- b (or a -?- b)

\*******************************************************************/

bool event_grapht::po_order(
  const vertex a, 
  const vertex b)
{
  if(a->proc != b->proc)
    return false;

  // list in the reverse order
  for(list cur=graph/*poList*/; cur; cur=cur->tl)
    if( ((vertex)cur->hd)->id == a->id )
      return false;
    else if( ((vertex)cur->hd)->id == b->id )
      return true;

  return false;
}

/*******************************************************************\

Function: event_grapht::select_pair

  Inputs:
    
 Outputs:
      
 Purpose:

\*******************************************************************/

inline bool event_grapht::select_pair(
  const vertex current, 
  const list pcycle, 
  std::ofstream &file, 
  modelt model, 
  unsigned cycle_cnt,
  std::set<irep_idt> &instr_set)
{
  bool cycle_instrumented=false;
  bool lwsync_met=false;

  // select the second element of the pair, in the cycle order, without a fence inbetween
  for(list nx=pcycle->tl; 
    ((vertex)nx->hd)->id!=current->id && ((vertex)nx->hd)->op!='F'; 
    nx=nx->tl)
  {
    const vertex next=(vertex)nx->hd;

    if(next->op=='f')
    {
      lwsync_met=true;
      continue;
    }

    bool pot_unsafe=false;
    bool pot_rfe=false; // only for Power -> to instrument the read in the pair

    if(current->proc==next->proc)
    {
      // no dp
      aliasest aliases=map_aliases[current->proc];

      if(aliases.dp(current,next,char_to_var,v_id_to_loc))
      {
        std::cout<<"are in dp: "<<current->op<<"@"<<current->proc<<" and "<<next->op<<"@"<<next->proc<<std::endl;
        continue;
      }
    }

    // TSO: potentially unsafe: poWr\barrier
    // Power: potentially unsafe: po\(dp U barrier) U rfe\(AC U BC)
    if(model==TSO)
      pot_unsafe=
        (current->proc == next->proc && current->op == 'W' && next->op == 'R'
        && not_local(current) && not_local(next) && po_order(current,next) );
    else if(model==PSO)
      pot_unsafe=
        (current->proc == next->proc && current->op == 'W' && next->op != 'F'
        // lwyncWW -> mfenceWW
        && !(current->op=='W' && next->op=='W' && lwsync_met)
        && not_local(current) && not_local(next) && po_order(current,next) );
    else if(model==RMO)
      pot_unsafe=
        (current->proc == next->proc && current->op != 'F' && next->op != 'F'
        && not_local(current) && not_local(next) && po_order(current,next)
        // lwsyncWW -> mfenceWW
        && !(current->op=='W' && next->op=='W' && lwsync_met)
        // lwsyncRW -> mfenceRW
        && !(current->op=='R' && next->op=='W' && lwsync_met)
        // lwsyncRR -> mfenceRR
        && !(current->op=='R' && next->op=='R' && lwsync_met)
        // if posWW, wsi => maintained by the proc
        && !(current->loc == next->loc && current->op == 'W' && next->op == 'W')
        // if posRW, maintained by the proc
        && !(current->loc == next->loc && current->op == 'R' && next->op == 'W')
      );
    else
    {
      if(nx == pcycle->tl) // no transitivity for rfe
      {
        bool AC=false;
        bool BC=false;

        // no fence after the second element? (AC)
        for(list AC_it=nx->tl;
            AC_it && ((vertex)AC_it->hd)->id != next->id && ((vertex)AC_it->hd)->proc == next->proc;
            AC_it=AC_it->tl)
          if(((vertex)AC_it->hd)->op == 'F')
          { 
            AC=true;
            break;
          }

          // no fence before the first element? (BC)
          for(list BC_it=nx->tl; //but could use pcycle as a starter
              BC_it && ( ((vertex)BC_it->hd)->id != current->id );
              BC_it=BC_it->tl)
          if(((vertex)BC_it->hd)->op == 'F' && ((vertex)BC_it->hd)->proc == current->proc)
          {
            BC=true;
            break;
          }

        pot_rfe = (current->proc != next->proc && current->op == 'W' && next->op == 'R' // rfe
          && current->loc == next->loc
          && !AC && !BC // \(AC U BC)
          && not_local(current) && not_local(next) );

        pot_unsafe=
          (current->proc == next->proc && current->op != 'F' && next->op != 'F'
             && not_local(current) && not_local(next) && po_order(current,next) // po\(dp U barrier)
             // lwsyncWW -> mfenceWW
             && !(current->op=='W' && next->op=='W' && lwsync_met)
             // lwsyncRW -> mfenceRW
             && !(current->op=='R' && next->op=='W' && lwsync_met)
             // lwsyncRR -> mfenceRR
             && !(current->op=='R' && next->op=='R' && lwsync_met)
             // if posWW, wsi => maintained by the processor
             && (current->loc != next->loc || current->op != 'W' || next->op != 'W')
          )
          || pot_rfe; // U rfe \(AC U BC)
      }
      else
        pot_unsafe=
          current->proc == next->proc && current->op != 'F' && next->op != 'F' 
             && not_local(current) && not_local(next) && po_order(current,next)  // po\(dp U barrier)
             && !next->dp
             // lwsyncWW -> mfenceWW
             && !(current->op=='W' && next->op=='W' && lwsync_met)
             // lwsyncRW -> mfenceRW
             && !(current->op=='R' && next->op=='W' && lwsync_met)
             // lwsyncRR -> mfenceRR
             && !(current->op=='R' && next->op=='R' && lwsync_met)
             // if posWW, wsi => maintained by the processor
             && (current->loc != next->loc || current->op != 'W' || next->op != 'W');
    }

    printCycle(poList);
    std::cout<<"pair: I check: "<<current->op<<"@"<<current->proc<<" and "<<next->op<<"@"<<next->proc
      <<" "<<pot_unsafe<<not_local(current)<<not_local(next)<<po_order(current,next)<<(current->id<=next->id)
      <<std::endl;

    if(pot_unsafe)
    {
      std::cout<<"pair: po: I mark"<<current->op<<"@"<<current->proc<<" and "<<next->op<<"@"<<next->proc<<std::endl;
      std::cout<<"pair: po: "<<char_to_var[current->loc]<<current->id<<" "<<char_to_var[next->loc]<<
        next->id<<std::endl;

      const irep_idt current_id=char_to_var[current->loc];
      instr_set.insert(current_id);
      const std::pair<irep_idt,locationt>
        p(current_id, *(locationt*)(current->location));

      // for instrumented events
      typedef std::multimap<irep_idt,locationt>::iterator m_itt;
      const std::pair<m_itt,m_itt> ran=id_to_loc.equal_range(current_id);
      m_itt ran_it;
      for(ran_it=ran.first;
        ran_it!=ran.second && ran_it->second!=p.second; ran_it++);

      if(ran_it==ran.second)
        id_to_loc.insert(p);

      const irep_idt next_id=char_to_var[next->loc];
      const std::pair<irep_idt,locationt>
        p_r(next_id, *(locationt*)(next->location));

      // for events in the cycle which can read from the previous event
      const std::pair<m_itt,m_itt> ran_r=id_to_cyc_loc.equal_range(next_id);
      m_itt ran_r_it;
      for(ran_r_it=ran_r.first;
        ran_r_it!=ran_r.second && ran_r_it->second!=p_r.second; ran_r_it++);

      if(ran_r_it==ran_r.second)
        id_to_cyc_loc.insert(p_r);

      // fills the cycle_db for strategies in pairs to instrument
      instr_pairt this_pair=(instr_pairt)malloc(sizeof(struct _instr_pairt));
      assert(this_pair);
      this_pair->scycle=cycle_cnt;
      this_pair->svar=current_id;
      this_pair->svertex=current;

      if(pot_rfe)
      {
        std::cout<<"pair: rfe: I mark"<<current->op<<"@"<<current->proc<<" and "<<next->op<<"@"<<next->proc<<std::endl;

        const irep_idt next_id=char_to_var[next->loc];
        instr_set.insert(next_id);
        const std::pair<irep_idt,locationt>
          p(next_id, *(locationt*)(next->location));

        typedef std::multimap<irep_idt,locationt>::iterator m_itt;
        const std::pair<m_itt,m_itt> ran=id_to_loc.equal_range(next_id);
        m_itt ran_it;
        for(ran_it=ran.first;
          ran_it!=ran.second && ran_it->second!=p.second; ran_it++);

        if(ran_it==ran.second)
          id_to_loc.insert(p);

        // fills the cycle_db for strategies in pairs to instrument
        this_pair->stwo=true;
        this_pair->svar2=next_id;
        this_pair->svertex2=next;
      }
      else
      {
        this_pair->stwo=false;
        //this_pair->svar2=NULL;
        //this_pair->svertex2=NULL;
      }

      cycle_db.insert(this_pair);

      cycle_instrumented=true;
    }
   
  }
  return cycle_instrumented;
}

/*******************************************************************\

Function: {to_circular_list, to_linear_list}

  Inputs:
     
 Outputs:
      
 Purpose: 

\*******************************************************************/

inline void to_circular_list(list l)
{
  assert(l && l->tl);

  list previous=NULL;
  for(list cur=l; cur; cur=cur->tl)
    previous=cur;
  previous->tl=l;
}

inline void to_linear_list(list l)
{
  assert(l && l->tl);

  list cur=NULL;
  for(cur=l->tl; cur && (vertex)cur->tl->hd != (vertex)l->hd; cur=cur->tl);
  cur->tl=NULL;
}

/*******************************************************************\

Function: rewind_first_po

  Inputs:
     
 Outputs:
      
 Purpose: rewinds the circular list to the first event of a po

\*******************************************************************/

inline list rewind_first_po(list l)
{
  assert(l && l->tl);

  vertex previous=(vertex)l->hd;
  list cur;
  for(cur=l->tl; cur 
    && ( ((vertex)l->hd)->id != ((vertex)cur->hd)->id )
    && ( previous->proc==((vertex)cur->hd)->proc ); 
    cur=cur->tl)
  {
    previous=(vertex)cur->hd;
  }

  return cur;
}

/*******************************************************************\

Function: same_cycles_sharing_one

  Inputs: linear lists
     
 Outputs:
      
 Purpose: returns whether the two cycles are identical by the
          variables and events (but not by locations in the code,
          due to unwinding, for instance), and share at least
          one variable+static location

\*******************************************************************/

bool same_cycles_sharing_one (
  const list first, 
  const list second)
{
  if(!first || !first->tl || !second || !second->tl)
    return false;

  vertex shared_vertex=NULL; // variable+static location

  for(list pfirst=first; pfirst && !shared_vertex; pfirst=pfirst->tl)
  {
    for(list psecond=second; psecond; psecond=psecond->tl)
    {
      const vertex firstVertex=(vertex)pfirst->hd;
      const vertex secondVertex=(vertex)psecond->hd;

      if( firstVertex->id == secondVertex->id ) 
      {
        shared_vertex=firstVertex;
        break;
      }
    }
  }

  if(!shared_vertex)
    return false;

  list pfirst=first;
  list psecond=second;

  // at this point, we know what vertex they share
  // we rewind them to this vertex
  to_circular_list(pfirst);
  to_circular_list(psecond);

  for(; ((vertex) pfirst->hd)->id != shared_vertex->id;
    pfirst=pfirst->tl);
  
  for(; ((vertex) psecond->hd)->id != shared_vertex->id;
    psecond=psecond->tl);

  // points to the same place now

  to_linear_list(pfirst);
  to_linear_list(psecond);

  const list start_pfirst=pfirst;
  const list start_psecond=psecond;

  while(pfirst && psecond)
  {
    if( ((vertex)pfirst->hd)->loc!=((vertex)psecond->hd)->loc
        || ((vertex)pfirst->hd)->op!=((vertex)psecond->hd)->op
        || ((vertex)pfirst->hd)->proc!=((vertex)psecond->hd)->proc)
//      || *((locationt*) ((vertex) second->hd)->location) != *((locationt*) shared_vertex->location))
    {
      // rewind second back to its original position
      to_circular_list(start_pfirst);
      to_linear_list(first);
      to_circular_list(start_psecond);
      to_linear_list(second);

      return false;
    }
    printf("colour: %c%c@%c\n %c%c@%d\n",((vertex)first->hd)->op,((vertex)first->hd)->loc,((vertex)first->hd)->proc,((vertex)second->hd)->op,((vertex)second->hd)->loc,((vertex)second->hd)->proc);
    pfirst=pfirst->tl;
    psecond=psecond->tl;
  }

  // rewind second back to its original position
  to_circular_list(start_pfirst);
  to_linear_list(first);
  to_circular_list(start_psecond);
  to_linear_list(second);

  return true;
}

/*******************************************************************\

Function: identical_cycles

  Inputs: linear lists
     
 Outputs:
      
 Purpose: returns whether the two cycles are identical by the id

\*******************************************************************/

bool identical_cycles (
  const list first,
  const list second)
{
  if(!first || !second)
    return false;

  list pfirst=first;
  list psecond=second;

  const vertex shared_vertex=(vertex) pfirst->hd;

  // checks this vertex is shared (for termination of rewinding)
  list psec;
  for(psec=psecond; psec && ((vertex) psec->hd)->id != shared_vertex->id; psec=psec->tl);

  if(!psec)
    return false;

  // at this point, we know that shared_vertex is in second
  // we rewind second to this vertex
  to_circular_list(psecond);

  for(; ((vertex) psecond->hd)->id != shared_vertex->id;
    psecond=psecond->tl);

  // points to the same place now
  to_linear_list(psecond);

  const list start_psecond=psecond;

  printCycle(psecond);

  // checks whether they are identical (i.e., same by id)
  while(pfirst && psecond)
  {
    if( ((vertex)pfirst->hd)->id !=((vertex)psecond->hd)->id )
    {
       // rewind second back to its original position
       to_circular_list(start_psecond);
       to_linear_list(second);
       return false;
    }
    pfirst=pfirst->tl;
    psecond=psecond->tl;
  }

  std::cout<<"cycles"<<std::endl;
  printCycle(start_psecond);

  // rewind second back to its original position
  to_circular_list(start_psecond);
  to_linear_list(second);

  return (!pfirst && !psecond); // both must end here -- to avoid subchain interferences
}

bool exactlyAlreadyFound(list foundStack, list cycle){
  list stack_iter;
  for(stack_iter=foundStack;stack_iter;stack_iter=stack_iter->tl)
    if(identical_cycles((list)stack_iter->hd,cycle))
      return true;
  return false;
}

/*******************************************************************\

Function: schemeAlreadyFound

  Inputs: linear list
     
 Outputs: 0 if not found, 1-14 (colours) if found
      
 Purpose:

\*******************************************************************/

unsigned schemeAlreadyFound(
  std::set<std::pair<list,unsigned> > foundStack, 
  list cycle)
{
  for(std::set<std::pair<list,unsigned> >::iterator it=foundStack.begin(); 
  it!=foundStack.end(); 
  it++)
  {
    const list this_list=it->first;
    if(!this_list || !this_list->tl)
      continue;

    if(same_cycles_sharing_one(this_list, cycle))
    {  std::cout<<"OUT"<<it->second<<std::endl;
      return (it->second);
    }
  }
  return 0;
}

// duplicates the cycle and adds it to foundStack
//
void schemeAddFoundStack(
  std::set<std::pair<list,unsigned> >& foundStack, 
  list cycle, 
  unsigned colour)
{
  list curr=NULL;
  list cycleCopy=NULL;

  for(curr=cycle;curr;curr=curr->tl)
    cycleCopy=createList((vertex)curr->hd,cycleCopy);
  cycleCopy=reverseList(cycleCopy);

  std::pair<list,unsigned> p(cycleCopy,colour);
  foundStack.insert(p);
}

/*******************************************************************\

Function: event_grapht::remove_useless

  Inputs: circular list
     
 Outputs:
      
 Purpose: remove useless vertices

\*******************************************************************/

// TO FIX:
void event_grapht::remove_useless(list cycle)
{
  list previous=NULL;
  bool start=true;
  for(list cur=cycle; start || ((vertex)cur->hd)->id!=((vertex)cycle->hd)->id; cur=cur->tl)
  {
    start=false;
    const vertex this_vertex = (vertex)cur->hd;
    const std::string id = id2string( char_to_var[ this_vertex->loc ] );
    if(previous 
      && ( !not_local(this_vertex)
         // hack 
         || has_prefix(id,"c::P1") || has_prefix(id,"c::P2") 
         || has_prefix(id,"c::__") || has_prefix(id,"c::worker")
         || has_prefix(id,"c::1") || has_prefix(id,"c::owner") 
         || has_prefix(id,"c::thief")) )
      previous->tl=cur->tl;
    else
      previous=cur;
  }
}

/*******************************************************************\

Function: po_reduction

  Inputs:
     
 Outputs:
      
 Purpose: reduces the cycle using po transitions
          Note: need to start from an event first on its po
          (if not, use rewind before)

\*******************************************************************/

void event_grapht::po_reduction(list cycle)
{
  assert(cycle->tl);

  list previous=cycle;
  for(list current=cycle->tl; 
    ((vertex)current->hd)->id!=((vertex)cycle->hd)->id;
    current=current->tl)
  {
    const vertex curr=(vertex)current->hd;
    const vertex prev=(vertex)previous->hd;
    const vertex next=(vertex)current->tl->hd;
 
    aliasest aliases=map_aliases[curr->proc];

    if(curr->op!='F' && curr->op!='f' && curr->proc==prev->proc && next->proc==curr->proc // do not reduce fence
      && !(prev->op=='W' && curr->op=='R' && prev->loc==curr->loc) // do not reduce p -rfi-> c
      && !(curr->op=='W' && next->op=='R' && curr->loc==next->loc) // do not reduce c -rfi-> n
      //&& !(prev->proc==curr->proc 
        //&& aliases.dp(prev,curr,char_to_var,v_id_to_loc)) // do not reduce dp?
      //&& !(curr->proc==next->proc 
        //&& aliases.dp(curr,next,char_to_var,v_id_to_loc)) // do not reduce dp?
    )
      previous->tl=current->tl;
    else
      previous=current;
  }
}

/*******************************************************************\

Function: uniproc

  Inputs: linear list
     
 Outputs:
      
 Purpose: 

\*******************************************************************/

inline bool uniproc(list cycle)
{
  list run;
  for(run=cycle; run && 
    ( ((vertex) run->hd)->op == 'F' || ((vertex) run->hd)->op == 'f' ); 
    run=run->tl);
  if(!run)
    return true; // just to kill this cycle

  const char loc=((vertex)run->hd)->loc;

  list cur;
  for(cur=cycle; 
    cur && ( ((vertex) cur->hd)->loc == loc || ((vertex) cur->hd)->op=='F' || ((vertex) cur->hd)->op=='f'); 
    cur=cur->tl);
  return !cur;
}

/*******************************************************************\

Function: thin-air

  Inputs: circular list
     
 Outputs:
      
 Purpose: 

\*******************************************************************/

inline bool event_grapht::thin_air(list cycle)
{
  assert(cycle && cycle->tl);

  const vertex ref=(vertex) cycle->hd;
  bool start=true;
  list curr;
  for(curr=cycle; 
    (start || ((vertex) curr->hd)->id!=ref->id);
    curr=curr->tl)
  {
    start=false;

    const vertex current = (vertex) curr->hd;
    const vertex next = (vertex) curr->tl->hd;

    if( ((vertex) curr->hd)->op == 'W' && ((vertex) curr->tl->hd)->op == 'R' )
      continue;

    if(current->proc != next->proc)
      return false;

    aliasest aliases=map_aliases[current->proc];

    if(!aliases.dp(current,next,char_to_var,v_id_to_loc))
      return false;
  }

  return true;
}

/*******************************************************************\

Function: have_same_po

  Inputs: linear list
     
 Outputs:
      
 Purpose:

\*******************************************************************/

inline bool have_same_po(list cycle)
{
  const char proc=((vertex)cycle->hd)->proc;
  list cur;
  for(cur=cycle; cur && ((vertex) cur->hd)->proc == proc; cur=cur->tl);
  return !cur;
}

/*******************************************************************\

Function: is_cycle

  Inputs: linear list
     
 Outputs:
      
 Purpose:

\*******************************************************************/

bool event_grapht::is_cycle(list cycle)
{
  const vertex firstVertex= (vertex)cycle->hd;
  list last;
  for(list cur=cycle; cur; cur=cur->tl)
    last=cur;
  const vertex lastVertex = (vertex)last->hd;
  
  if(lastVertex->proc==firstVertex->proc && po_order(lastVertex, firstVertex))
    return true;

  //
  if(lastVertex->op=='W' && firstVertex->op=='R' && lastVertex->loc==firstVertex->loc)
    return true;

  if(lastVertex->op=='W' && firstVertex->op=='W' && lastVertex->loc==firstVertex->loc)
    return true;

  if(lastVertex->op=='R' && firstVertex->op=='W' && lastVertex->loc==firstVertex->loc)
    return true;

/*  for(list curCmp=lastVertex->cmp; curCmp; curCmp=curCmp->tl)
    if( ((vertex)curCmp->hd)->id == firstVertex->id)
      return true;*/

  return false;
}

/*******************************************************************\

Function: is_full_cycle

  Inputs: linear list
     
 Outputs:
      
 Purpose:

\*******************************************************************/

bool is_full_cycle(list cycle)
{
  const vertex firstVertex= (vertex)cycle->hd;
  list last;
  for(list cur=cycle; cur; cur=cur->tl)
    last=cur;
  const vertex lastVertex = (vertex)last->hd;

  if(lastVertex->po && lastVertex->po->id==firstVertex->id)
    return true;

  for(list curCmp=lastVertex->cmp; curCmp; curCmp=curCmp->tl)
    if( ((vertex)curCmp->hd)->id == firstVertex->id)
      return true;

  return false;
}

/*******************************************************************\

Function: event_grapht::to_instrument

  Inputs:
     
 Outputs:
      
 Purpose: returns the set of variables to instrument
          Note that these are just the variables, and not their
          location in the code. To find the locations where
          those variables need to be instrumented, use the map
          id_to_loc

\*******************************************************************/

void event_grapht::to_instrument(const modelt model)
{     
  std::set<irep_idt> instr_set;
  unsigned cycle_cnt=0;

  list cyclesSet=NULL;
  std::set<std::pair<list,unsigned> > schemeCyclesSet;
  unsigned colour_max=1;

  open_print_cycle();

  std::cout<<"#cycles="<<cycleList.size()<<std::endl; 

  for(list l=*(cycleList.begin()); l ; l=l->tl)
  {
     std::cout<<((vertex) l->hd)->proc<<std::endl;
  }
 
  // for each cycle in the stack   
  for(std::set<list>::iterator pstack=cycleList.begin(); pstack!=cycleList.end(); pstack++)
  {
    list this_cycle=(*pstack); // the cycle

    std::cout<<"pick new cycle"<<std::endl;

    printCycle(this_cycle);

    if(!is_full_cycle(this_cycle)) //!is_cycle
    {
      std::cout<<"cycle: not a full cycle"<<std::endl;
      continue;
    }

    to_circular_list(this_cycle);
    remove_useless(this_cycle);
    to_linear_list(this_cycle);

    if(!this_cycle || !this_cycle->tl)
    {
      std::cout<<"cycle: useless"<<std::endl;
      continue;
    }

    printCycle(this_cycle);

    if(!is_cycle(this_cycle))
    {
      std::cout<<"cycle: not a cycle"<<std::endl;
      continue;
    }

    if(have_same_po(this_cycle))
    {
      std::cout<<"cycle: one thread"<<std::endl;
      continue;
    }

    // we are sure there is several po, so we can rewind safely
    to_circular_list(this_cycle);
    this_cycle=rewind_first_po(this_cycle);
    po_reduction(this_cycle);

    // checks thin-air
    if(thin_air(this_cycle))
    {
      std::cout<<"cycle: thin air"<<std::endl;
      continue;
    }

    to_linear_list(this_cycle);

    // checks uniproc
    if(uniproc(this_cycle))
    {
      std::cout<<"cycle: uniproc"<<std::endl;
      continue;
    }

    if(!this_cycle || !this_cycle->tl) // cycles contain at least 3 events
      continue;

    //to_circular_list(this_cycle);
    assert(this_cycle->tl);
    bool start=true;

    printCycleRef(this_cycle);
    printCycle(this_cycle);

    bool cycle_instrumented=false;

   if(!exactlyAlreadyFound(cyclesSet, this_cycle))
   {
    to_circular_list(this_cycle);

    // for each event of the cycle
    for(list pcycle=this_cycle; 
      pcycle && ( start || ((vertex)pcycle->hd)->id != ((vertex)this_cycle->hd)->id ); 
      pcycle=pcycle->tl) 
    {
      start=false;
      const vertex current_event=(vertex)pcycle->hd; // this first event

      // select pairs
      cycle_instrumented|=select_pair(current_event, pcycle, file, model, cycle_cnt, instr_set);

      // no more useful, as po-reduction applied before
      for(;
        ((vertex)pcycle->tl->hd)->proc==current_event->proc &&
        ((vertex)pcycle->tl->tl->hd)->proc==current_event->proc;pcycle=pcycle->tl); // -po-> transitivity
    }

    to_linear_list(this_cycle);

    if(!this_cycle || !this_cycle->tl) // cycles contain at least 3 events
      continue;

    printCycleRef(this_cycle);
    printCycle(this_cycle);

    assert(this_cycle && this_cycle->tl);

    // printing in the file
    if(cycle_instrumented)// && !exactlyAlreadyFound(cyclesSet, this_cycle)) // alreadyFound checks the ids of the vertices, so OK
    {
      std::cout<<"after this"<<std::endl;
      printCycle(this_cycle);
 
      unsigned colour=1;

      cyclesSet=addFoundStack(cyclesSet, this_cycle);
      colour=schemeAlreadyFound(schemeCyclesSet, this_cycle);

      std::cout<<"after this"<<std::endl;
      printCycle(this_cycle);

      if(!colour)
      {
         schemeAddFoundStack(schemeCyclesSet, this_cycle,colour_max);
         colour=colour_max++;
      }

      if(!this_cycle || !this_cycle->tl)
        continue;

      to_circular_list(this_cycle);

      // removes last artefacts
      unsigned size=0;
      const vertex first=(vertex)this_cycle->hd;
      for(list l=this_cycle->tl; l && ((vertex)l->hd)->id!=first->id; l=l->tl)
        size++;
      if(size<3)
        continue;

      print_cycle(this_cycle, cycle_cnt++,colour,model);
    }
    else
      to_circular_list(this_cycle);
    // END    

    to_linear_list(this_cycle);

    printCycleRef(this_cycle);
    printCycle(this_cycle);
  }    
 }

  var_to_instr=instr_set;
}

/*******************************************************************\

Function: event_grapht::to_instrument_{tso,rmo,pso,power}

  Inputs:
        
 Outputs:
               
 Purpose: returns the set of variables to instrument for
          TSO/PSO/RMO/Power. Note that these are just the 
          variables, and not their location in the code. To 
          find the locations where those variables need to 
          be instrumented, use the map id_to_loc

\*******************************************************************/

void event_grapht::to_instrument_tso()
{
  to_instrument(TSO);
}

void event_grapht::to_instrument_pso()
{
  to_instrument(PSO);
}

void event_grapht::to_instrument_rmo()
{
  to_instrument(RMO);
}

void event_grapht::to_instrument_power()
{
  to_instrument(Power);
}

/*******************************************************************\

Function: event_grapht::instrument_...

  Inputs: circular list
        
 Outputs:
               
 Purpose: strategies for pairs to instrument in the cycles

\*******************************************************************/

// How to implement other strategies?
// cycle_db contains those info for each unsafe pair in cycles:
// variable, place in the code, cycle, operation (Read/Write).
// The final variables to instrument are to be placed in the set var_to_instr,
// and their location in the map id_to_loc, relating variables and locations.

void event_grapht::instrument_one_event_per_cycle()
{
  id_to_loc.clear();
  var_to_instr.clear();

  std::set<int> cycles_already_visited;
  
  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
    if( cycles_already_visited.find( (*it)->scycle ) == cycles_already_visited.end() )
    {
      cycles_already_visited.insert( (*it)->scycle );
      var_to_instr.insert( (*it)->svar );

      const vertex this_vertex=(*it)->svertex;
      const std::pair<irep_idt,locationt> p( (*it)->svar, *(locationt*)this_vertex->location );
      id_to_loc.insert(p);

      // marks the instrumented event in the generated graph
      instr_print_cycle(this_vertex);

      // if it is a rfe pair
      if((*it)->stwo)
      {
        var_to_instr.insert( (*it)->svar2 );

        const vertex this_vertex2=(*it)->svertex2;
        const std::pair<irep_idt,locationt> p( (*it)->svar2, *(locationt*)this_vertex2->location );
        id_to_loc.insert(p);

        // marks the instrumented event in the generated graph
        instr_print_cycle(this_vertex2);
      }
    }
}

void event_grapht::instrument_one_read_per_cycle()
{
  id_to_loc.clear();
  var_to_instr.clear();

  std::set<int> cycles_already_instrumented;

  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
    if( cycles_already_instrumented.find( (*it)->scycle ) == cycles_already_instrumented.end() )
      if( (*it)->svertex->op=='R' )
      { 
        cycles_already_instrumented.insert( (*it)->scycle );
        var_to_instr.insert( (*it)->svar );

        const vertex this_vertex=(*it)->svertex;
        const std::pair<irep_idt,locationt> p( (*it)->svar, *(locationt*)this_vertex->location );
        id_to_loc.insert(p);

        // marks the instrumented event in the generated graph
        instr_print_cycle(this_vertex);

        break;
      }
}

void event_grapht::instrument_one_write_per_cycle()
{
  id_to_loc.clear();
  var_to_instr.clear();

  std::set<int> cycles_already_instrumented;

  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
    if( cycles_already_instrumented.find( (*it)->scycle ) == cycles_already_instrumented.end() )
      if( (*it)->svertex->op=='W' )
      {
        cycles_already_instrumented.insert( (*it)->scycle );
        var_to_instr.insert( (*it)->svar );

        const vertex this_vertex=(*it)->svertex;
        const std::pair<irep_idt,locationt> p( (*it)->svar, *(locationt*)this_vertex->location );
        id_to_loc.insert(p);

        // marks the instrumented event in the generated graph
        instr_print_cycle(this_vertex);

        break;
      }
}

// for later: if we prefer to allow only pairs, and not single events...
/*
void event_grapht::instrument_my_events(const std::set<int> to_instrument)
{
  id_to_loc.clear();
  var_to_instr.clear();

  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
    if( to_instrument.find( (*it)->svertex->id ) != to_instrument.end() )
    {
        var_to_instr.insert( (*it)->svar );

        const vertex this_vertex=(*it)->svertex;
        const std::pair<irep_idt,locationt> p( (*it)->svar, *(locationt*)this_vertex->location );
        id_to_loc.insert(p);

        // marks the instrumented event in the generated graph
        instr_print_cycle(this_vertex);

        // if it is a rfe pair
        if((*it)->stwo)
        {
          var_to_instr.insert( (*it)->svar2 );

          const vertex this_vertex2=(*it)->svertex2;
          const std::pair<irep_idt,locationt> p( (*it)->svar2, *(locationt*)this_vertex2->location );
          id_to_loc.insert(p);

          // marks the instrumented event in the generated graph
          instr_print_cycle(this_vertex2);
        }
    }
}*/

// event by event -- if pair, ask both
void event_grapht::instrument_my_events(const std::set<int> to_instrument)
{
  id_to_loc.clear();
  var_to_instr.clear();

  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
  {
    if( to_instrument.find( (*it)->svertex->id ) != to_instrument.end() )
    {
      var_to_instr.insert( (*it)->svar );

      const vertex this_vertex=(*it)->svertex;
      const std::pair<irep_idt,locationt> p( (*it)->svar, *(locationt*)this_vertex->location );
      id_to_loc.insert(p); 
         
      // marks the instrumented event in the generated graph
      instr_print_cycle(this_vertex);
    } 
     
    if((*it)->stwo && to_instrument.find( (*it)->svertex2->id ) != to_instrument.end())
    {    
      var_to_instr.insert( (*it)->svar2 );

      const vertex this_vertex2=(*it)->svertex2;
      const std::pair<irep_idt,locationt> p( (*it)->svar2, *(locationt*)this_vertex2->location );
      id_to_loc.insert(p); 
    
      // marks the instrumented event in the generated graph
      instr_print_cycle(this_vertex2);
    }
  }
}  

void event_grapht::instrument_all()
{
  // by default

  for(pair_dbt::iterator it=cycle_db.begin(); it!=cycle_db.end(); it++)
  {
    // marks the instrumented event in the generated graph
    instr_print_cycle( (*it)->svertex );

    // if it is a rfe pair
    if((*it)->stwo)
      // marks the instrumented event in the generated graph
      instr_print_cycle( (*it)->svertex2 );
  }
}

void event_grapht::instrument_minimum_interference()
{
  // TO DO
}

/*******************************************************************\

Function: order_qualify

  Inputs:
        
 Outputs:
               
 Purpose: returns the name of the order between two events

\*******************************************************************/

std::string event_grapht::order_qualify(
  const vertex prev, 
  const vertex curr, 
  const vertex succ, modelt model)
{
  std::stringstream ss;
  std::string s; 

  // first, we treat the dp
  if(prev->proc==curr->proc && prev->op!='F' && prev->op!='f')
  {
    aliasest& aliases= map_aliases[prev->proc];
    if(aliases.dp(prev,curr,char_to_var,v_id_to_loc))
    {
      ss << "Dp" << tostr(prev->loc==curr->loc?'s':'d') << tostr(curr->op);
      ss >> s;
      return s;
    }
  }

  if(curr->op=='F' && model==Power)
    ss << "Sync" << tostr(prev->op) << tostr(succ->op);

  else if(curr->op=='f' && model==Power)
    ss << "Lwsync" << tostr(prev->op) << tostr(succ->op);

  else if(curr->op=='f')
    ss << "Lwfence" << tostr(prev->op) << tostr(succ->op);

  else if(curr->op=='F')
    ss << "MFenced" << tostr(prev->op) << tostr(succ->op);

  else if(prev->loc==curr->loc
    && prev->op=='W'
    && curr->op=='R')
    ss << "Rf" << tostr( (prev->proc==curr->proc?'i':'e') );

  else if(prev->loc==curr->loc
    && prev->op=='R'
    && curr->op=='W')
    ss << "Fr" << tostr( (prev->proc==curr->proc?'i':'e') );

  else if(prev->loc==curr->loc
    && prev->op=='W'
    && curr->op=='W'
    && prev->proc!=curr->proc) //we prefer to write Po rather than Wsi
    ss << "Ws" << tostr( (prev->proc==curr->proc?'i':'e') );

/*  else if(prev->proc==curr->proc
    && prev->op!='F' && prev->op!='f' && model==Power && aliases.dp(prev,curr,char_to_var,v_id_to_loc))
    ss << "Dp" << tostr(prev->loc==curr->loc?'s':'d') << tostr(curr->op);*/

  else if(prev->proc==curr->proc
    && prev->op!='F'&& prev->op!='f')
    ss << "Po" << tostr(prev->loc==curr->loc?'s':'d') << tostr(prev->op) << tostr(curr->op);

  else 
    ss << " ";

  ss >> s;
  return s;
}

/*******************************************************************\

Function: event_grapht::..._print_cycle

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void event_grapht::open_print_cycle()
{
  output.open("output.txt");
  ref.open("ref.txt");
  file.open("cycles.dot");

  file<<"digraph G {"<<std::endl
   <<"splines=true;"<<std::endl
   <<"overlap=scale;"<<std::endl
   <<"compound=true;"<<std::endl
   <<std::endl;
}

void event_grapht::close_print_cycle()
{
  file << "}";

  file.close();
  output.close();
  ref.close();
}

void event_grapht::instr_print_cycle(
  const vertex current)
{
  file
    << "\" \\\\lb {"
      << current->id << "}"
      << current->op
      << "{" << id2string(char_to_var[current->loc])
      << "} {} @thread " << current->proc
      << "\" [shape=box, color=red];" << std::endl;
}

void event_grapht::print_cycle(
  list cycle, 
  unsigned cycle_cnt,
  unsigned color,
  modelt model)
{
  // file: .dot graph
  // output: instrumented vars, by cycles
  // ref: cycles names

  bool start=true;
  for(list it=cycle; 
      it && ( start || ((vertex)cycle->hd)->id != ((vertex)it->hd)->id ); 
      it=it->tl)
  {
    assert(it && it-> tl && it->tl->tl);

    const vertex previous = (vertex)it->hd;
    const vertex current = (vertex)it->tl->hd;
    const vertex next = (vertex)it->tl->tl->hd;

    std::cout<<  order_qualify(previous,current, next, model) << std::endl;
    ref << order_qualify(previous, current, next, model) << " ";

    file 
      << "\" \\\\lb {"
      << previous->id << "}"
      << previous->op
      << "{" << id2string(char_to_var[previous->loc])
      << "} {} @thread " << previous->proc
      << "\" -> "
      << "\" \\\\lb {"
      << current->id << "}"
      << current->op
      << "{" << id2string(char_to_var[current->loc])
      << "} {} @thread " << current->proc
      << "\" [label=\"" << order_qualify(previous,current, next, model) 
      << "\", color=\"" << color_map[color%14] <<"\"]; " << std::endl;

    output << id2string(char_to_var[current->loc]) << " (" << *((locationt*) current->location) << ") ";

    start=false;
  }

  output << std::endl;
  ref << std::endl;
}

