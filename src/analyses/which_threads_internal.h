/*******************************************************************\

Module: Which-Threads Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_WHICH_THREADS_INTERNAL_H
#define CPROVER_ANALYSES_WHICH_THREADS_INTERNAL_H

#include <iostream>
#include <iosfwd>
#include <map>

#include <goto-programs/goto_functions.h>

class which_threads_internalt
{
protected:
  const goto_functionst &goto_functions;

public:
  explicit which_threads_internalt(const goto_functionst&);

  bool is_threaded(const goto_programt::const_targett t) const
  {
    return is_threaded_set.count(t)!=0;
  }

  bool is_shared(const goto_programt::const_targett t) const
  {
    return is_shared_set.count(t)!=0;
  }

  bool is_thread_entry(const irep_idt &name) const
  {
    return thread_categories.find(name) != thread_categories.end();
  }

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  // ********** call and thread-creation graph ************

  struct edget
  {
    bool thread;        // is thread spawn edge
    irep_idt name;      // function name
    unsigned k;         // static occurrences
    bool inside_loop;   // occurrence within loop
    
  edget(bool _thread, 
	irep_idt _name, 
	unsigned _k, 
	bool _inside_loop)
  : thread(_thread),
      name(_name),
      k(_k),
      inside_loop(_inside_loop) {}
  };

  typedef std::pair<irep_idt, irep_idt> caller_calleet;
  typedef std::map<caller_calleet, edget> edgest;
  edgest edges;

  // ********* thread categories ***********

  // a category describes threads running the same function
  struct thread_categoryt
  {
    unsigned depth;
    bool inside_loop;
    unsigned k;

    unsigned nr_instructions;

    typedef std::set<irep_idt> used_functionst;
    used_functionst used_functions;
  };

  typedef std::map<irep_idt, thread_categoryt> thread_categoriest;
  thread_categoriest thread_categories;

  void used_by_thread_categories(const irep_idt &name, 
				 thread_categoriest &_thread_categories)
  {
    for(thread_categoriest::const_iterator it = thread_categories.begin();
	it != thread_categories.end(); ++it)
    {
      if(it->first == name || 
	 it->second.used_functions.find(name) != 
	 it->second.used_functions.end())
      {
	_thread_categories[it->first] = it->second;
      }
    }
  }

  bool are_concurrent(const goto_programt::const_targett t1,
    const goto_programt::const_targett t2)
  {
    thread_categoriest tc1, tc2;
    used_by_thread_categories(t1->function, tc1);
    used_by_thread_categories(t2->function, tc2);
    
    if(tc1.empty() && tc2.empty()) //both are main thread
      return false;
    if(!(tc1.size()==1 && tc2.size()==1)) 
      return true;

    return tc1.begin()->first != tc2.begin()->first || 
      tc1.begin()->second.inside_loop || tc1.begin()->second.k>1;
  }


  // ********* statistics ***********

  // code statistics

  unsigned nr_functions;           // nr of functions
  unsigned nr_shared_functions;    // nr of shared functions
  float ratio_shared_functions;    // ratio of shared functions

  unsigned nr_instructions;        // nr of instructions
  unsigned nr_shared_instructions; // nr of instructions shared between threads
  float ratio_shared_instructions; // ratio of shared instructions

  unsigned min_nr_of_instructions;    // minimum nr of instr. per thread category
  unsigned med_nr_of_instructions;    // median nr of instr. per thread category
  unsigned max_nr_of_instructions;    // maximum nr of instr. per thread category

  unsigned min_depth; // minimum thread creation depth
  unsigned med_depth; // median thread creation depth
  unsigned max_depth; // maximum thread creation depth

  unsigned nr_thread_categories;           // nr thread categories
  unsigned nr_thread_creation_inside_loop; // categories with thread creation inside loop

  // categories = size(c \in thread_categories | c.inside_loop || k>1)


protected:
  typedef std::set<goto_programt::const_targett> target_sett;
  target_sett is_threaded_set;

  // by how many thread categories are functions used?
  typedef std::map<irep_idt, unsigned> use_counterst;
  use_counterst use_counters;

  std::set<irep_idt> shared_functions;
  target_sett is_shared_set;

  std::vector<unsigned> thread_creation_depths;
  std::vector<unsigned> thread_nr_instructions;

  unsigned count_instructions(const irep_idt &name);

  void add(const caller_calleet &cc, const edget &edge);

  void add(const irep_idt &function,
           const goto_programt &body);

  void add_to_target_set(
    const irep_idt &function,
    target_sett &target_set);
};

#endif
