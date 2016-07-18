/*******************************************************************\

Module: Sharing Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com
        Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_SHARING_ANALYSIS_H
#define CPROVER_POINTER_ANALYSIS_SHARING_ANALYSIS_H

#include <goto-programs/goto_functions.h>

#include <analyses/which_threads.h>
#include "value_set_analysis.h"
#include <analyses/lock_set_analysis.h>


class namespacet;

class sharing_analysist
{
public:

  sharing_analysist(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    const value_set_analysist &value_set_analysis,
    const lock_set_analysist &lock_set_analysis);

  // stream output
  void output(std::ostream &out) const;
  
  // XML output
  void convert(xmlt &dest) const;
  
  /* diagnostics */
  enum statust { INCONCLUSIVE, YES, NO} : 2;

  typedef unsigned object_idt; // memory object

  // pair of racy accesses
  struct race_entryt
  {
    statust status;
    statust lock_protection;
    statust same_object;
    
    unsigned access1;  // index into access vector of object
    unsigned access2;  // index into access vector of object
    
    race_entryt(
      statust _status,
      statust _lock_protection,
      statust _same_object,
      unsigned _access1,
      unsigned _access2)
      : status(_status),
        lock_protection(_lock_protection),
        same_object(_same_object),
        access1(_access1),
        access2(_access2)
      { }
  };
  
  // description of an access

  typedef goto_programt::targett targett;
  typedef goto_programt::const_targett const_targett;
  typedef goto_programt::instructiont instructiont;
  

  struct accesst
  {
  	enum typet { READ, WRITE} type;

  	const_targett target;

  	accesst(
  	  typet _type,
  	  const_targett _target)
  	  : type(_type), target(_target) {}
  };


  typedef hash_map_cont<object_idt,
    std::vector<accesst> > access_mapt;

  typedef hash_map_cont<object_idt,
    std::vector<race_entryt> > race_mapt;
 
  access_mapt accesses;
  race_mapt race_map;


protected:

  void visit(
    const_targett t);

  void visit(
    const goto_programt &program);

  // interface value_sets
  const value_sett& get_value_set(
    const_targett l)
  {
    return (value_set_analysis)[l].value_set;
  }

  void update(
      const exprt &expr,
      const const_targett &t,
      accesst::typet);

  const namespacet &ns;
  const value_set_analysist &value_set_analysis;

  const lock_set_analysist &lock_set_analysis;

  which_threadst which_threads;

  void
  reads (const exprt &expr,
         std::set<exprt> &dest);

  void
  add_access(object_idt, const const_targett &t,
             accesst::typet type);

  bool is_shared(const exprt& expr);

};

void show_sharing_analysis(
  ui_message_handlert::uit ui,
  const sharing_analysist &sharing_analysis);

#endif
