/*******************************************************************\
 
Module: Convert goto functions into binary format and back (with irep
        hashing).
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#ifndef GOTO_FUNCTION_SERIALIZATION_H_
#define GOTO_FUNCTION_SERIALIZATION_H_

#include <irep_serialization.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program_serialization.h>

class goto_function_serializationt
{
  private:
    irep_serializationt::ireps_containert &ireps_container;
    goto_program_serializationt gpconverter;
    
  public:
    goto_function_serializationt(irep_serializationt::ireps_containert &ic) : 
      ireps_container(ic), gpconverter(ic) {};
      
  void convert(std::istream &, irept &);
  void convert(const goto_functionst::goto_functiont &, std::ostream &);
};

#endif /*GOTO_FUNCTION_SERIALIZATION_H_*/
