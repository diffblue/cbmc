/*******************************************************************\
 
Module: Convert goto programs to binary format and back (with 
        irep hashing)
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#ifndef GOTO_PROGRAM_SERIALIZATION_H_
#define GOTO_PROGRAM_SERIALIZATION_H_

#include <util/irep_serialization.h>

#include <goto-programs/goto_program.h>

class goto_program_serializationt {
  private:
    irep_serializationt irepconverter;
    std::list<irept> irepcache;
    
  public:
    goto_program_serializationt(irep_serializationt::ireps_containert &ic) : 
      irepconverter(ic) { };
        
  void convert(const goto_programt&, std::ostream &);
  void convert(std::istream&, irept&);
  
  goto_programt::targett
  find_instruction( goto_programt&, unsigned );
};

#endif /*GOTO_PROGRAM_SERIALIZATION_H_*/
