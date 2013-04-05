/*******************************************************************\
 
Module: Symbol to binary conversions with irep hashing
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#ifndef SYMBOL_SERIALIZATION_H_
#define SYMBOL_SERIALIZATION_H_

#include <istream>
#include <ostream>
#include <list>

#include "irep_serialization.h"

class symbolt;

class symbol_serializationt {
  private:
    irep_serializationt irepconverter;
    std::list<irept> irepcache;
    
  public:
    symbol_serializationt(irep_serializationt::ireps_containert &ic) : 
      irepconverter(ic) {};
        
  void convert(const symbolt &, std::ostream &);
  void convert(std::istream&, irept&);
};

#endif /*SYMBOL_SERIALIZATION_H_*/
