/*******************************************************************\
 
Module: XML-symbol conversions with irep hashing
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#ifndef XML_SYMBOL_HASHING_H_
#define XML_SYMBOL_HASHING_H_

#include <util/symbol.h>
#include <util/xml.h>

#include "xml_irep_hashing.h"

class xml_symbol_convertt {
  private:
    xml_irep_convertt irepconverter;
    std::list<irept> irepcache;
    
  public:
    xml_symbol_convertt(xml_irep_convertt::ireps_containert &ic) : 
      irepconverter(ic) {};
        
  void convert(const symbolt &, xmlt &);
  void convert(const xmlt &, symbolt &);
};

#endif /*XML_SYMBOL_HASHING_H_*/
