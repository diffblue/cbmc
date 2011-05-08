/*******************************************************************\
 
Module: Convert goto functions into xml structures and back (with irep
        hashing).
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#ifndef XML_GOTO_FUNCTION_H_
#define XML_GOTO_FUNCTION_H_

#include <xml.h>
#include <goto-programs/goto_functions.h>

#include "xml_irep_hashing.h"

class xml_goto_function_convertt {
  private:
    xml_irep_convertt::ireps_containert &ireps_container;
  public:
    xml_goto_function_convertt(xml_irep_convertt::ireps_containert &ic) : 
      ireps_container(ic) {};
      
  void convert( const xmlt&, goto_functionst::goto_functiont& );
  void convert( const goto_functionst::goto_functiont&, xmlt& );
};

#endif /*XML_GOTO_FUNCTION_H_*/
