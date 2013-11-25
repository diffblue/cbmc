/*******************************************************************\
 
Module: Convert goto functions into xml structures and back
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef XML_GOTO_FUNCTION_H_
#define XML_GOTO_FUNCTION_H_

#include <util/xml.h>
#include <goto-programs/goto_functions.h>

void convert( const xmlt&, goto_functionst::goto_functiont& );
void convert( const goto_functionst::goto_functiont&, xmlt& );

#endif /*XML_GOTO_FUNCTION_H_*/
