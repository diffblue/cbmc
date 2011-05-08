/*******************************************************************\
 
Module: Converts symbols to xml structures and back.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef XML_SYMBOL_H_
#define XML_SYMBOL_H_

#include <symbol.h>
#include <xml.h>

void convert(const symbolt &, xmlt &);
void convert(const xmlt &, symbolt &);

#endif /*XML_SYMBOL_H_*/
