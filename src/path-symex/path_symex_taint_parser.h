/*******************************************************************
 Module: Taint Parser

 Author: Daniel Neville,	daniel.neville@cs.ox.ac.uk
 John Galea,		john.galea@cs.ox.ac.uk

 \*******************************************************************/

#ifndef PATH_SYMEX_PATH_SYMEX_TAINT_PARSER_H_
#define PATH_SYMEX_PATH_SYMEX_TAINT_PARSER_H_

#include <ostream>
#include <iostream>

#include <util/string2int.h>

#include <json/json_parser.h>
#include <util/message.h>
#include <path-symex/path_symex_taint_data.h>

bool parse_taint_file(const std::string &file_name,
    message_handlert &message_handler, taint_datat &taint_data,
    taint_enginet &taint_engine);

#endif /* PATH_SYMEX_PATH_SYMEX_TAINT_PARSER_H_ */
