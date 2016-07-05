/*******************************************************************\

Module: JSON repair tool

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_OUTPUT_REPAIR_JSON_REPAIR_H
#define CPROVER_OUTPUT_REPAIR_JSON_REPAIR_H

#include <fstream>

void json_repair(std::ifstream &infile, std::ofstream &outfile);

#endif // CPROVER_OUTPUT_REPAIR_JSON_REPAIR_H
