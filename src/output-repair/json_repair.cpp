/*******************************************************************\

Module: JSON repair tool

Author: Peter Schrammel

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <stack>
#include <sstream>

#include <util/unicode.h>

#include "json_repair.h"

// cut non-closed branches at this level
#define BACKTRACK_LEVEL 2

/*******************************************************************\

Function: json_repair

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void json_repair(std::ifstream &infile, std::ofstream &outfile)
{
  std::stack<bool> elements;         // element stack (object=true)
  bool instring=false;               // within a string
  char c, lastc=' ';                 // current and last character
  std::stringstream backtrackbuffer; // buffer for cutting branches

  while(infile >> std::noskipws >> c)
  {
    backtrackbuffer << c;
    switch(c)
    {
      case '[':
        if(!instring)
          elements.push(false);
        break;
      case '{':
        if(!instring)
          elements.push(true);
        break;
      case '"':
        if(lastc!='\\')
          instring=!instring;
        break;
      case ']':
      case '}':
        if(!instring)
        {
          if(elements.size()<=BACKTRACK_LEVEL)
          {
            // at this level everything in the buffer is part of the output
            outfile << backtrackbuffer.str();
            // clear buffer
            backtrackbuffer.seekp(0);
            backtrackbuffer.seekg(0);
            backtrackbuffer.str("");
            backtrackbuffer.clear();
          }
          elements.pop();
          if(elements.empty()) // cut trailing garbage
            return;
        }
        break;
      default: break;
    }
    lastc=c;
  }

  // everything above BACKTRACK_LEVEL is discarded
  // now, add missing closing elements below it:
  while(!elements.empty())
  {
    if(elements.size()<BACKTRACK_LEVEL)
    {
      outfile << (elements.top() ? "}": "]") << std::endl;
    }
    elements.pop();
  }
}
