/*******************************************************************\

Module: XML repair tool

Author: Peter Schrammel

\*******************************************************************/

#include <util/unicode.h>

#include <fstream>
#include <iostream>
#include <stack>
#include <sstream>

#include "xml_repair.h"

// cut non-closed branches at this level
#define BACKTRACK_LEVEL 1

/*******************************************************************\

Function: xml_repair

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_repair(std::ifstream &infile, std::ofstream &outfile)
{
  std::stack<std::string> tags; // tag stack
  bool intag=false;             // within a tag
  bool intagname=false;         // within a tag name
  bool closingtag=false;        // it's a closing tag
  std::stringstream tag;        // the tag name
  std::stringstream backtrackbuffer; // buffer for cutting branches
  char c, lastc=' ';            // current and last character

  while(infile >> std::noskipws >> c)
  {
    backtrackbuffer << c;
    switch(c)
    {
    case '<' : intag=intagname=true; break;
    case ' ' :
      if(intag)
        intagname=false;
      break;
    case '/' :
      if(intag)
      {
        if(lastc=='<')
          closingtag=true;
        else
          intagname=false;
      }
      break;
    case '>' :
      if(!closingtag && lastc!='/') // end of opening tag
      {
        if(lastc!='?')
        {
          tags.push(tag.str());
        }
      }
      else // end of closing tag
      {
        if(lastc!='/')
        {
          tags.pop();
        }
      }
      // clear tag name buffer
      tag.seekp(0);
      tag.seekg(0);
      tag.str("");
      tag.clear();

      if(tags.size()<=BACKTRACK_LEVEL)
      {
        // at this level everything in the buffer is part of the output
        outfile << backtrackbuffer.str();

        // clear buffer
        backtrackbuffer.seekp(0);
        backtrackbuffer.seekg(0);
        backtrackbuffer.str("");
        backtrackbuffer.clear();
      }
      intag=intagname=closingtag=false;
      break;
    default :
      if(intagname)
        tag << c;
      break;
    }
    lastc=c;
  }
  if(tags.size()>0) // truncated
  {
    // everything above BACKTRACK_LEVEL is discarded
    // now, add missing closing tags below it:
    while(!tags.empty())
    {
      if(tags.size()<=BACKTRACK_LEVEL)
      {
        outfile << std::endl << "</" << tags.top() << ">" << std::endl;
      }
      tags.pop();
    }
  }
}
