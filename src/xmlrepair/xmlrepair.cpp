/*******************************************************************\

Module: XML repair tool

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <stack>
#include <sstream>

//cut non-closed branches at this level
#define BACKTRACK_LEVEL 1

/*******************************************************************\

Function: recover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int repair(const char* infilename, const char* outfilename) {
  std::ifstream infile;
  infile.open(infilename);
  if(!infile.is_open()) {
    std::cerr << "Cannot open file '" << infilename << "'" << 
      std::endl << std::endl;
    return -1;
  }

  std::ofstream outfile;
  outfile.open(outfilename);
  if(!outfile.is_open()) {
    std::cerr << "Cannot open file '" << outfilename << "'" << 
      std::endl << std::endl;
    return -1;
  }

  //do the actual stuff
  std::stack<std::string> tags; // tag stack
  bool intag=false;             // within a tag
  bool intagname=false;         // within a tag name
  bool closingtag=false;        // it's a closing tag
  std::stringstream tag;        // the tag name
  std::stringstream backtrackbuffer; // buffer for cutting branches
  char c, lastc = ' ';          // current and last character

  while (infile >> std::noskipws >> c) {
    backtrackbuffer << c;
    switch(c) {
    case '<' :  intag = intagname = true; break;
    case ' ' :  if(intag) intagname = false; break;
    case '/' :  
      if(intag) {
        if(lastc=='<')  closingtag = true; 
        else intagname = false; 
      }
      break;
    case '>' : 
      if(!closingtag && lastc!='/') { //end of opening tag
        if(lastc!='?') {
        
#if 0
  	  std::cerr << "OPENING: " << tag.str() << std::endl;
#endif 

          tags.push(tag.str());
	}
      }
      else { //end of closing tag
        if(lastc!='/') {

#if 0
   	  std::cerr << "CLOSING: " << tag.str() << std::endl;
#endif

          tags.pop();
	}
      }
      //clear tag name buffer
      tag.seekp(0); tag.seekg(0); tag.str(""); tag.clear();      

#if 0
      std::cerr << "TAGS: " << tags.size() << std::endl;
#endif

      if(tags.size()<=BACKTRACK_LEVEL) { 
        //at this level everything in the buffer is part of the output
        outfile << backtrackbuffer.str();

#if 0
        std::cerr << "CLEAR BUFFER" << std::endl;
#endif

        //clear buffer
        backtrackbuffer.seekp(0); backtrackbuffer.seekg(0); 
        backtrackbuffer.str(""); backtrackbuffer.clear();      
      }
      intag = intagname = closingtag = false;
      break;
    default : 
      if(intagname) tag << c;
      break;
    }
    lastc = c;
  }
  if(tags.size()>0) { //truncated

#if 0
    std::cout << "file truncated. repairing... ";
#endif

    //everything above BACKTRACK_LEVEL is discarded
    //now, add missing closing tags below it:
    while(!tags.empty()) {
      if(tags.size()<=BACKTRACK_LEVEL) { 
        outfile << std::endl << "</" << tags.top() << ">" << std::endl;
      }
      tags.pop();
    }
  }

#if 0
  std::cout << "done." << std::endl;
#endif

  outfile.close();

  return 0;
}

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  if(argc!=3) {
    std::cerr << "Usage: xmlrecover.exe <infile> <outfile>" << 
      std::endl << std::endl;
    return -1;
  }
  return repair(argv[1],argv[2]);
}
#else
int main(int argc, const char **argv)
{
  if(argc!=3) {
    std::cerr << "Usage: xmlrecover <infile> <outfile>" << 
      std::endl << std::endl;
    return -1;
  }
  return repair(argv[1],argv[2]);
}
#endif
