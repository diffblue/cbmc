/*******************************************************************\

Module: Output repair tool

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>
#include <cassert>

#include "json_repair.h"
#include "xml_repair.h"

/*******************************************************************\

Function: repair

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int repair(const char **argv)
{
  std::string first(argv[1]);
  std::string last(argv[3]);
  bool json=(first=="--json") || (last=="--json");
  bool xml=(first=="--xml") || (last=="--xml");
  bool is_first=(first=="--json") || (first=="--xml");

  std::string infilename(argv[1]);
  std::string outfilename(argv[2]);
  if(is_first)
  {
    infilename=std::string(argv[2]);
    outfilename=std::string(argv[3]);
  }

  std::ifstream infile;
  infile.open(infilename);
  if(!infile.is_open())
  {
    std::cerr << "Cannot open file '" << infilename << "'" << "\n\n";
    return -1;
  }

  std::ofstream outfile;
  outfile.open(outfilename);
  if(!outfile.is_open())
  {
    std::cerr << "Cannot open file '" << outfilename << "'" << "\n\n";
    return -1;
  }

  if(json)
    json_repair(infile, outfile);
  else if(xml)
    xml_repair(infile, outfile);
  else assert(false);

  infile.close();
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
  if(argc!=4)
  {
    std::cerr << "Usage: output-repair.exe "
              << "(--json | --xml) <infile> outfile>\n\n";
    return -1;
  }
  return repair(argv);
}
#else
int main(int argc, const char **argv)
{
  if(argc!=4)
  {
    std::cerr << "Usage: output-repair "
              << "(--json | --xml) <infile> <outfile>\n\n";
    return -1;
  }
  return repair(argv);
}
#endif
