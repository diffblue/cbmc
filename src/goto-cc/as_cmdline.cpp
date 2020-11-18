/*******************************************************************\

Module: A special command line object for GNU Assembler

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// A special command line object for GNU Assembler

#include "as_cmdline.h"

#include <iostream>

#include <util/prefix.h>

// non-as options
const char *goto_as_options_with_argument[]=
{
  "--verbosity",
  "--function",
  "--native-assembler",
  "--print-rejected-preprocessed-source",
  nullptr
};

const char *as_options_without_argument[]=
{
  "-a", // [-a[cdghlns][=file]]
  "--alternate",
  "-D",
  "--divide", // i386
  "-f",
  "-g",
  "--gstabs",
  "--gstabs+",
  "--gdwarf-2",
  "--help",
  "-J",
  "-K",
  "-L",
  "--keep-locals",
  "-Qy",
  "-R",
  "--reduce-memory-overheads",
  "--statistics",
  "-v",
  "-version",
  "--version",
  "-W",
  "--warn",
  "--fatal-warnings",
  "-w",
  "-x",
  "-Z",
  "--target-help",
  "--32", // i386
  "--64", // i386
  "-n", // i386
  nullptr
};

const char *as_options_with_argument[]=
{
  "--debug-prefix-map",
  "--defsym",
  "-I",
  "--listing-lhs-width",
  "--listing-lhs-width2",
  "--listing-rhs-width",
  "--listing-cont-lines",
  "-o",
  "-march", // i386
  "-mtune", // i386
  nullptr
};

bool as_cmdlinet::parse(int argc, const char **argv)
{
  assert(argc>0);
  add_arg(argv[0]);

  for(int i=1; i<argc; i++)
  {
    std::string argv_i=argv[i];

    // options file?
    if(has_prefix(argv_i, "@"))
    {
      // TODO
      continue;
    }

    // file?
    if(argv_i=="-" || !has_prefix(argv_i, "-"))
    {
      add_infile_arg(argv_i);
      continue;
    }

    bool found=false;

    // separated only, and also allow concatenation with "="
    for(const char **o=goto_as_options_with_argument;
        *o!=nullptr && !found;
        ++o)
    {
      std::string os(*o);

      if(argv_i==os) // separated
      {
        found=true;
        if(i!=argc-1)
        {
          set(argv_i, argv[i+1]);
          ++i;
        }
        else
          set(argv_i, "");
      }
      else if(has_prefix(argv_i, os+"=")) // concatenated with "="
      {
        found=true;
        set(os, argv_i.substr(os.size()+1));
      }
    }

    // goto-as-only command line argument found
    if(found)
      continue;

    // add to new_argv
    add_arg(argv_i);

    // also store in cmdlinet
    if(has_prefix(argv_i, "-a")) // a-options
    {
      // may have an =file argument
      std::size_t equal_pos=argv_i.find('=');

      std::string a_opts="hls";
      if(argv_i.size()>2 &&
         equal_pos!=std::string::npos &&
         equal_pos>2)
        a_opts=argv_i.substr(2, equal_pos-2);
      else if(argv_i.size()>2 &&
              equal_pos==std::string::npos)
        a_opts=argv_i.substr(2);

      for(std::string::const_iterator
          it=a_opts.begin();
          it!=a_opts.end();
          ++it)
      {
        if(equal_pos==std::string::npos)
          set(std::string("-a")+*it); // no value
        else
          set(std::string("-a")+*it, argv_i.substr(equal_pos+1));
      }

      continue;
    }
    // without argument
    else if(in_list(argv_i.c_str(), as_options_without_argument))
    {
      set(argv_i);
      continue;
    }

    for(const char **o=as_options_with_argument;
        *o!=nullptr && !found;
        ++o)
    {
      std::string os(*o);

      if(argv_i==os) // separated
      {
        found=true;
        if(i!=argc-1)
        {
          set(argv_i, argv[i+1]);
          add_arg(argv[i+1]);
          ++i;
        }
        else
          set(argv_i, "");
      }
      else if(has_prefix(argv_i, os+"=")) // concatenated with "="
      {
        found=true;
        set(os, argv_i.substr(os.size()+1));
      }
    }

    if(!found)
    {
      // unrecognized option
      std::cerr << "Warning: uninterpreted as option '" << argv_i
                << "'\n";
    }
  }

  return false;
}
