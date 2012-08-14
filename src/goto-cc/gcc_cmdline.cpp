/*******************************************************************\

Module: A special command line object for the gcc-like options

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <cassert>
#include <cstring>
#include <iostream>

#include <prefix.h>

#include "gcc_cmdline.h"

/*******************************************************************\
 
Function: gcc_cmdlinet::parse
 
  Inputs: argument count, argument strings
 
 Outputs: none
 
 Purpose: parses the commandline options into a cmdlinet

\*******************************************************************/

// separated or concatenated
const char *gcc_options_with_argument[]=
{
  "-o",
  "-x",
  "-B",
  "-iquote",
  "-idirafter",
  "-include",
  "-I",
  "-V",
  "-D",
  "-L",
  "-MT",
  "-MQ",
  "-MF",
  "-u", // goes to linker
  "-T", // goes to linker
  NULL
};

const char *gcc_options_with_separated_argument[]=
{
  "--verbosity", // non-gcc
  "--function",  // non-gcc
  "-aux-info",
  "--param",
  "-imacros",
  "-iprefix",
  "-iwithprefix",
  "-iwithprefixbefore",
  "-isystem",
  "-isysroot",
  "-Xpreprocessor",
  "-Xassembler",
  "-Xlinker",
  "-b",
  "-std",
  "-print-file-name",
  "-print-prog-name",
  "-specs",
  "--sysroot",
  NULL
};

const char *gcc_options_with_concatenated_argument[]=
{
  "-d",
  "-g",
  "-A",
  "-U",
  "-l",
  NULL
};

const char *gcc_options_without_argument[]=
{
  "--dot", // NON-GCC
  "--show-symbol-table", // NON-GCC
  "--show-function-table", // NON-GCC
  "--ppc-macos", // NON-GCC
  "--i386-linux", // NON-GCC
  "--i386-win32", // NON-GCC
  "--i386-macos", // NON-GCC
  "--winx64", // NON_GCC
  "--string-abstraction", // NON-GCC
  "--no-library", // NON-GCC
  "--16", // NON-GCC
  "--32", // NON-GCC
  "--64", // NON-GCC
  "--little-endian", // NON-GCC
  "--big-endian", // NON-GCC
  "--no-arch", // NON-GCC            
  "--partial-inlining", // NON-GCC
  "-h", 
  "--help", // NON-GCC
  "-?", // NON-GCC
  "-r", // for ld mimicking
  "-c", 
  "-S",
  "-E", 
  "-combine",
  "-pipe", 
  "-pass-exit-codes",
  "-v", 
  "-###",
  "-help", 
  "-target-help",
  "--version", 
  "-ansi",
  "-trigraphs",
  "-no-integrated-cpp",
  "-traditional",
  "-traditional-cpp",
  "-nostdinc++", 
  "-gen-decls",
  "-pedantic",
  "-pedantic-errors",
  "-w", 
  "-dumpspecs",
  "-dumpmachine",
  "-dumpversion", 
  "-g",
  "-gcoff", 
  "-gdwarf-2",
  "-ggdb", 
  "-gstabs",
  "-gstabs+", 
  "-gvms",
  "-gxcoff", 
  "-gxcoff+",
  "-p", 
  "-pg",
  "-print-libgcc-file-name",
  "-print-multi-directory",
  "-print-multi-lib",
  "-print-search-dirs", 
  "-Q",
  "-pthread",
  "-save-temps", 
  "-time",
  "-O", 
  "-O0",        
  "-O1", 
  "-O2",
  "-O3", 
  "-Os",
  "-C", 
  "-E",
  "-H", 
  "-M",
  "-MM", 
  "-MG", 
  "-MP",
  "-MD", 
  "-MMD",
  "-nostdinc", 
  "-P",
  "-remap", 
  "-undef",
  "-nostdinc", 
  "-nostartfiles",
  "-nodefaultlibs",
  "-nostdlib", 
  "-pie",
  "-rdynamic", 
  "-s",
  "-static", 
  "-static-libgcc", 
  "-shared",
  "-symbolic",
  "-EB",
  "-EL",
  NULL
};

bool gcc_cmdlinet::parse(int argc, const char **argv)
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
      args.push_back(argv_i);
      add_arg(argv_i);
      parsed_argv.back().is_infile_name=true;
      continue;
    }    
    
    // add to new_argv    
    add_arg(argv_i);

    // also store in cmdlinet

    if(has_prefix(argv_i, "-f")) // f-options
    {
      set(argv_i);
    }
    else if(has_prefix(argv_i, "-W")) // W-options
    {
      // "Wp,..." is s special case. These are to pass stuff
      // to the preprocessor.
      if(has_prefix(argv_i, "-Wp,"))
      {
        std::string value=std::string(argv[i]+4);
        set("-WP,", value);
      }
      else
        set(argv_i);
    }
    else if(has_prefix(argv_i, "-m")) // m-options
    {
      set(argv_i);
    }
    else if(in_list(argv[i], gcc_options_without_argument)) // without argument
    {
      set(argv_i);
    }
    else
    {
      bool found=false;

      // separated only, and also allow concatenation with "="
      for(const char **o=gcc_options_with_separated_argument; *o!=NULL && !found; o++)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(i!=argc-1)
          {
            set(argv_i, argv[i+1]);
            add_arg(argv[i+1]);
            i++;
          }
          else
            set(argv_i, "");
        }
        else if(has_prefix(argv_i, std::string(*o)+"=")) // concatenated with "="
        {
          found=true;
          set(*o, argv[i]+strlen(*o)+1);
        }
      }

      // concatenated _or_ separated, e.g., -I
      for(const char **o=gcc_options_with_argument; *o!=NULL && !found; o++)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(i!=argc-1)
          {
            set(argv_i, argv[i+1]);
            add_arg(argv[i+1]);
            i++;
          }
          else
            set(argv_i, "");
        }
        else if(has_prefix(argv_i, *o)) // concatenated
        {
          found=true;
          set(*o, argv[i]+strlen(*o));
        }
      }

      // concatenated only
      for(const char **o=gcc_options_with_concatenated_argument; *o!=NULL && !found; o++)
      {
        if(has_prefix(argv_i, *o)) // concatenated
        {
          found=true;
          set(*o, argv[i]+strlen(*o));
        }
      }

      if(!found)
      {    
        // unrecognized option
        std::cout << "Warning: uninterpreted gcc option '" << argv[i] << "'" << std::endl;
      }
    }
  }

  return false;
}
