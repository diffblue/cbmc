/*******************************************************************\

Module: A special command line object for the gcc-like options

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <cassert>
#include <cstring>
#include <iostream>

#include "gcc_cmdline.h"

/*******************************************************************\
 
Function: gcc_cmdlinet::option_nr
 
  Inputs: option name
 
 Outputs: option number
 
 Purpose: 
 
\*******************************************************************/

int gcc_cmdlinet::option_nr(const std::string &opt)
{
  assert(opt.size()>=2);
  if(std::string(opt, 0, 2)=="--") // something like --option
  {
    std::string opt_str=std::string(opt, 2, std::string::npos);
    int opt_nr=getoptnr(opt_str);
    if(opt_nr==-1)
    {
      optiont option;
      option.islong=true;
      option.optstring=opt_str;
      option.optchar=0;
      options.push_back(option);
      opt_nr=options.size()-1;
    }
    return opt_nr;
  }
  else if(opt.size()==2) // something like -o
  {
    char opt_char=opt[1];
    int opt_nr=getoptnr(opt_char);
    if(opt_nr==-1)
    {
      optiont option;
      option.islong=false;
      option.optstring="";
      option.optchar=opt_char;
      options.push_back(option);
      opt_nr=options.size()-1;
    }
    return opt_nr;
  }
  else // something like -option
  {
    std::string opt_str=std::string(opt, 1, std::string::npos);
    int opt_nr=getoptnr(opt_str);
    if(opt_nr==-1)
    {
      optiont option;
      option.islong=true;
      option.optstring=opt_str;
      option.optchar=0;
      options.push_back(option);
      opt_nr=options.size()-1;
    }
    return opt_nr;
  }
}

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
  "--unsigned-char", // NON-GCC
  "--no-arch", // NON-GCC            
  "--xml", // NON-GCC
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
  for(int i=1; i<argc; i++)
  {
    // file?
    if(strcmp(argv[i], "-")==0 ||
       argv[i][0]!='-')
    {
      args.push_back(argv[i]);
      continue;
    }    

    if(strncmp(argv[i], "-f", 2)==0) // f-options
    {
      set(argv[i]);
    }
    else if(strncmp(argv[i], "-W", 2)==0) // W-options
    {
      // "Wp,..." is s special case. These are to pass stuff
      // to the preprocessor.
      if(strncmp(argv[i], "-Wp,", 4)==0)
      {
        std::string value=std::string(argv[i]+4);
        set("-WP,", value);
      }
      else
        set(argv[i]);
    }
    else if(strncmp(argv[i], "-m", 2)==0) // m-options
    {
      set(argv[i]);
    }
    else if( // options that have an = argument
      strncmp(argv[i], "-std", 4)==0 ||
      strncmp(argv[i], "-print-file-name", 16)==0 ||
      strncmp(argv[i], "-print-prog-name", 16)==0 ||
      strncmp(argv[i], "-specs", 6)==0 ||
      strncmp(argv[i], "--sysroot", 9)==0
    )
    {
      std::string opt_str=argv[i];
      std::size_t p=opt_str.find('=');
      if(p!=std::string::npos)
      {
        std::string opt=opt_str.substr(0, p-1);
        set(opt, std::string(opt_str, p+1, std::string::npos));
      }
    }
    else
    {
      bool found=false;

      // without argument
      for(const char **o=gcc_options_without_argument; *o!=NULL && !found; o++)
      {
        if(strcmp(argv[i], *o)==0)
        {
          found=true;
          set(argv[i]);
        }
      }
      
      // separated only    
      for(const char **o=gcc_options_with_separated_argument; *o!=NULL && !found; o++)
      {
        if(strcmp(argv[i], *o)==0) // separated
        {
          found=true;
          if(i!=argc-1)
          {
            set(argv[i], argv[i+1]);
            i++;
          }
          else
            set(argv[i], "");
        }
      }

      // concatenated _or_ separated, e.g., -I
      for(const char **o=gcc_options_with_argument; *o!=NULL && !found; o++)
      {
        if(strcmp(argv[i], *o)==0) // separated
        {
          found=true;
          if(i!=argc-1)
          {
            set(argv[i], argv[i+1]);
            i++;
          }
          else
            set(argv[i], "");
        }
        else if(strncmp(argv[i], *o, strlen(*o))==0) // concatenated
        {
          found=true;
          set(*o, argv[i]+strlen(*o));
        }
      }

      // concatenated only
      for(const char **o=gcc_options_with_concatenated_argument; *o!=NULL && !found; o++)
      {
        if(strncmp(argv[i], *o, strlen(*o))==0) // concatenated
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
