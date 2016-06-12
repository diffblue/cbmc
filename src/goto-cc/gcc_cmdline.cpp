/*******************************************************************\

Module: A special command line object for the gcc-like options

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <cassert>
#include <cstring>
#include <iostream>

#include <util/prefix.h>

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
  "-l",
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
  "--native-compiler", // non-gcc
  "--native-linker", // non-gcc
  "--print-rejected-preprocessed-source", // non-gcc
  "-aux-info",
  "--param", // Apple only
  "-imacros",
  "-iprefix",
  "-iwithprefix",
  "-iwithprefixbefore",
  "-isystem",
  "-isysroot",
  "-imultilib",
  "-imultiarch",
  "-Xpreprocessor",
  "-Xassembler",
  "-Xlinker",
  "-b",
  "-std",
  "--std",
  "-print-file-name",
  "-print-prog-name",
  "-specs",
  "--sysroot",
  "--include", // undocumented
  "-current_version", // on the Mac
  "-compatibility_version",  // on the Mac
  "-z",
  NULL
};

const char *gcc_options_with_concatenated_argument[]=
{
  "-d",
  "-g",
  "-A",
  "-U",
  NULL
};

const char *gcc_options_without_argument[]=
{
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
  "-dylib", // for ld mimicking on MacOS
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
  "-Qn",
  "-Qy",
  "-pthread",
  "-save-temps",
  "-time",
  "-O",
  "-O0",
  "-O1",
  "-O2",
  "-O3",
  "-Os",
  "-Oz", // Apple only
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
  "--static",
  "-shared",
  "--shared",
  "-shared-libgcc",
  "-symbolic",
  "-EB",
  "-EL",
  "-fast", // Apple only
  NULL
};

bool gcc_cmdlinet::parse(int argc, const char **argv)
{
  assert(argc>0);
  add_arg(argv[0]);

  argst args;
  args.reserve(argc-1);

  for(int i=1; i<argc; i++)
    args.push_back(argv[i]);

  return parse_arguments(args);
}

/*******************************************************************\

Function: gcc_cmdlinet::parse_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool gcc_cmdlinet::parse_arguments(const argst &args)
{
  for(argst::const_iterator it=args.begin();
      it!=args.end();
      ++it)
  {
    const std::string &argv_i=*it;

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
        std::string value=argv_i.substr(4);
        set("-WP,", value);
      }
      else
        set(argv_i);
    }
    else if(has_prefix(argv_i, "-m")) // m-options
    {
      // these sometimes come with a value separated by '=', e.g.,
      // -march=cpu_type
      std::size_t equal_pos=argv_i.find('=');

      if(equal_pos==std::string::npos)
        set(argv_i); // no value
      else
        set(argv_i.substr(0, equal_pos), argv_i.substr(equal_pos+1));
    }
    // without argument
    else if(in_list(argv_i.c_str(), gcc_options_without_argument))
    {
      set(argv_i);
    }
    else
    {
      argst::const_iterator next=it;
      ++next;

      bool found=false;

      // separated only, and also allow concatenation with "="
      for(const char **o=gcc_options_with_separated_argument;
          *o!=NULL && !found;
          ++o)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(next!=args.end())
          {
            set(argv_i, *next);
            add_arg(*next);
            ++it;
          }
          else
            set(argv_i, "");
        }
        else if(has_prefix(argv_i, std::string(*o)+"=")) // concatenated with "="
        {
          found=true;
          set(*o, argv_i.substr(strlen(*o)+1));
        }
      }

      // concatenated _or_ separated, e.g., -I
      for(const char **o=gcc_options_with_argument;
          *o!=NULL && !found;
          ++o)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(next!=args.end())
          {
            set(argv_i, *next);
            add_arg(*next);
            ++it;
          }
          else
            set(argv_i, "");
        }
        else if(has_prefix(argv_i, *o)) // concatenated
        {
          found=true;
          set(*o, argv_i.substr(strlen(*o)));
        }
      }

      // concatenated only
      for(const char **o=gcc_options_with_concatenated_argument;
          *o!=NULL && !found;
          ++o)
      {
        if(has_prefix(argv_i, *o)) // concatenated
        {
          found=true;
          set(*o, argv_i.substr(strlen(*o)));
        }
      }

      if(!found)
      {
        // unrecognized option
        std::cerr << "Warning: uninterpreted gcc option '" << argv_i
                  << "'" << std::endl;
      }
    }
  }

  return false;
}
