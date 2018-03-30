/*******************************************************************\

Module: A special command line object for the gcc-like options

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// A special command line object for the gcc-like options

#include "gcc_cmdline.h"

#include <cassert>
#include <cstring>
#include <iostream>
#include <fstream>

#include <util/prefix.h>

/// parses the command line options into a cmdlinet
/// \par parameters: argument count, argument strings
/// \return none
// non-gcc options
const char *goto_cc_options_with_separated_argument[]=
{
  "--verbosity",
  "--function",
  "--native-compiler",
  "--native-linker",
  "--print-rejected-preprocessed-source",
  nullptr
};

// non-gcc options
const char *goto_cc_options_without_argument[]=
{
  "--show-symbol-table",
  "--show-function-table",
  "--ppc-macos",
  "--i386-linux",
  "--i386-win32",
  "--i386-macos",
  "--winx64",
  "--string-abstraction",
  "--no-library",
  "--16",
  "--32",
  "--64",
  "--little-endian",
  "--big-endian",
  "--no-arch",
  "--partial-inlining",
  "-?",
  nullptr
};

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
  "-U",
  "-u", // goes to linker
  "-T", // goes to linker
  nullptr
};

const char *gcc_options_with_separated_argument[]=
{
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
  "-mcpu",
  "-mtune",
  "-march",
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
  nullptr
};

const char *gcc_options_with_concatenated_argument[]=
{
  "-d",
  "-g",
  "-A",
  nullptr
};

const char *gcc_options_without_argument[]=
{
  "--help",
  "-h",
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
  "-mno-unaligned-access",
  "-mthumb",
  "-mthumb-interwork",
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
  nullptr
};

bool gcc_cmdlinet::parse(int argc, const char **argv)
{
  assert(argc>0);
  add_arg(argv[0]);

  argst args;
  args.reserve(argc-1);

  for(int i=1; i<argc; i++)
    args.push_back(argv[i]);

  bool result=parse_arguments(args, false);

  parse_specs();

  return result;
}

bool gcc_cmdlinet::parse_arguments(
  const argst &args,
  bool in_spec_file)
{
  for(argst::const_iterator it=args.begin();
      it!=args.end();
      ++it)
  {
    const std::string &argv_i=*it;

    // options file?
    if(has_prefix(argv_i, "@"))
    {
      std::ifstream opts_file(argv_i.substr(1));
      std::string line;

      while(std::getline(opts_file, line))
      {
        // erase leading whitespace
        line.erase(0, line.find_first_not_of("\t "));

        if(!line.empty())
          parse_specs_line(line);
      }

      continue;
    }

    // file?
    if(argv_i=="-" || !has_prefix(argv_i, "-"))
    {
      if(!in_spec_file)
        add_infile_arg(argv_i);
      continue;
    }

    if(!in_spec_file)
    {
      argst::const_iterator next=it;
      ++next;

      bool found=false;

      if(in_list(argv_i.c_str(),
                 goto_cc_options_without_argument)) // without argument
      {
        set(argv_i);
        found=true;
      }

      // separated only, and also allow concatenation with "="
      for(const char **o=goto_cc_options_with_separated_argument;
          *o!=nullptr && !found;
          ++o)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(next!=args.end())
          {
            set(argv_i, *next);
            ++it;
          }
          else
            set(argv_i, "");
        }
        // concatenated with "="
        else if(has_prefix(argv_i, std::string(*o)+"="))
        {
          found=true;
          set(*o, argv_i.substr(strlen(*o)+1));
        }
      }

      if(found)
        continue;

      // add to new_argv
      add_arg(argv_i);
    }

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
          *o!=nullptr && !found;
          ++o)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(next!=args.end())
          {
            set(argv_i, *next);
            if(!in_spec_file)
              add_arg(*next);
            ++it;
          }
          else
            set(argv_i, "");
        }
        // concatenated with "="
        else if(has_prefix(argv_i, std::string(*o)+"="))
        {
          found=true;
          set(*o, argv_i.substr(strlen(*o)+1));
        }
      }

      // concatenated _or_ separated, e.g., -I
      for(const char **o=gcc_options_with_argument;
          *o!=nullptr && !found;
          ++o)
      {
        if(argv_i==*o) // separated
        {
          found=true;
          if(next!=args.end())
          {
            set(argv_i, *next);
            if(!in_spec_file)
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
          *o!=nullptr && !found;
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
                  << "'\n";
      }
    }
  }

  return false;
}

/// Parse GCC spec files https://gcc.gnu.org/onlinedocs/gcc/Spec-Files.html
void gcc_cmdlinet::parse_specs_line(const std::string &line)
{
  // initial whitespace has been stripped
  assert(!line.empty());
  assert(line[0]!=' ' && line[0]!='\t');

  argst args;

  for(std::string::size_type arg_start=0, arg_end=0;
      arg_end!=std::string::npos;
      arg_start=line.find_first_not_of("\t ", arg_end))
  {
    arg_end=line.find_first_of("\t ", arg_start);
    args.push_back(line.substr(arg_start, arg_end-arg_start));
  }

  parse_arguments(args, true);
}

/// Parse GCC spec files https://gcc.gnu.org/onlinedocs/gcc/Spec-Files.html
void gcc_cmdlinet::parse_specs()
{
  const std::string &specs_file_name=get_value("specs");
  if(specs_file_name.empty())
    return;

  std::ifstream specs_file(specs_file_name);
  std::string line;
  bool use_line=false;

  while(std::getline(specs_file, line))
  {
    // erase leading whitespace
    line.erase(0, line.find_first_not_of("\t "));

    if(line.empty())
      // blank lines reset the mode
      use_line=false;
    else if(!use_line &&
            (line=="*link_libgcc:" ||
             line=="*lib:" ||
             line=="*libgcc:" ||
             line=="*link:"))
      use_line=true;
    else if(use_line)
      parse_specs_line(line);
    else
    {
      // TODO need message interface
      // debug() << "Warning: ignoring spec " << line << eom;
    }
  }
}
