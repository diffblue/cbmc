/*******************************************************************\

Module: Assembler Mode

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Assembler Mode

#include "as_mode.h"

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <fstream>
#include <iostream>
#include <cstring>

#include <util/config.h>
#include <util/get_base_name.h>
#include <util/run.h>
#include <util/tempdir.h>
#include <util/version.h>

#include "compile.h"

static std::string assembler_name(
  const cmdlinet &cmdline,
  const std::string &base_name)
{
  if(cmdline.isset("native-assembler"))
    return cmdline.get_value("native-assembler");

  if(base_name=="as86" ||
     base_name.find("goto-as86")!=std::string::npos)
    return "as86";

  std::string::size_type pos=base_name.find("goto-as");

  if(pos==std::string::npos)
    return "as";

  std::string result=base_name;
  result.replace(pos, 7, "as");

  return result;
}

as_modet::as_modet(
  goto_cc_cmdlinet &_cmdline,
  const std::string &_base_name,
  bool _produce_hybrid_binary):
  goto_cc_modet(_cmdline, _base_name, message_handler),
  produce_hybrid_binary(_produce_hybrid_binary),
  native_tool_name(assembler_name(cmdline, base_name))
{
}

/// does it.
int as_modet::doit()
{
  if(cmdline.isset('?') ||
     cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  bool act_as_as86=
    base_name=="as86" ||
    base_name.find("goto-as86")!=std::string::npos;

  if((cmdline.isset('v') && act_as_as86) ||
     cmdline.isset("version"))
  {
    if(act_as_as86)
      status() << "as86 version: 0.16.17 (goto-cc " << CBMC_VERSION << ")"
               << eom;
    else
      status() << "GNU assembler version 2.20.51.0.7 20100318"
               << " (goto-cc " << CBMC_VERSION << ")" << eom;

    status()
      << '\n'
      << "Copyright (C) 2006-2014 Daniel Kroening, Christoph Wintersteiger\n"
      << "CBMC version: " << CBMC_VERSION << '\n'
      << "Architecture: " << config.this_architecture() << '\n'
      << "OS: " << config.this_operating_system() << eom;

    return EX_OK; // Exit!
  }

  auto default_verbosity = (cmdline.isset("w-") || cmdline.isset("warn")) ?
    messaget::M_WARNING : messaget::M_ERROR;
  eval_verbosity(
    cmdline.get_value("verbosity"), default_verbosity, message_handler);

  if(act_as_as86)
  {
    if(produce_hybrid_binary)
      debug() << "AS86 mode (hybrid)" << eom;
    else
      debug() << "AS86 mode" << eom;
  }
  else
  {
    if(produce_hybrid_binary)
      debug() << "AS mode (hybrid)" << eom;
    else
      debug() << "AS mode" << eom;
  }

  // get configuration
  config.set(cmdline);

  // determine actions to be undertaken
  compilet compiler(cmdline, message_handler, cmdline.isset("fatal-warnings"));

  if(cmdline.isset('b')) // as86 only
  {
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;
    debug() << "Compiling and linking an executable" << eom;
  }
  else
  {
    compiler.mode=compilet::COMPILE_LINK;
    debug() << "Compiling and linking a library" << eom;
  }

  config.ansi_c.mode=configt::ansi_ct::flavourt::GCC;

  compiler.object_file_extension="o";

  if(cmdline.isset('o'))
  {
    compiler.output_file_object=cmdline.get_value('o');
    compiler.output_file_executable=cmdline.get_value('o');
  }
  else if(cmdline.isset('b')) // as86 only
  {
    compiler.output_file_object=cmdline.get_value('b');
    compiler.output_file_executable=cmdline.get_value('b');
  }
  else
  {
    compiler.output_file_object="a.out";
    compiler.output_file_executable="a.out";
  }

  // We now iterate over any input files

  temp_dirt temp_dir("goto-cc-XXXXXX");

  for(goto_cc_cmdlinet::parsed_argvt::iterator
      arg_it=cmdline.parsed_argv.begin();
      arg_it!=cmdline.parsed_argv.end();
      arg_it++)
  {
    if(!arg_it->is_infile_name)
      continue;

    // extract the preprocessed source from the file
    std::string infile=arg_it->arg=="-"?cmdline.stdin_file:arg_it->arg;
    std::ifstream is(infile);
    if(!is.is_open())
    {
      error() << "Failed to open input source " << infile << eom;
      return 1;
    }

    // there could be multiple source files in case GCC's --combine
    // was used
    unsigned outputs=0;
    std::string line;
    std::ofstream os;
    std::string dest;

    const std::string comment2=act_as_as86 ? "::" : "##";

    // search for comment2 GOTO-CC
    // strip comment2 from all subsequent lines
    while(std::getline(is, line))
    {
      if(line==comment2+" GOTO-CC")
      {
        if(outputs>0)
        {
          assert(!dest.empty());
          compiler.add_input_file(dest);
          os.close();
        }

        ++outputs;
        std::string new_name=
          get_base_name(infile, true)+"_"+
          std::to_string(outputs)+".i";
        dest=temp_dir(new_name);

        os.open(dest);
        if(!os.is_open())
        {
          error() << "Failed to tmp output file " << dest << eom;
          return 1;
        }

        continue;
      }
      else if(outputs==0)
        continue;

      if(line.size()>2)
        os << line.substr(2) << '\n';
    }

    if(outputs>0)
    {
      assert(!dest.empty());
      compiler.add_input_file(dest);
    }
    else
      warning() << "No GOTO-CC section found in " << arg_it->arg << eom;
  }

  // Revert to as in case there is no source to compile

  if(compiler.source_files.empty())
    return run_as(); // exit!

  // do all the rest
  if(compiler.doit())
    return 1; // GCC exit code for all kinds of errors

  // We can generate hybrid ELF and Mach-O binaries
  // containing both executable machine code and the goto-binary.
  if(produce_hybrid_binary)
    return as_hybrid_binary();

  return EX_OK;
}

/// run as or as86 with original command line
int as_modet::run_as()
{
  assert(!cmdline.parsed_argv.empty());

  // build new argv
  std::vector<std::string> new_argv;
  new_argv.reserve(cmdline.parsed_argv.size());
  for(const auto &a : cmdline.parsed_argv)
    new_argv.push_back(a.arg);

  // overwrite argv[0]
  new_argv[0]=native_tool_name;

  #if 0
  std::cout << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << '\n';
  #endif

  return run(new_argv[0], new_argv, cmdline.stdin_file, "", "");
}

int as_modet::as_hybrid_binary()
{
  std::string output_file="a.out";

  if(cmdline.isset('o'))
  {
    output_file=cmdline.get_value('o');
  }
  else if(cmdline.isset('b')) // as86 only
    output_file=cmdline.get_value('b');

  if(output_file=="/dev/null")
    return EX_OK;

  debug() << "Running " << native_tool_name
          << " to generate hybrid binary" << eom;

  // save the goto-cc output file
  int result=rename(
    output_file.c_str(),
    (output_file+".goto-cc-saved").c_str());
  if(result!=0)
  {
    error() << "Rename failed: " << std::strerror(errno) << eom;
    return result;
  }

  result=run_as();

  // merge output from as with goto-binaries
  // using objcopy, or do cleanup if an earlier call failed
  debug() << "merging " << output_file << eom;
  std::string saved=output_file+".goto-cc-saved";

  #if defined(__linux__) || defined(__FreeBSD_kernel__)
  if(result==0)
  {
    // remove any existing goto-cc section
    std::vector<std::string> objcopy_argv;

    objcopy_argv.push_back("objcopy");
    objcopy_argv.push_back("--remove-section=goto-cc");
    objcopy_argv.push_back(output_file);

    result = run(objcopy_argv[0], objcopy_argv);
  }

  if(result==0)
  {
    // now add goto-binary as goto-cc section
    std::vector<std::string> objcopy_argv;

    objcopy_argv.push_back("objcopy");
    objcopy_argv.push_back("--add-section");
    objcopy_argv.push_back("goto-cc="+saved);
    objcopy_argv.push_back(output_file);

    result = run(objcopy_argv[0], objcopy_argv);
  }

  int remove_result=remove(saved.c_str());
  if(remove_result!=0)
  {
    error() << "Remove failed: " << std::strerror(errno) << eom;
    if(result==0)
      result=remove_result;
  }

  #elif defined(__APPLE__)
  // Mac
  if(result==0)
  {
    std::vector<std::string> lipo_argv;

    // now add goto-binary as hppa7100LC section
    lipo_argv.push_back("lipo");
    lipo_argv.push_back(output_file);
    lipo_argv.push_back("-create");
    lipo_argv.push_back("-arch");
    lipo_argv.push_back("hppa7100LC");
    lipo_argv.push_back(saved);
    lipo_argv.push_back("-output");
    lipo_argv.push_back(output_file);

    result = run(lipo_argv[0], lipo_argv);
  }

  int remove_result=remove(saved.c_str());
  if(remove_result!=0)
  {
    error() << "Remove failed: " << std::strerror(errno) << eom;
    if(result==0)
      result=remove_result;
  }

  #else
  error() << "binary merging not implemented for this platform" << eom;
  result = 1;
  #endif

  return result;
}

/// display command line help
void as_modet::help_mode()
{
  std::cout << "goto-as understands the options of as plus the following.\n\n";
}
