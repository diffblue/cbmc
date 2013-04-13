/*******************************************************************\

Module: LD Mode

Author: Daniel Kroening, 2013

\*******************************************************************/

#include <cstdlib>
#include <iostream>

#include <util/config.h>

#include "compile.h"
#include "version.h"
#include "ld_mode.h"

/*******************************************************************\

Function: ld_modet::doit

  Inputs:

 Outputs:

 Purpose: does it.

\*******************************************************************/

bool ld_modet::doit()
{
  if(cmdline.isset("help"))
  {
    help();
    return false;
  }

  int verbosity=1;

  compilet compiler(cmdline);
  
  if(cmdline.isset('v') || cmdline.isset('V'))
  {
    // This a) prints the version and b) increases verbosity.
    // Linking continues, don't exit!
    
    print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
    
    // 'V' should also print some supported "emulations".
  }

  if(cmdline.isset("version"))
  {
    print("GNU ld version 2.16.91 20050610 (goto-cc " GOTOCC_VERSION ")");
    print("Copyright (C) 2006-2013 Daniel Kroening, Christoph Wintersteiger");
    return false; // Exit!
  }

  if(cmdline.isset("verbosity"))
    verbosity=atoi(cmdline.getval("verbosity"));

  compiler.set_verbosity(verbosity);
  set_verbosity(verbosity);

  if(produce_hybrid_binary)
    debug("LD mode (hybrid)");
  else
    debug("LD mode");
  
  // get configuration
  config.set(cmdline);
  
  // determine actions to be undertaken
  compiler.mode=compilet::LINK_LIBRARY;

  compiler.object_file_extension="o";

  if(cmdline.isset('L'))
    compiler.library_paths=cmdline.get_values('L');
    // Don't add the system paths!

  if(cmdline.isset("library-path"))
    compiler.library_paths=cmdline.get_values("library-path");
    // Don't add the system paths!

  if(cmdline.isset('l'))
    compiler.libraries=cmdline.get_values('l');

  if(cmdline.isset("library"))
    compiler.libraries=cmdline.get_values("library");

  if(cmdline.isset('o'))
  {
    // given gcc -o file1 -o file2,
    // gcc will output to file2, not file1
    compiler.output_file_object=cmdline.get_values('o').back();
    compiler.output_file_executable=cmdline.get_values('o').back();
  }
  else if(cmdline.isset("output"))
  {
    // given gcc -o file1 -o file2,
    // gcc will output to file2, not file1
    compiler.output_file_object=cmdline.get_values("output").back();
    compiler.output_file_executable=cmdline.get_values("output").back();
  }
  else
  {
    // defaults
    compiler.output_file_object="";
    compiler.output_file_executable="a.out";
  }
    
  // do all the rest
  bool result=compiler.doit();

  #if 0
  if(produce_hybrid_binary)
  {
    if(gcc_hybrid_binary(original_args))
      result=true;
  }
  #endif
  
  return result;
}

/*******************************************************************\

Function: ld_modet::gcc_hybrid_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
int ld_modet::gcc_hybrid_binary(const cmdlinet::argst &input_files)
{
  if(input_files.empty())
    return 0;

  std::list<std::string> output_files;
  
  if(cmdline.isset('c'))
  {
    if(cmdline.isset('o'))
    {
      // there should be only one input file
      output_files.push_back(cmdline.getval('o'));
    }
    else
    {
      for(cmdlinet::argst::const_iterator
          i_it=input_files.begin();
          i_it!=input_files.end();
          i_it++)
      {
        if(is_supported_source_file(*i_it) && cmdline.isset('c'))
          output_files.push_back(get_base_name(*i_it)+".o");
      }
    }
  }
  else
  {
    // -c is not given
    if(cmdline.isset('o'))
      output_files.push_back(cmdline.getval('o'));
    else
      output_files.push_back("a.out");      
  }

  if(output_files.empty()) return 0;

  debug("Running gcc to generate hybrid binary");
  
  // save the goto-cc output files
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    rename(it->c_str(), (*it+".goto-cc-saved").c_str());
  }

  // build new argv
  std::vector<std::string> new_argv;
  
  new_argv.reserve(cmdline.parsed_argv.size());
  
  bool skip_next=false;

  for(ld_cmdlinet::parsed_argvt::const_iterator
      it=cmdline.parsed_argv.begin();
      it!=cmdline.parsed_argv.end();
      it++)
  {
    if(skip_next)
    {
      // skip
      skip_next=false;
    }
    else if(it->arg=="--verbosity")
    {
      // ignore here
      skip_next=true;
    }
    else
      new_argv.push_back(it->arg);
  }

  // overwrite argv[0]
  assert(new_argv.size()>=1);
  new_argv[0]="gcc";
  
  #if 0
  std::cout << "RUN:";
  for(unsigned i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif
  
  int result=run("gcc", new_argv);
  
  // merge output from gcc with goto-binaries
  // using objcopy
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    #ifdef __linux__
    debug("merging "+*it);

    if(!cmdline.isset('c'))
    {
      // remove any existing goto-cc section
      std::vector<std::string> objcopy_argv;
    
      objcopy_argv.push_back("objcopy");
      objcopy_argv.push_back("--remove-section=goto-cc");
      objcopy_argv.push_back(*it);
      
      run(objcopy_argv[0], objcopy_argv);
    }

    // now add goto-binary as goto-cc section  
    std::string saved=*it+".goto-cc-saved";

    std::vector<std::string> objcopy_argv;
  
    objcopy_argv.push_back("objcopy");
    objcopy_argv.push_back("--add-section");
    objcopy_argv.push_back("goto-cc="+saved);
    objcopy_argv.push_back(*it);
    
    run(objcopy_argv[0], objcopy_argv);

    remove(saved.c_str());    

    #elif defined(__APPLE__)
    // Mac

    for(std::list<std::string>::const_iterator
        it=output_files.begin();
        it!=output_files.end();
        it++)
    {
      debug("merging "+*it);

      std::vector<std::string> lipo_argv;
    
      // now add goto-binary as hppa7100LC section  
      std::string saved=*it+".goto-cc-saved";

      lipo_argv.push_back("lipo");
      lipo_argv.push_back(*it);
      lipo_argv.push_back("-create");
      lipo_argv.push_back("-arch");
      lipo_argv.push_back("hppa7100LC");
      lipo_argv.push_back(saved);
      lipo_argv.push_back("-output");
      lipo_argv.push_back(*it);
      
      run(lipo_argv[0], lipo_argv);

      remove(saved.c_str());    
    }
    
    return 0;
    
    #else
    
    error("binary merging not implemented for this architecture");
    return 1;

    #endif
  }
  
  return result!=0;
}
#endif

/*******************************************************************\

Function: ld_modet::help_mode

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void ld_modet::help_mode()
{
  std::cout << "goto-ld understands the options of ld plus the following.\n\n";
}

