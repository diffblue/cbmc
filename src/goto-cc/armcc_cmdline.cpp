/*******************************************************************\

Module: A special command line object to mimick ARM's armcc

Author: Daniel Kroening

\*******************************************************************/

#include <string.h>

#include <iostream>

#include "armcc_cmdline.h"

/*******************************************************************\
 
Function: armcc_cmdlinet::parse
 
  Inputs: argument count, argument strings
 
 Outputs: none
 
 Purpose: parses the commandline options into a cmdlinet
 
\*******************************************************************/

// see
// http://infocenter.arm.com/help/topic/com.arm.doc.dui0472c/Cchbggjb.html

static const char *options_no_arg[]=
{
  // goto-cc-specific
  "--show-symbol-table",
  "--show-function-table",
  "--16",
  "--32",
  "--64",
  "--little-endian",
  "--big-endian",
  "--unsigned-char",
  "--ppc-macos",
  "--i386-macos",
  "--i386-linux",
  "--i386-win32",
  "--no-arch",
  "--no-library",
  "--string-abstraction",
                  
  // armcc
  "--help",
  "--show_cmdline",
  "--version_number",
  "--vsn",
  "--c90",
  "--c99",
  "--compile_all_input",
  "--no_compile_all_input",
  "--cpp",
  "--gnu",
  "--strict",
  "--no_strict",
  "--strict_warnings",
  "--kandr_include",
  "--reduce_paths",
  "--no_reduce_paths",
  "--sys_include",
  "--no-project",
  "--reinitialize_workdir",
  "--pch",
  "--pch_messages",
  "--no_pch_messages",
  "--pch_verbose",
  "--no_pch_verbose",
  "-C",
  "--code_gen",
  "--no_code_gen",
  "-E",
  "-M",
  "--anachronisms",
  "--no_anachronisms",
  "--dep_name",
  "--no_dep_name",
  "--export_all_vtbl",
  "--no_export_all_vtbl",
  "--force_new_nothrow",
  "--no_force_new_nothrow",
  "--friend_injection",
  "--no_friend_injection",
  "--guiding_decls",
  "--no_guiding_decls",
  "--implicit_include",
  "--no_implicit_include",
  "--implicit_include_searches",
  "--no_implicit_include_searches",
  "--implicit_typename",
  "--no_implicit_typename",
  "--nonstd_qualifider_deduction",
  "--no_nonstd_qualifider_deduction",
  "--old_specializations",
  "--no_old_specializations",
  "--parse_templates",
  "--no_parse_templates",
  "--rtti",
  "--no_rtti",
  "--using_std",
  "--no_using_std",
  "--vfe",
  "--no_vf",
  "--asm",
  "-c",
  "--depend_system_headers",
  "--no_depend_system_headers",
  "--interleave",
  "--list",
  "--md",
  "-S",
  "--split_sections",
  "--arm",
  "--thumb",
  "--debug",
  "--no_debug",
  "--debug_macros",
  "--no_debug_macros",
  "--dwarf2",
  "--dwarf3",
  "-g",
  "--remove_unneeded_entities",
  "--no_remove_unneeded_entities",
  "--alternative_tokens",
  "--no_alternative_tokens",
  "--bigend",
  "--dllexpot_all",
  "--no_dllexpot_all",
  "--dollar",
  "--no_dollar",
  "--enum_is_int",
  "--exceptions",
  "--no_exceptions",
  "--exceptions_unwind",
  "--no_exceptions_unwind",
  "--export_all_vtbl",
  "--no_export_all_vtbl",
  "--export_defs_implicitly",
  "--no_export_defs_implicitly",
  "--extend_initializers",
  "--no_extend_initializers",
  "--hide_all",
  "--no_hide_all",
  "--littleend",
  "--loose_implicit_cast",
  "--multibyte_chars",
  "--no_multibyte_chars",
  "--narrow_volatile_bitfields",
  "--restrict",
  "--no_restrict",
  "--signed_bitfields",
  "--unsigned_bitfields",
  "--signed_chars",
  "--unsigned_chars",
  "--split_ldm",
  "--unaligned_access",
  "--no_unaligned_access",
  "--vectorize",
  "--no_vectorize",
  "--vla",
  "--no_vla",
  "--wchar16",
  "--wchar32",
  "--autoinline",
  "--no_autoinline",
  "--data_reorder",
  "--no_data_reorder",
  "--forceinline",
  "--inline",
  "--no_inline",
  "--lower_ropi",
  "--no_lower_ropi",
  "--lower_rwpi",
  "--no_lower_rwpi",
  "--ltcg",
  "--multifile",
  "--no_multifile",
  "-Ospace",
  "-Otime",
  "-O1",
  "-O2",
  "-O3",
  "-O4",
  "--brief_diagnostics",
  "--no_brief_diagnostics",
  "--remarks",
  "--wrap_diagnostics",
  "--no_wrap_diagnostics",
  "--arm_linux",
  "--arm_linux_configure",
  "--arm_linux_paths",
  "--shared",
  "--translate_g++",
  "--translate_gcc",
  "--translate_gld",
  "-W",
  NULL
};

static const char *options_with_prefix[]=
{
  "--project=",
  "--workdir=",
  "--create_pch=",
  "--pch_dir=",
  "--use_pch=",
  "--pending_instantiations=",
  "--errors=",
  "--default_extension=",
  "--depend=",
  "--depend_format=",
  "--info=",
  "--compatible=",
  "--entry=",
  "--scatter=",
  "--fpu=",
  "--fp16_format=",
  "--fpmode=",
  "--fpu=",
  "--bss_threshold=",
  "--keep=",
  "--locale=",
  "--message_locale=",
  "--min_array_alignment=",
  "--pointer_alignment=",
  "--fpmode=",
  "--library_interface=",
  "--library_type=",
  "--retain=",
  "--diag_error=",
  "--diag_remark=",
  "--diag_style=",
  "--diag_suppress=",
  "--diag_warning=",
  "--preinclude=",
  "--via=",
  "--feedback=",
  "--profile=",
  "--apcs=",
  "--arm_linux_config_file=",
  "--configure_gcc=",
  "--configure_gld=",
  "--configure_sysroot=",
  "--configure_cpp_headers=",
  "--configure_extra_includes=",
  "--configure_extra_libraries=",
  NULL
};

static const char *options_with_arg[]=
{
  // goto-cc specific
  "--verbosity",
  "--function",

  // armcc-specific
  "-D",
  "-U",
  "-A",
  "-L",
  "-I",
  "-J",
  "-Warmcc,",
  "-o",
  "--cpu",
  "--apcs",
  NULL
};

bool armcc_cmdlinet::parse(int argc, const char **argv)
{
  for(int i=1; i<argc; i++)
  {
    if(strcmp(argv[i], "-")==0 ||
       argv[i][0]!='-')
    {
      args.push_back(argv[i]);
      continue;
    }    
    
    // it starts with - and it isn't "-"

    std::string prefix;

    if(in_list(argv[i], options_no_arg))
    {
      // options that don't have any arguments
      set(argv[i]);
    }
    else if(prefix_in_list(argv[i], options_with_arg, prefix))
    {
      // options that have a separated _or_ concatenated argument
      if(strlen(argv[i])>prefix.size()) // concatenated?
        set(prefix, std::string(argv[i], prefix.size(), std::string::npos));
      else
      {
        // Separated.
        if(i!=argc-1) // Guard against end of command line.
        {
          set(prefix, argv[i+1]);
          i++;
        }
        else
          set(prefix, "");
      }
    } 
    else if(prefix_in_list(argv[i], options_with_prefix, prefix))
    {
      // options that have a concatenated argument
      set(prefix, std::string(argv[i], prefix.size(), std::string::npos));
    }
    else
    { // unrecognized option
      std::cout << "Warning: uninterpreted armcc option '" 
                << argv[i] << "'" << std::endl;
    }
  }

  return false;
}
