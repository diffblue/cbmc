/*******************************************************************\

Module: GCC Mode

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// GCC Mode

#include "gcc_mode.h"

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <iostream>
#include <fstream>
#include <numeric>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/file_util.h>
#include <util/get_base_name.h>
#include <util/invariant.h>
#include <util/prefix.h>
#include <util/run.h>
#include <util/suffix.h>
#include <util/tempdir.h>
#include <util/version.h>

#include "compile.h"
#include "goto_cc_cmdline.h"
#include "hybrid_binary.h"
#include "linker_script_merge.h"

static std::string compiler_name(
  const cmdlinet &cmdline,
  const std::string &base_name)
{
  if(cmdline.isset("native-compiler"))
    return cmdline.get_value("native-compiler");

  if(base_name=="bcc" ||
     base_name.find("goto-bcc")!=std::string::npos)
    return "bcc";

  if(base_name=="goto-clang")
    return "clang";

  std::string::size_type pos=base_name.find("goto-gcc");

  if(pos==std::string::npos ||
     base_name=="goto-gcc" ||
     base_name=="goto-ld")
  {
    #ifdef __FreeBSD__
    return "clang";
    #else
    return "gcc";
    #endif
  }

  std::string result=base_name;
  result.replace(pos, 8, "gcc");

  return result;
}

static std::string linker_name(
  const cmdlinet &cmdline,
  const std::string &base_name)
{
  if(cmdline.isset("native-linker"))
    return cmdline.get_value("native-linker");

  std::string::size_type pos=base_name.find("goto-ld");

  if(pos==std::string::npos ||
     base_name=="goto-gcc" ||
     base_name=="goto-ld")
    return "ld";

  std::string result=base_name;
  result.replace(pos, 7, "ld");

  return result;
}

gcc_modet::gcc_modet(
  goto_cc_cmdlinet &_cmdline,
  const std::string &_base_name,
  bool _produce_hybrid_binary):
  goto_cc_modet(_cmdline, _base_name, gcc_message_handler),
  produce_hybrid_binary(_produce_hybrid_binary),
  goto_binary_tmp_suffix(".goto-cc-saved"),

  // Keys are architectures specified in configt::set_arch().
  // Values are lists of GCC architectures that can be supplied as
  // arguments to the -march, -mcpu, and -mtune flags (see the GCC
  // manual https://gcc.gnu.org/onlinedocs/).
  arch_map(
  {
    // ARM information taken from the following:
    //
    // the "ARM core timeline" table on this page:
    // https://en.wikipedia.org/wiki/List_of_ARM_microarchitectures
    //
    // articles on particular core groups, e.g.
    // https://en.wikipedia.org/wiki/ARM9
    //
    // The "Cores" table on this page:
    // https://en.wikipedia.org/wiki/ARM_architecture
    // NOLINTNEXTLINE(whitespace/braces)
    {"arm", {
      "strongarm", "strongarm110", "strongarm1100", "strongarm1110",
      "arm2", "arm250", "arm3", "arm6", "arm60", "arm600", "arm610",
      "arm620", "fa526", "fa626", "fa606te", "fa626te", "fmp626",
      "xscale", "iwmmxt", "iwmmxt2", "xgene1"
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"armhf", {
      "armv7", "arm7m", "arm7d", "arm7dm", "arm7di", "arm7dmi",
      "arm70", "arm700", "arm700i", "arm710", "arm710c", "arm7100",
      "arm720", "arm7500", "arm7500fe", "arm7tdmi", "arm7tdmi-s",
      "arm710t", "arm720t", "arm740t", "mpcore", "mpcorenovfp",
      "arm8", "arm810", "arm9", "arm9e", "arm920", "arm920t",
      "arm922t", "arm946e-s", "arm966e-s", "arm968e-s", "arm926ej-s",
      "arm940t", "arm9tdmi", "arm10tdmi", "arm1020t", "arm1026ej-s",
      "arm10e", "arm1020e", "arm1022e", "arm1136j-s", "arm1136jf-s",
      "arm1156t2-s", "arm1156t2f-s", "arm1176jz-s", "arm1176jzf-s",
      "cortex-a5", "cortex-a7", "cortex-a8", "cortex-a9",
      "cortex-a12", "cortex-a15", "cortex-a53", "cortex-r4",
      "cortex-r4f", "cortex-r5", "cortex-r7", "cortex-m7",
      "cortex-m4", "cortex-m3", "cortex-m1", "cortex-m0",
      "cortex-m0plus", "cortex-m1.small-multiply",
      "cortex-m0.small-multiply", "cortex-m0plus.small-multiply",
      "marvell-pj4", "ep9312", "fa726te",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"arm64", {
      "cortex-a57", "cortex-a72", "exynos-m1"
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"hppa", {"1.0", "1.1", "2.0"}}, // NOLINTNEXTLINE(whitespace/braces)
    // PowerPC
    // https://en.wikipedia.org/wiki/List_of_PowerPC_processors
    // NOLINTNEXTLINE(whitespace/braces)
    {"powerpc", {
      "powerpc", "601", "602", "603", "603e", "604", "604e", "630",
      // PowerPC G3 == 7xx series
      "G3", "740", "750",
      // PowerPC G4 == 74xx series
      "G4", "7400", "7450",
      // SoC and low power: https://en.wikipedia.org/wiki/PowerPC_400
      "401", "403", "405", "405fp", "440", "440fp", "464", "464fp",
      "476", "476fp",
      // e series. x00 are 32-bit, x50 are 64-bit. See e.g.
      // https://en.wikipedia.org/wiki/PowerPC_e6500
      "e300c2", "e300c3", "e500mc", "ec603e",
      // https://en.wikipedia.org/wiki/Titan_(microprocessor)
      "titan",
    }},
    // NOLINTNEXTLINE(whitespace/braces)
    {"powerpc64", {
      "powerpc64",
      // First IBM 64-bit processor
      "620",
      "970", "G5"
      // All IBM POWER processors are 64 bit, but POWER 8 is
      // little-endian so not in this list.
      // https://en.wikipedia.org/wiki/Ppc64
      "power3", "power4", "power5", "power5+", "power6", "power6x",
      "power7", "rs64",
      // e series SoC chips. x00 are 32-bit, x50 are 64-bit. See e.g.
      // https://en.wikipedia.org/wiki/PowerPC_e6500
      "e500mc64", "e5500", "e6500",
      // https://en.wikipedia.org/wiki/IBM_A2
      "a2",
    }},
    // The latest Power processors are little endian.
    {"powerpc64le", {"powerpc64le", "power8"}},
    // There are two MIPS architecture series. The 'old' one comprises
    // MIPS I - MIPS V (where MIPS I and MIPS II are 32-bit
    // architectures, and the III, IV and V are 64-bit). The 'new'
    // architecture series comprises MIPS32 and MIPS64. Source: [0].
    //
    // CPROVER's names for these are in configt::this_architecture(),
    // in particular note the preprocessor variable names. MIPS
    // processors can run in little-endian or big-endian mode; [1]
    // gives more information on particular processors. Particular
    // processors and their architectures are at [2]. This means that
    // we cannot use the processor flags alone to decide which CPROVER
    // name to use; we also need to check for the -EB or -EL flags to
    // decide whether little- or big-endian code should be generated.
    // Therefore, the keys in this part of the map don't directly map
    // to CPROVER architectures.
    //
    // [0] https://en.wikipedia.org/wiki/MIPS_architecture
    // [1] https://www.debian.org/ports/mips/
    // [2] https://en.wikipedia.org/wiki/List_of_MIPS_architecture_processors
    // NOLINTNEXTLINE(whitespace/braces)
    {"mips64n", {
      "loongson2e", "loongson2f", "loongson3a", "mips64", "mips64r2",
      "mips64r3", "mips64r5", "mips64r6 4kc", "5kc", "5kf", "20kc",
      "octeon", "octeon+", "octeon2", "octeon3", "sb1", "vr4100",
      "vr4111", "vr4120", "vr4130", "vr4300", "vr5000", "vr5400",
      "vr5500", "sr71000", "xlp",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"mips32n", {
      "mips32", "mips32r2", "mips32r3", "mips32r5", "mips32r6",
      // https://www.imgtec.com/mips/classic/
      "4km", "4kp", "4ksc", "4kec", "4kem", "4kep", "4ksd", "24kc",
      "24kf2_1", "24kf1_1", "24kec", "24kef2_1", "24kef1_1", "34kc",
      "34kf2_1", "34kf1_1", "34kn", "74kc", "74kf2_1", "74kf1_1",
      "74kf3_2", "1004kc", "1004kf2_1", "1004kf1_1", "m4k", "m14k",
      "m14kc", "m14ke", "m14kec",
      // https://en.wikipedia.org/wiki/List_of_MIPS_architecture_processors
      "p5600", "xlr",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"mips32o", {
      "mips1", "mips2", "r2000", "r3000",
      "r6000", // Not a mistake, r4000 came out _after_ this
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"mips64o", {
      "mips3", "mips4", "r4000", "r4400", "r4600", "r4650", "r4700",
      "r8000", "rm7000", "rm9000", "r10000", "r12000", "r14000",
      "r16000",
    }},
    // These are IBM mainframes. s390 is 32-bit; s390x is 64-bit [0].
    // Search that page for s390x and note that 32-bit refers to
    // everything "prior to 2000's z900 model".  The list of model
    // numbers is at [1].
    // [0] https://en.wikipedia.org/wiki/Linux_on_z_Systems
    // [1] https://en.wikipedia.org/wiki/IBM_System_z
    // NOLINTNEXTLINE(whitespace/braces)
    {"s390", {
      "z900", "z990", "g5", "g6",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"s390x", {
      "z9-109", "z9-ec", "z10", "z196", "zEC12", "z13"
    }},
    // SPARC
    // In the "Implementations" table of [0], everything with an arch
    // version up to V8 is 32-bit. V9 and onward are 64-bit.
    // [0] https://en.wikipedia.org/wiki/SPARC
    // NOLINTNEXTLINE(whitespace/braces)
    {"sparc", {
      "v7", "v8", "leon", "leon3", "leon3v7", "cypress", "supersparc",
      "hypersparc", "sparclite", "f930", "f934", "sparclite86x",
      "tsc701",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"sparc64", {
      "v9", "ultrasparc", "ultrasparc3", "niagara", "niagara2",
      "niagara3", "niagara4",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"ia64", {
      "itanium", "itanium1", "merced", "itanium2", "mckinley"
    }}, // NOLINTNEXTLINE(whitespace/braces)
    // x86 and x86_64. See
    // https://en.wikipedia.org/wiki/List_of_AMD_microprocessors
    // https://en.wikipedia.org/wiki/List_of_Intel_microprocessors
    {"i386", {
      // Intel generic
      "i386", "i486", "i586", "i686",
      // AMD
      "k6", "k6-2", "k6-3", "athlon" "athlon-tbird", "athlon-4",
      "athlon-xp", "athlon-mp",
      // Everything called "pentium" by GCC is 32 bits; the only 64-bit
      // Pentium flag recognized by GCC is "nocona".
      "pentium", "pentium-mmx", "pentiumpro" "pentium2", "pentium3",
      "pentium3m", "pentium-m" "pentium4", "pentium4m", "prescott",
      // Misc
      "winchip-c6", "winchip2", "c3", "c3-2", "geode",
    }}, // NOLINTNEXTLINE(whitespace/braces)
    {"x86_64", {
      // Intel
      "nocona", "core2", "nehalem" "westmere", "sandybridge", "knl",
      "ivybridge", "haswell", "broadwell" "bonnell", "silvermont",
      // AMD generic
      "k8", "k8-sse3", "opteron", "athlon64", "athlon-fx",
      "opteron-sse3" "athlon64-sse3", "amdfam10", "barcelona",
      // AMD "bulldozer" (high power, family 15h)
      "bdver1", "bdver2" "bdver3", "bdver4",
      // AMD "bobcat" (low power, family 14h)
      "btver1", "btver2",
    }},
  })
{
}

bool gcc_modet::needs_preprocessing(const std::string &file)
{
  if(has_suffix(file, ".c") ||
     has_suffix(file, ".cc") ||
     has_suffix(file, ".cp") ||
     has_suffix(file, ".cpp") ||
     has_suffix(file, ".CPP") ||
     has_suffix(file, ".c++") ||
     has_suffix(file, ".C"))
    return true;
  else
    return false;
}

/// does it.
int gcc_modet::doit()
{
  if(cmdline.isset('?') ||
     cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  native_tool_name=
    compiler_name(cmdline, base_name);

  auto default_verbosity = (cmdline.isset("Wall") || cmdline.isset("Wextra")) ?
    messaget::M_WARNING : messaget::M_ERROR;
  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), default_verbosity, gcc_message_handler);

  bool act_as_bcc=
    base_name=="bcc" ||
    base_name.find("goto-bcc")!=std::string::npos;

  // if we are gcc or bcc, then get the version number
  gcc_version.get(native_tool_name);

  if((cmdline.isset('v') && cmdline.have_infile_arg()) ||
     (cmdline.isset("version") && !produce_hybrid_binary))
  {
    // "-v" a) prints the version and b) increases verbosity.
    // Compilation continues, don't exit!

    if(act_as_bcc)
      std::cout << "bcc: version " << gcc_version << " (goto-cc "
                << CBMC_VERSION << ")\n";
    else
    {
      if(gcc_version.flavor == gcc_versiont::flavort::CLANG)
        std::cout << "clang version " << gcc_version << " (goto-cc "
                  << CBMC_VERSION << ")\n";
      else
        std::cout << "gcc (goto-cc " << CBMC_VERSION << ") " << gcc_version
                  << '\n';
    }
  }

  compilet compiler(cmdline,
                    gcc_message_handler,
                    cmdline.isset("Werror") &&
                    !cmdline.isset("Wno-error"));

  if(cmdline.isset("version"))
  {
    if(produce_hybrid_binary)
      return run_gcc(compiler);

    std::cout
      << '\n'
      << "Copyright (C) 2006-2018 Daniel Kroening, Christoph Wintersteiger\n"
      << "CBMC version: " << CBMC_VERSION << '\n'
      << "Architecture: " << config.this_architecture() << '\n'
      << "OS: " << config.this_operating_system() << '\n';

    if(gcc_version.flavor == gcc_versiont::flavort::CLANG)
      std::cout << "clang: " << gcc_version << '\n';
    else
      std::cout << "gcc: " << gcc_version << '\n';

    return EX_OK; // Exit!
  }

  if(
    cmdline.isset("dumpmachine") || cmdline.isset("dumpspecs") ||
    cmdline.isset("dumpversion") || cmdline.isset("print-sysroot") ||
    cmdline.isset("print-sysroot-headers-suffix"))
  {
    if(produce_hybrid_binary)
      return run_gcc(compiler);

    // GCC will only print one of these, even when multiple arguments are
    // passed, so we do the same
    if(cmdline.isset("dumpmachine"))
      std::cout << config.this_architecture() << '\n';
    else if(cmdline.isset("dumpversion"))
      std::cout << gcc_version << '\n';

    // we don't have any meaningful output for the other options, and GCC
    // doesn't necessarily produce non-empty output either

    return EX_OK;
  }

  messaget log{gcc_message_handler};

  if(act_as_bcc)
  {
    if(produce_hybrid_binary)
      log.debug() << "BCC mode (hybrid)" << messaget::eom;
    else
      log.debug() << "BCC mode" << messaget::eom;
  }
  else
  {
    if(produce_hybrid_binary)
      log.debug() << "GCC mode (hybrid)" << messaget::eom;
    else
      log.debug() << "GCC mode" << messaget::eom;
  }

  // model validation
  compiler.validate_goto_model = cmdline.isset("validate-goto-model");

  // determine actions to be undertaken
  if(cmdline.isset('S'))
    compiler.mode=compilet::ASSEMBLE_ONLY;
  else if(cmdline.isset('c'))
    compiler.mode=compilet::COMPILE_ONLY;
  else if(cmdline.isset('E'))
    compiler.mode=compilet::PREPROCESS_ONLY;
  else if(cmdline.isset("shared") ||
          cmdline.isset('r')) // really not well documented
    compiler.mode=compilet::COMPILE_LINK;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;

  // In gcc mode, we have just pass on to gcc to handle the following:
  // * if -M or -MM is given, we do dependencies only
  // * preprocessing (-E)
  // * no input files given

  if(cmdline.isset('M') ||
     cmdline.isset("MM") ||
     cmdline.isset('E') ||
     !cmdline.have_infile_arg())
    return run_gcc(compiler); // exit!

  // get configuration
  config.set(cmdline);

  // Intel-specific
  // in GCC, m16 is 32-bit (!), as documented here:
  // https://gcc.gnu.org/bugzilla/show_bug.cgi?id=59672
  if(cmdline.isset("m16") ||
     cmdline.isset("m32") || cmdline.isset("mx32"))
  {
    config.ansi_c.arch="i386";
    config.ansi_c.set_arch_spec_i386();
  }
  else if(cmdline.isset("m64"))
  {
    config.ansi_c.arch="x86_64";
    config.ansi_c.set_arch_spec_x86_64();
  }

  // ARM-specific
  if(cmdline.isset("mbig-endian") || cmdline.isset("mbig"))
    config.ansi_c.endianness=configt::ansi_ct::endiannesst::IS_BIG_ENDIAN;
  else if(cmdline.isset("little-endian") || cmdline.isset("mlittle"))
    config.ansi_c.endianness=configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;

  if(cmdline.isset("mthumb") || cmdline.isset("mthumb-interwork"))
    config.ansi_c.set_arch_spec_arm("armhf");

  // -mcpu sets both the arch and tune, but should only be used if
  // neither -march nor -mtune are passed on the command line.
  std::string target_cpu=
    cmdline.isset("march") ? cmdline.get_value("march") :
    cmdline.isset("mtune") ? cmdline.get_value("mtune") :
    cmdline.isset("mcpu")  ? cmdline.get_value("mcpu")  : "";

  if(!target_cpu.empty())
  {
    // Work out what CPROVER architecture we should target.
    for(auto &pair : arch_map)
      for(auto &processor : pair.second)
        if(processor==target_cpu)
        {
          if(pair.first.find("mips")==std::string::npos)
            config.set_arch(pair.first);
          else
          {
            // Targeting a MIPS processor. MIPS is special; we also need
            // to know the endianness. -EB (big-endian) is the default.
            if(cmdline.isset("EL"))
            {
              if(pair.first=="mips32o")
                config.set_arch("mipsel");
              else if(pair.first=="mips32n")
                config.set_arch("mipsn32el");
              else
                config.set_arch("mips64el");
            }
            else
            {
              if(pair.first=="mips32o")
                config.set_arch("mips");
              else if(pair.first=="mips32n")
                config.set_arch("mipsn32");
              else
                config.set_arch("mips64");
            }
          }
        }
  }

  // -fshort-wchar makes wchar_t "short unsigned int"
  if(cmdline.isset("fshort-wchar"))
  {
    config.ansi_c.wchar_t_width=config.ansi_c.short_int_width;
    config.ansi_c.wchar_t_is_unsigned=true;
  }

  // -fsingle-precision-constant makes floating-point constants "float"
  // instead of double
  if(cmdline.isset("-fsingle-precision-constant"))
    config.ansi_c.single_precision_constant=true;

  // -fshort-double makes double the same as float
  if(cmdline.isset("fshort-double"))
    config.ansi_c.double_width=config.ansi_c.single_width;

  // configure version-specific gcc settings
  configure_gcc(gcc_version);

  switch(compiler.mode)
  {
  case compilet::LINK_LIBRARY:
    log.debug() << "Linking a library only" << messaget::eom;
    break;
  case compilet::COMPILE_ONLY:
    log.debug() << "Compiling only" << messaget::eom;
    break;
  case compilet::ASSEMBLE_ONLY:
    log.debug() << "Assembling only" << messaget::eom;
    break;
  case compilet::PREPROCESS_ONLY:
    log.debug() << "Preprocessing only" << messaget::eom;
    break;
  case compilet::COMPILE_LINK:
    log.debug() << "Compiling and linking a library" << messaget::eom;
    break;
  case compilet::COMPILE_LINK_EXECUTABLE:
    log.debug() << "Compiling and linking an executable" << messaget::eom;
    break;
  }

  if(cmdline.isset("i386-win32") ||
     cmdline.isset("winx64"))
  {
    // We may wish to reconsider the below.
    config.ansi_c.mode=configt::ansi_ct::flavourt::VISUAL_STUDIO;
    log.debug() << "Enabling Visual Studio syntax" << messaget::eom;
  }
  else
  {
    if(gcc_version.flavor == gcc_versiont::flavort::CLANG)
      config.ansi_c.mode = configt::ansi_ct::flavourt::CLANG;
    else
      config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  }

  if(compiler.mode==compilet::ASSEMBLE_ONLY)
    compiler.object_file_extension="s";
  else
    compiler.object_file_extension="o";

  if(cmdline.isset("std"))
  {
    std::string std_string=cmdline.get_value("std");

    if(std_string=="gnu89" || std_string=="c89")
      config.ansi_c.set_c89();

    if(std_string=="gnu99" || std_string=="c99" || std_string=="iso9899:1999" ||
       std_string=="gnu9x" || std_string=="c9x" || std_string=="iso9899:199x")
      config.ansi_c.set_c99();

    if(std_string=="gnu11" || std_string=="c11" ||
       std_string=="gnu1x" || std_string=="c1x")
      config.ansi_c.set_c11();

    if(std_string=="c++11" || std_string=="c++1x" ||
       std_string=="gnu++11" || std_string=="gnu++1x" ||
       std_string=="c++1y" ||
       std_string=="gnu++1y")
      config.cpp.set_cpp11();

    if(std_string=="gnu++14" || std_string=="c++14")
      config.cpp.set_cpp14();

    if(std_string == "gnu++17" || std_string == "c++17")
      config.cpp.set_cpp17();
  }
  else
  {
    config.ansi_c.c_standard = gcc_version.default_c_standard;
    config.cpp.cpp_standard = gcc_version.default_cxx_standard;
  }

  // gcc's default is 32 bits for wchar_t
  if(cmdline.isset("short-wchar"))
    config.ansi_c.wchar_t_width=16;

  // gcc's default is 64 bits for double
  if(cmdline.isset("short-double"))
    config.ansi_c.double_width=32;

  // gcc's default is signed chars on most architectures
  if(cmdline.isset("funsigned-char"))
    config.ansi_c.char_is_unsigned=true;

  if(cmdline.isset("fsigned-char"))
    config.ansi_c.char_is_unsigned=false;

  if(cmdline.isset('U'))
    config.ansi_c.undefines=cmdline.get_values('U');

  if(cmdline.isset("undef"))
    config.ansi_c.preprocessor_options.push_back("-undef");

  if(cmdline.isset("nostdinc"))
    config.ansi_c.preprocessor_options.push_back("-nostdinc");

  if(cmdline.isset('L'))
    compiler.library_paths=cmdline.get_values('L');
    // Don't add the system paths!

  if(cmdline.isset('l'))
    compiler.libraries=cmdline.get_values('l');

  if(cmdline.isset("static"))
    compiler.libraries.push_back("c");

  if(cmdline.isset("pthread"))
    compiler.libraries.push_back("pthread");

  if(cmdline.isset('o'))
  {
    // given gcc -o file1 -o file2,
    // gcc will output to file2, not file1
    compiler.output_file_object=cmdline.get_values('o').back();
    compiler.output_file_executable=cmdline.get_values('o').back();
  }
  else
  {
    compiler.output_file_object.clear();
    compiler.output_file_executable="a.out";
  }

  // We now iterate over any input files

  std::vector<temp_dirt> temp_dirs;

  {
    std::string language;

    for(goto_cc_cmdlinet::parsed_argvt::iterator
        arg_it=cmdline.parsed_argv.begin();
        arg_it!=cmdline.parsed_argv.end();
        arg_it++)
    {
      if(arg_it->is_infile_name)
      {
        // do any preprocessing needed

        if(language=="cpp-output" || language=="c++-cpp-output")
        {
          compiler.add_input_file(arg_it->arg);
        }
        else if(
          language == "c" || language == "c++" ||
          (language.empty() && needs_preprocessing(arg_it->arg)))
        {
          std::string new_suffix;

          if(language=="c")
            new_suffix=".i";
          else if(language=="c++")
            new_suffix=".ii";
          else
            new_suffix=has_suffix(arg_it->arg, ".c")?".i":".ii";

          std::string new_name=
            get_base_name(arg_it->arg, true)+new_suffix;

          temp_dirs.emplace_back("goto-cc-XXXXXX");
          std::string dest = temp_dirs.back()(new_name);

          int exit_code=
            preprocess(language, arg_it->arg, dest, act_as_bcc);

          if(exit_code!=0)
          {
            log.error() << "preprocessing has failed" << messaget::eom;
            return exit_code;
          }

          compiler.add_input_file(dest);
        }
        else
          compiler.add_input_file(arg_it->arg);
      }
      else if(arg_it->arg=="-x")
      {
        arg_it++;
        if(arg_it!=cmdline.parsed_argv.end())
        {
          language=arg_it->arg;
          if(language=="none")
            language.clear();
        }
      }
      else if(has_prefix(arg_it->arg, "-x"))
      {
        language=std::string(arg_it->arg, 2, std::string::npos);
        if(language=="none")
          language.clear();
      }
    }
  }

  if(
    cmdline.isset('o') && cmdline.isset('c') &&
    compiler.source_files.size() >= 2)
  {
    log.error() << "cannot specify -o with -c with multiple files"
                << messaget::eom;
    return 1; // to match gcc's behaviour
  }

  // Revert to gcc in case there is no source to compile
  // and no binary to link.

  if(compiler.source_files.empty() &&
     compiler.object_files.empty())
    return run_gcc(compiler); // exit!

  if(compiler.mode==compilet::ASSEMBLE_ONLY)
    return asm_output(act_as_bcc, compiler.source_files, compiler);

  // do all the rest
  if(compiler.doit())
    return 1; // GCC exit code for all kinds of errors

  // We can generate hybrid ELF and Mach-O binaries
  // containing both executable machine code and the goto-binary.
  if(produce_hybrid_binary && !act_as_bcc)
    return gcc_hybrid_binary(compiler);

  return EX_OK;
}

/// call gcc for preprocessing
int gcc_modet::preprocess(
  const std::string &language,
  const std::string &src,
  const std::string &dest,
  bool act_as_bcc)
{
  // build new argv
  std::vector<std::string> new_argv;

  new_argv.reserve(cmdline.parsed_argv.size());

  bool skip_next=false;

  for(goto_cc_cmdlinet::parsed_argvt::const_iterator
      it=cmdline.parsed_argv.begin();
      it!=cmdline.parsed_argv.end();
      it++)
  {
    if(skip_next)
    {
      // skip
      skip_next=false;
    }
    else if(it->is_infile_name)
    {
      // skip
    }
    else if(it->arg=="-c" || it->arg=="-E" || it->arg=="-S")
    {
      // skip
    }
    else if(it->arg=="-o")
    {
      skip_next=true;
    }
    else if(has_prefix(it->arg, "-o"))
    {
      // ignore
    }
    else
      new_argv.push_back(it->arg);
  }

  // We just want to preprocess.
  new_argv.push_back("-E");

  // destination file
  std::string stdout_file;
  if(act_as_bcc)
    stdout_file=dest;
  else
  {
    new_argv.push_back("-o");
    new_argv.push_back(dest);
  }

  // language, if given
  if(!language.empty())
  {
    new_argv.push_back("-x");
    new_argv.push_back(language);
  }

  // source file
  new_argv.push_back(src);

  // overwrite argv[0]
  INVARIANT(new_argv.size()>=1, "No program name in argv");
  new_argv[0]=native_tool_name.c_str();

  messaget log{gcc_message_handler};
  log.debug() << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    log.debug() << " " << new_argv[i];
  log.debug() << messaget::eom;

  return run(new_argv[0], new_argv, cmdline.stdin_file, stdout_file, "");
}

int gcc_modet::run_gcc(const compilet &compiler)
{
  PRECONDITION(!cmdline.parsed_argv.empty());

  // build new argv
  std::vector<std::string> new_argv;
  new_argv.reserve(cmdline.parsed_argv.size());
  for(const auto &a : cmdline.parsed_argv)
    new_argv.push_back(a.arg);

  if(compiler.wrote_object_files())
  {
    // Undefine all __CPROVER macros for the system compiler
    std::map<irep_idt, std::size_t> arities;
    compiler.cprover_macro_arities(arities);
    for(const auto &pair : arities)
    {
      std::ostringstream addition;
      addition << "-D" << id2string(pair.first) << "(";
      std::vector<char> params(pair.second);
      std::iota(params.begin(), params.end(), 'a');
      for(std::vector<char>::iterator it=params.begin(); it!=params.end(); ++it)
      {
        addition << *it;
        if(it+1!=params.end())
          addition << ",";
      }
      addition << ")= ";
      new_argv.push_back(addition.str());
    }
  }

  // overwrite argv[0]
  new_argv[0]=native_tool_name;

  messaget log{gcc_message_handler};
  log.debug() << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    log.debug() << " " << new_argv[i];
  log.debug() << messaget::eom;

  return run(new_argv[0], new_argv, cmdline.stdin_file, "", "");
}

int gcc_modet::gcc_hybrid_binary(compilet &compiler)
{
  {
    bool have_files=false;

    for(goto_cc_cmdlinet::parsed_argvt::const_iterator
        it=cmdline.parsed_argv.begin();
        it!=cmdline.parsed_argv.end();
        it++)
      if(it->is_infile_name)
        have_files=true;

    if(!have_files)
      return EX_OK;
  }

  std::list<std::string> output_files;

  if(cmdline.isset('c'))
  {
    if(cmdline.isset('o'))
    {
      // there should be only one input file
      output_files.push_back(cmdline.get_value('o'));
    }
    else
    {
      for(goto_cc_cmdlinet::parsed_argvt::const_iterator
          i_it=cmdline.parsed_argv.begin();
          i_it!=cmdline.parsed_argv.end();
          i_it++)
        if(i_it->is_infile_name &&
           needs_preprocessing(i_it->arg))
          output_files.push_back(get_base_name(i_it->arg, true)+".o");
    }
  }
  else
  {
    // -c is not given
    if(cmdline.isset('o'))
      output_files.push_back(cmdline.get_value('o'));
    else
      output_files.push_back("a.out");
  }

  if(output_files.empty() ||
     (output_files.size()==1 &&
      output_files.front()=="/dev/null"))
    return run_gcc(compiler);

  messaget log{gcc_message_handler};
  log.debug() << "Running " << native_tool_name << " to generate hybrid binary"
              << messaget::eom;

  // save the goto-cc output files
  std::list<std::string> goto_binaries;
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    std::string bin_name=*it+goto_binary_tmp_suffix;

    try
    {
      file_rename(*it, bin_name);
    }
    catch(const cprover_exception_baset &e)
    {
      log.error() << "Rename failed: " << e.what() << messaget::eom;
      return 1;
    }

    goto_binaries.push_back(bin_name);
  }

  int result=run_gcc(compiler);

  if(result==0 &&
     cmdline.isset('T') &&
     goto_binaries.size()==1 &&
     output_files.size()==1)
  {
    linker_script_merget ls_merge(
      output_files.front(),
      goto_binaries.front(),
      cmdline,
      gcc_message_handler);
    result=ls_merge.add_linker_script_definitions();
  }

  std::string native_tool;

  if(has_suffix(linker_name(cmdline, base_name), "-ld"))
    native_tool=linker_name(cmdline, base_name);
  else if(has_suffix(compiler_name(cmdline, base_name), "-gcc"))
    native_tool=compiler_name(cmdline, base_name);

  // merge output from gcc with goto-binaries
  // using objcopy, or do cleanup if an earlier call failed
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    std::string goto_binary=*it+goto_binary_tmp_suffix;

    if(result==0)
      result = hybrid_binary(
        native_tool,
        goto_binary,
        *it,
        compiler.mode == compilet::COMPILE_LINK_EXECUTABLE,
        gcc_message_handler);
  }

  return result;
}

int gcc_modet::asm_output(
  bool act_as_bcc,
  const std::list<std::string> &preprocessed_source_files,
  const compilet &compiler)
{
  {
    bool have_files=false;

    for(goto_cc_cmdlinet::parsed_argvt::const_iterator
        it=cmdline.parsed_argv.begin();
        it!=cmdline.parsed_argv.end();
        it++)
      if(it->is_infile_name)
        have_files=true;

    if(!have_files)
      return EX_OK;
  }

  messaget log{gcc_message_handler};

  if(produce_hybrid_binary)
  {
    log.debug() << "Running " << native_tool_name
                << " to generate native asm output" << messaget::eom;

    int result=run_gcc(compiler);
    if(result!=0)
      // native tool failed
      return result;
  }

  std::map<std::string, std::string> output_files;

  if(cmdline.isset('o'))
  {
    // GCC --combine supports more than one source file
    for(const auto &s : preprocessed_source_files)
      output_files.insert(std::make_pair(s, cmdline.get_value('o')));
  }
  else
  {
    for(const std::string &s : preprocessed_source_files)
      output_files.insert(
        std::make_pair(s, get_base_name(s, true)+".s"));
  }

  if(output_files.empty() ||
     (output_files.size()==1 &&
      output_files.begin()->second=="/dev/null"))
    return EX_OK;

  log.debug() << "Appending preprocessed sources to generate hybrid asm output"
              << messaget::eom;

  for(const auto &so : output_files)
  {
    std::ifstream is(so.first);
    if(!is.is_open())
    {
      log.error() << "Failed to open input source " << so.first
                  << messaget::eom;
      return 1;
    }

    std::ofstream os(so.second, std::ios::app);
    if(!os.is_open())
    {
      log.error() << "Failed to open output file " << so.second
                  << messaget::eom;
      return 1;
    }

    const char comment=act_as_bcc ? ':' : '#';

    os << comment << comment << " GOTO-CC" << '\n';

    std::string line;

    while(std::getline(is, line))
    {
      os << comment << comment << line << '\n';
    }
  }

  return EX_OK;
}

/// display command line help
void gcc_modet::help_mode()
{
  std::cout << "goto-cc understands the options of "
            << "gcc plus the following.\n\n";
}
