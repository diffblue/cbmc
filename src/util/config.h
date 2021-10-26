/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_CONFIG_H
#define CPROVER_UTIL_CONFIG_H

#include <list>

#include "ieee_float.h"
#include "irep.h"
#include "optional.h"

class cmdlinet;
class symbol_tablet;

// Configt is the one place beyond *_parse_options where options are ... parsed.
// Options that are handled by configt are documented here.

// clang-format off
#define OPT_CONFIG_C_CPP                                                       \
  "D:I:(include)(function)"                                                    \
  "(c89)(c99)(c11)(cpp98)(cpp03)(cpp11)"                                       \
  "(unsigned-char)"                                                            \
  "(round-to-even)(round-to-nearest)"                                          \
  "(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)"                     \
  "(no-library)"                                                               \

#define HELP_CONFIG_C_CPP                                                      \
  " -I path                      set include path (C/C++)\n"                   \
  " -D macro                     define preprocessor macro (C/C++)\n"          \
  " --c89/99/11                  set C language standard (default: "           \
                                 << (configt::ansi_ct::default_c_standard()==  \
                                     configt::ansi_ct::c_standardt::C89?"c89": \
                                     configt::ansi_ct::default_c_standard()==  \
                                     configt::ansi_ct::c_standardt::C99?"c99": \
                                     configt::ansi_ct::default_c_standard()==  \
                          configt::ansi_ct::c_standardt::C11?"c11":"") << ")\n"\
  " --cpp98/03/11                set C++ language standard (default: "         \
                                 << (configt::cppt::default_cpp_standard()==   \
                                   configt::cppt::cpp_standardt::CPP98?"cpp98":\
                                     configt::cppt::default_cpp_standard()==   \
                                   configt::cppt::cpp_standardt::CPP03?"cpp03":\
                                     configt::cppt::default_cpp_standard()==   \
                       configt::cppt::cpp_standardt::CPP11?"cpp11":"") << ")\n"\
  " --unsigned-char              make \"char\" unsigned by default\n"          \
  " --round-to-nearest           rounding towards nearest even (default)\n"    \
  " --round-to-plus-inf          rounding towards plus infinity\n"             \
  " --round-to-minus-inf         rounding towards minus infinity\n"            \
  " --round-to-zero              rounding towards zero\n"                      \
  " --no-library                 disable built-in abstract C library\n"        \


#define OPT_CONFIG_LIBRARY                                                     \
  "(malloc-fail-assert)(malloc-fail-null)(malloc-may-fail)"                    \
  "(string-abstraction)"                                                       \

#define HELP_CONFIG_LIBRARY                                                    \
" --malloc-may-fail            allow malloc calls to return a null pointer\n"  \
" --malloc-fail-assert         set malloc failure mode to assert-then-assume\n"\
" --malloc-fail-null           set malloc failure mode to return null\n"       \


#define OPT_CONFIG_JAVA                                                        \
  "(classpath)(cp)(main-class)"                                                \


#define OPT_CONFIG_PLATFORM                                                    \
  "(arch):(os):"                                                               \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)"                              \
  "(little-endian)(big-endian)"                                                \
  "(i386-linux)"                                                               \
  "(i386-win32)(win32)(winx64)"                                                \
  "(i386-macos)(ppc-macos)"                                                    \
  "(gcc)"                                                                      \

#define HELP_CONFIG_PLATFORM \
  " --arch                       set architecture (default: "                  \
                                 << configt::this_architecture() << ")\n"      \
  " --os                         set operating system (default: "              \
                                 << configt::this_operating_system() << ")\n"  \
  " --16, --32, --64             set width of int\n"                           \
  " --LP64, --ILP64, --LLP64,\n"                                               \
  "   --ILP32, --LP32            set width of int, long and pointers\n"        \
  " --little-endian              allow little-endian word-byte conversions\n"  \
  " --big-endian                 allow big-endian word-byte conversions\n"     \
  " --gcc                        use GCC as preprocessor\n"                    \

#define OPT_CONFIG_BACKEND                                                     \
  "(object-bits):"                                                             \

#define HELP_CONFIG_BACKEND                                                    \
  " --object-bits n              number of bits used for object addresses\n"

// clang-format on

/*! \brief Globally accessible architectural configuration
*/
class configt
{
public:
  struct ansi_ct
  {
    // for ANSI-C
    std::size_t int_width;
    std::size_t long_int_width;
    std::size_t bool_width;
    std::size_t char_width;
    std::size_t short_int_width;
    std::size_t long_long_int_width;
    std::size_t pointer_width;
    std::size_t single_width;
    std::size_t double_width;
    std::size_t long_double_width;
    std::size_t wchar_t_width;

    // various language options
    bool char_is_unsigned, wchar_t_is_unsigned;
    bool for_has_scope;
    bool ts_18661_3_Floatn_types; // ISO/IEC TS 18661-3:2015
    bool gcc__float128_type;      // __float128, a gcc extension since 4.3/4.5
    bool single_precision_constant;
    enum class c_standardt
    {
      C89,
      C99,
      C11
    } c_standard;
    static c_standardt default_c_standard();

    void set_c89()
    {
      c_standard = c_standardt::C89;
      for_has_scope = false;
    }
    void set_c99()
    {
      c_standard = c_standardt::C99;
      for_has_scope = true;
    }
    void set_c11()
    {
      c_standard = c_standardt::C11;
      for_has_scope = true;
    }

    ieee_floatt::rounding_modet rounding_mode;

    void set_16();
    void set_32();
    void set_64();

    // http://www.unix.org/version2/whatsnew/lp64_wp.html
    void set_LP64();  // int=32, long=64, pointer=64
    void set_ILP64(); // int=64, long=64, pointer=64
    void set_LLP64(); // int=32, long=32, pointer=64
    void set_ILP32(); // int=32, long=32, pointer=32
    void set_LP32();  // int=16, long=32, pointer=32

    // minimum alignment (in structs) measured in bytes
    std::size_t alignment;

    // maximum minimum size of the operands for a machine
    // instruction (in bytes)
    std::size_t memory_operand_size;

    enum class endiannesst
    {
      NO_ENDIANNESS,
      IS_LITTLE_ENDIAN,
      IS_BIG_ENDIAN
    };
    endiannesst endianness;

    enum class ost
    {
      NO_OS,
      OS_LINUX,
      OS_MACOS,
      OS_WIN
    };
    ost os;

    static std::string os_to_string(ost);
    static ost string_to_os(const std::string &);

    irep_idt arch;

    // architecture-specific integer value of null pointer constant
    bool NULL_is_zero;

    void set_arch_spec_i386();
    void set_arch_spec_x86_64();
    void set_arch_spec_power(const irep_idt &subarch);
    void set_arch_spec_arm(const irep_idt &subarch);
    void set_arch_spec_alpha();
    void set_arch_spec_mips(const irep_idt &subarch);
    void set_arch_spec_riscv64();
    void set_arch_spec_s390();
    void set_arch_spec_s390x();
    void set_arch_spec_sparc(const irep_idt &subarch);
    void set_arch_spec_ia64();
    void set_arch_spec_x32();
    void set_arch_spec_v850();
    void set_arch_spec_hppa();
    void set_arch_spec_sh4();

    enum class flavourt
    {
      NONE,
      ANSI,
      GCC,
      ARM,
      CLANG,
      VISUAL_STUDIO,
      CODEWARRIOR
    };
    flavourt mode; // the syntax of source files

    enum class preprocessort
    {
      NONE,
      GCC,
      CLANG,
      VISUAL_STUDIO,
      CODEWARRIOR,
      ARM
    };
    preprocessort preprocessor; // the preprocessor to use

    std::list<std::string> defines;
    std::list<std::string> undefines;
    std::list<std::string> preprocessor_options;
    std::list<std::string> include_paths;
    std::list<std::string> include_files;

    enum class libt
    {
      LIB_NONE,
      LIB_FULL
    };
    libt lib;

    bool string_abstraction;
    bool malloc_may_fail = false;

    enum malloc_failure_modet
    {
      malloc_failure_mode_none = 0,
      malloc_failure_mode_return_null = 1,
      malloc_failure_mode_assert_then_assume = 2
    };

    malloc_failure_modet malloc_failure_mode = malloc_failure_mode_none;

    static const std::size_t default_object_bits = 8;
  } ansi_c;

  struct cppt
  {
    enum class cpp_standardt
    {
      CPP98,
      CPP03,
      CPP11,
      CPP14,
      CPP17
    } cpp_standard;
    static cpp_standardt default_cpp_standard();

    void set_cpp98()
    {
      cpp_standard = cpp_standardt::CPP98;
    }
    void set_cpp03()
    {
      cpp_standard = cpp_standardt::CPP03;
    }
    void set_cpp11()
    {
      cpp_standard = cpp_standardt::CPP11;
    }
    void set_cpp14()
    {
      cpp_standard = cpp_standardt::CPP14;
    }
    void set_cpp17()
    {
      cpp_standard = cpp_standardt::CPP17;
    }

    static const std::size_t default_object_bits = 8;
  } cpp;

  struct verilogt
  {
    std::list<std::string> include_paths;
  } verilog;

  struct javat
  {
    typedef std::list<std::string> classpatht;
    classpatht classpath;
    irep_idt main_class;

    static const std::size_t default_object_bits = 16;
  } java;

  struct bv_encodingt
  {
    // number of bits to encode heap object addresses
    std::size_t object_bits = 8;
    bool is_object_bits_default = true;
  } bv_encoding;

  // this is the function to start executing
  optionalt<std::string> main;

  void set_arch(const irep_idt &);

  void set_from_symbol_table(const symbol_tablet &);

  bool set(const cmdlinet &cmdline);

  void set_object_bits_from_symbol_table(const symbol_tablet &);
  std::string object_bits_info();

  static irep_idt this_architecture();
  static irep_idt this_operating_system();

private:
  void set_classpath(const std::string &cp);
};

extern configt config;

#endif // CPROVER_UTIL_CONFIG_H
