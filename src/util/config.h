/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_CONFIG_H
#define CPROVER_UTIL_CONFIG_H

#include "ieee_float.h"
#include "irep.h"

#include <list>
#include <optional>

class cmdlinet;
class symbol_table_baset;

// Configt is the one place beyond *_parse_options where options are ... parsed.
// Options that are handled by configt are documented here.

#define OPT_CONFIG_C_CPP                                                       \
  "D:I:(include)(function)"                                                    \
  "(c89)(c99)(c11)(cpp98)(cpp03)(cpp11)"                                       \
  "(unsigned-char)"                                                            \
  "(round-to-even)(round-to-nearest)"                                          \
  "(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)"                     \
  "(no-library)"

#define HELP_CONFIG_C_CPP                                                      \
  " {y-I} {upath} \t set include path (C/C++)\n"                               \
  " {y--include} {ufile} \t set include file (C/C++)\n"                        \
  " {y-D} {umacro} \t define preprocessor macro (C/C++)\n"                     \
  " {y--c89}, {y--c99}, {y--c11} \t "                                          \
  "set C language standard (default: " +                                       \
    std::string(                                                               \
      configt::ansi_ct::default_c_standard() ==                                \
          configt::ansi_ct::c_standardt::C89                                   \
        ? "c89"                                                                \
      : configt::ansi_ct::default_c_standard() ==                              \
          configt::ansi_ct::c_standardt::C99                                   \
        ? "c99"                                                                \
      : configt::ansi_ct::default_c_standard() ==                              \
          configt::ansi_ct::c_standardt::C11                                   \
        ? "c11"                                                                \
        : "") +                                                                \
    ")\n"                                                                      \
    " {y--cpp98}, {y--cpp03}, {y--cpp11} \t "                                  \
    "set C++ language standard (default: " +                                   \
    std::string(                                                               \
      configt::cppt::default_cpp_standard() ==                                 \
          configt::cppt::cpp_standardt::CPP98                                  \
        ? "cpp98"                                                              \
      : configt::cppt::default_cpp_standard() ==                               \
          configt::cppt::cpp_standardt::CPP03                                  \
        ? "cpp03"                                                              \
      : configt::cppt::default_cpp_standard() ==                               \
          configt::cppt::cpp_standardt::CPP11                                  \
        ? "cpp11"                                                              \
        : "") +                                                                \
    ")\n"                                                                      \
    " {y--unsigned-char} \t make \"char\" unsigned by default\n"               \
    " {y--round-to-nearest}, {y--round-to-even} \t "                           \
    "rounding towards nearest even (default)\n"                                \
    " {y--round-to-plus-inf} \t rounding towards plus infinity\n"              \
    " {y--round-to-minus-inf} \t rounding towards minus infinity\n"            \
    " {y--round-to-zero} \t rounding towards zero\n"                           \
    " {y--no-library} \t disable built-in abstract C library\n"

#define OPT_CONFIG_LIBRARY                                                     \
  "(malloc-fail-assert)(malloc-fail-null)(malloc-may-fail)"                    \
  "(no-malloc-may-fail)"                                                       \
  "(string-abstraction)"

#define HELP_CONFIG_LIBRARY                                                    \
  " {y--malloc-may-fail} \t allow malloc calls to return a null pointer\n"     \
  " {y--no-malloc-may-fail} \t disable potential malloc failure\n"             \
  " {y--malloc-fail-assert} \t "                                               \
  "set malloc failure mode to assert-then-assume\n"                            \
  " {y--malloc-fail-null} \t set malloc failure mode to return null\n"         \
  " {y--string-abstraction} \t track C string lengths and zero-termination\n"

#define OPT_CONFIG_JAVA "(classpath)(cp)(main-class)"

#define OPT_CONFIG_PLATFORM                                                    \
  "(arch):(os):"                                                               \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)"                              \
  "(little-endian)(big-endian)"                                                \
  "(i386-linux)"                                                               \
  "(i386-win32)(win32)(winx64)"                                                \
  "(i386-macos)(ppc-macos)"                                                    \
  "(gcc)"

#define HELP_CONFIG_PLATFORM                                                   \
  " {y--arch} {uarch_name} \t "                                                \
  "set architecture (default: " +                                              \
    id2string(configt::this_architecture()) +                                  \
    ") to one of: {yalpha}, {yarm}, {yarm64}, {yarmel}, {yarmhf}, {yhppa}, "   \
    "{yi386}, {yia64}, {ymips}, {ymips64}, {ymips64el}, {ymipsel}, "           \
    "{ymipsn32}, "                                                             \
    "{ymipsn32el}, {ypowerpc}, {yppc64}, {yppc64le}, {yriscv64}, {ys390}, "    \
    "{ys390x}, {ysh4}, {ysparc}, {ysparc64}, {yv850}, {yx32}, {yx86_64}, or "  \
    "{ynone}\n"                                                                \
    " {y--os} {uos_name} \t "                                                  \
    "set operating system (default: " +                                        \
    id2string(configt::this_operating_system()) +                              \
    ") to one of: {yfreebsd}, {ylinux}, {ymacos}, {ynetbsd}, {yopenbsd}, "     \
    "{ysolaris}, {yhurd}, or {ywindows}\n"                                     \
    " {y--i386-linux}, {y--i386-win32}, {y--i386-macos}, {y--ppc-macos}, "     \
    "{y--win32}, {y--winx64} \t "                                              \
    "set architecture and operating system\n"                                  \
    " {y--LP64}, {y--ILP64}, {y--LLP64}, {y--ILP32}, {y--LP32} \t "            \
    "set width of int, long and pointers, but don't override default "         \
    "architecture and operating system\n"                                      \
    " {y--16}, {y--32}, {y--64} \t "                                           \
    "equivalent to {y--LP32}, {y--ILP32}, {y--LP64} (on Windows: "             \
    "{y--LLP64})\n"                                                            \
    " {y--little-endian} \t allow little-endian word-byte conversions\n"       \
    " {y--big-endian} \t allow big-endian word-byte conversions\n"             \
    " {y--gcc} \t use GCC as preprocessor\n"

#define OPT_CONFIG_BACKEND "(object-bits):"

#define HELP_CONFIG_BACKEND                                                    \
  " {y--object-bits} {un} \t number of bits used for object addresses\n"

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
    bool __float128_is_keyword;   // __float128 as a keyword (and not typedef)
    bool float16_type;            // _Float16 (Clang >= 15, GCC >= 12)
    bool bf16_type;               // __bf16 (Clang >= 15, GCC >= 13)
    bool fp16_type;               // __fp16 (GCC >= 4.5 on ARM, Clang >= 6)
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
    void set_arch_spec_loongarch64();
    void set_arch_spec_emscripten();

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
    bool malloc_may_fail = true;

    enum malloc_failure_modet
    {
      malloc_failure_mode_none = 0,
      malloc_failure_mode_return_null = 1,
      malloc_failure_mode_assert_then_assume = 2
    };

    malloc_failure_modet malloc_failure_mode = malloc_failure_mode_return_null;

    static const std::size_t default_object_bits = 8;

    /// Maximum value of argc, which is operating-systems dependent: Windows
    /// limits the number of characters accepte by CreateProcess, and Unix
    /// systems have sysconf(ARG_MAX).
    std::optional<mp_integer> max_argc;
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
  std::optional<std::string> main;

  void set_arch(const irep_idt &);

  void set_from_symbol_table(const symbol_table_baset &);

  bool set(const cmdlinet &cmdline);

  void set_object_bits_from_symbol_table(const symbol_table_baset &);
  std::string object_bits_info();
  mp_integer max_malloc_size() const;

  static irep_idt this_architecture();
  static irep_idt this_operating_system();

private:
  void set_classpath(const std::string &cp);
};

extern configt config;

#endif // CPROVER_UTIL_CONFIG_H
