/// \file
/// Equivalence tests between float_utilst (bit-blasting) and float_bvt
/// (expression-level) floating-point encodings.
///
/// For each operation, we build a SAT miter: run both encodings on the same
/// symbolic inputs and assert the outputs differ.  UNSAT proves equivalence
/// for all inputs; SAT yields a counterexample.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/floatbv/float_bv.h>
#include <solvers/floatbv/float_utils.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <iostream>

// ──────────────────────────────────────────────────────────────────
// Helpers
// ──────────────────────────────────────────────────────────────────

/// Floating-point specs used for CORE equivalence testing.
/// Tiny and small formats keep SAT solve times CI-friendly.
static const std::vector<ieee_float_spect> core_specs = {
  ieee_float_spect{3, 3}, // tiny:  7-bit
  ieee_float_spect{4, 5}, // small: 10-bit
};

/// Small x86-extended format (explicit integer bit, 8-bit total).
static ieee_float_spect x86_ext_tiny()
{
  ieee_float_spect s{3, 3};
  s.x86_extended = true;
  return s;
}

/// Single-precision spec for thorough (nightly) testing.
static const std::vector<ieee_float_spect> thorough_specs = {
  ieee_float_spect::single_precision(),
};

static std::string spec_name(const ieee_float_spect &spec)
{
  return "e=" + std::to_string(spec.e) + " f=" + std::to_string(spec.f);
}

/// Create a symbol_exprt, add it to the symbol table, and obtain its
/// SAT literals from boolbvt.  Returns the symbol and its bvt.
static std::pair<symbol_exprt, bvt> make_input(
  boolbvt &boolbv,
  symbol_tablet &symbol_table,
  const irep_idt &name,
  const typet &type)
{
  symbolt sym;
  sym.name = name;
  sym.type = type;
  sym.is_lvalue = true;
  symbol_table.add(sym);

  symbol_exprt se{name, type};
  bvt bv = boolbv.convert_bv(se);
  return {std::move(se), std::move(bv)};
}

/// Constrain a 32-bit rounding-mode bitvector to one of the five valid
/// IEEE 754 modes (0..4).
static void constrain_rounding_mode(boolbvt &boolbv, const symbol_exprt &rm_sym)
{
  const signedbv_typet t(32);
  boolbv.set_to_true(binary_relation_exprt(rm_sym, ID_ge, from_integer(0, t)));
  boolbv.set_to_true(binary_relation_exprt(rm_sym, ID_le, from_integer(4, t)));
}

/// Extract a float value from a SAT model for diagnostic output.
[[maybe_unused]] static ieee_float_valuet
extract_float(const propt &prop, const bvt &bv, const ieee_float_spect &spec)
{
  std::string bits;
  for(auto it = bv.rbegin(); it != bv.rend(); ++it)
    bits += prop.l_get(*it).is_true() ? '1' : '0';
  mp_integer int_val = binary2integer(bits, false);
  ieee_float_valuet v{spec};
  v.unpack(int_val);
  return v;
}

/// Assert that two bitvectors are not equal.
static literalt
miter_not_equal(propt &prop, bv_utilst &bv_utils, const bvt &a, const bvt &b)
{
  REQUIRE(a.size() == b.size());
  return !bv_utils.equal(a, b);
}

/// Check that the miter is UNSAT (encodings are equivalent).
/// On SAT, print a counterexample and FAIL.
static void check_unsat(
  satcheckt &satcheck,
  const std::string &op_name,
  const ieee_float_spect &spec,
  const bvt &a_bv = {},
  const bvt &b_bv = {},
  const bvt &rm_bv = {},
  const bvt &result_utils = {},
  const bvt &result_bv = {})
{
  const auto result = satcheck.prop_solve();
  if(result == satcheckt::resultt::P_SATISFIABLE)
  {
    if(!a_bv.empty())
    {
      auto a_val = extract_float(satcheck, a_bv, spec);
      std::cerr << "  a = " << a_val << " (0x"
                << integer2string(a_val.pack(), 16) << ")\n";
    }
    if(!b_bv.empty())
    {
      auto b_val = extract_float(satcheck, b_bv, spec);
      std::cerr << "  b = " << b_val << " (0x"
                << integer2string(b_val.pack(), 16) << ")\n";
    }
    if(!rm_bv.empty())
    {
      std::string rm_bits;
      for(auto it = rm_bv.rbegin(); it != rm_bv.rend(); ++it)
        rm_bits += satcheck.l_get(*it).is_true() ? '1' : '0';
      mp_integer rm_val = binary2integer(rm_bits, true);
      std::cerr << "  rm = " << rm_val << "\n";
    }
    if(!result_utils.empty())
    {
      auto ru = extract_float(satcheck, result_utils, spec);
      std::cerr << "  result_utils = " << ru << " (0x"
                << integer2string(ru.pack(), 16) << ")\n";
    }
    if(!result_bv.empty())
    {
      auto rb = extract_float(satcheck, result_bv, spec);
      std::cerr << "  result_bv    = " << rb << " (0x"
                << integer2string(rb.pack(), 16) << ")\n";
    }
    FAIL(
      "Equivalence violation for " << op_name << " with spec e=" << spec.e
                                   << " f=" << spec.f);
  }
  REQUIRE(result == satcheckt::resultt::P_UNSATISFIABLE);
}

/// Convenience: set up satcheck + boolbv + float_utilst for a given spec,
/// with two float inputs and a rounding mode.
struct test_environt
{
  satcheckt satcheck;
  symbol_tablet symbol_table;
  namespacet ns;
  boolbvt boolbv;
  bv_utilst bv_utils;
  float_utilst float_utils;

  ieee_float_spect spec;
  floatbv_typet float_type;

  symbol_exprt a_sym;
  bvt a_bv;
  symbol_exprt b_sym;
  bvt b_bv;
  symbol_exprt rm_sym;
  bvt rm_bv;

  explicit test_environt(const ieee_float_spect &_spec)
    : satcheck{null_message_handler},
      symbol_table{},
      ns{symbol_table},
      boolbv{ns, satcheck, null_message_handler},
      bv_utils{satcheck},
      float_utils{satcheck},
      spec{_spec},
      float_type{_spec.to_type()},
      a_sym{"", typet{}},
      b_sym{"", typet{}},
      rm_sym{"", typet{}}
  {
    float_utils.spec = spec;

    auto [as, ab] = make_input(boolbv, symbol_table, "a", float_type);
    a_sym = std::move(as);
    a_bv = std::move(ab);

    auto [bs, bb] = make_input(boolbv, symbol_table, "b", float_type);
    b_sym = std::move(bs);
    b_bv = std::move(bb);

    auto [rs, rb] = make_input(boolbv, symbol_table, "rm", signedbv_typet{32});
    rm_sym = std::move(rs);
    rm_bv = std::move(rb);

    constrain_rounding_mode(boolbv, rm_sym);
    float_utils.set_rounding_mode(rm_bv);

    // For x86 extended, exclude unnormals (exponent ≠ 0 AND integer bit = 0)
    // which are invalid/undefined values.
    if(spec.x86_extended)
    {
      auto exclude_unnormal = [&](const bvt &bv)
      {
        bvt exp = float_utils.get_exponent(bv);
        literalt exp_nonzero = bv_utils.is_not_zero(exp);
        literalt int_bit = bv[spec.f];
        satcheck.l_set_to_true(!satcheck.land(exp_nonzero, !int_bit));
      };
      exclude_unnormal(a_bv);
      exclude_unnormal(b_bv);
    }
  }

  std::pair<symbol_exprt, bvt> add_input_c()
  {
    return make_input(boolbv, symbol_table, "c", float_type);
  }

  void assert_miter_bv(const bvt &ru, const bvt &rb)
  {
    satcheck.l_set_to_true(miter_not_equal(satcheck, bv_utils, ru, rb));
  }

  void assert_miter_lit(literalt ru, literalt rb)
  {
    satcheck.l_set_to_true(satcheck.lxor(ru, rb));
  }

  bvt lower(const exprt &e)
  {
    return boolbv.convert_bv(e);
  }

  literalt lower_bool(const exprt &e)
  {
    return boolbv.convert(e);
  }

  void check(const std::string &op_name)
  {
    check_unsat(satcheck, op_name, spec, a_bv, b_bv, rm_bv);
  }

  void
  check_with_results(const std::string &op_name, const bvt &ru, const bvt &rb)
  {
    check_unsat(satcheck, op_name, spec, a_bv, b_bv, rm_bv, ru, rb);
  }
};

// ──────────────────────────────────────────────────────────────────
// Test body functions (called from both CORE and thorough tests)
// ──────────────────────────────────────────────────────────────────

static void test_abs(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.abs(env.a_bv);
  bvt rb = env.lower(float_bvt::abs(env.a_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check("abs");
}

static void test_negate(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.negate(env.a_bv);
  bvt rb = env.lower(float_bvt::negation(env.a_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check("negate");
}

static void test_add(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.add(env.a_bv, env.b_bv);
  bvt rb = env.lower(
    float_bvt{}.add_sub(false, env.a_sym, env.b_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check_with_results("add", ru, rb);
}

static void test_sub(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.sub(env.a_bv, env.b_bv);
  bvt rb = env.lower(
    float_bvt{}.add_sub(true, env.a_sym, env.b_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check("sub");
}

static void test_mul(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.mul(env.a_bv, env.b_bv);
  bvt rb = env.lower(float_bvt{}.mul(env.a_sym, env.b_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check_with_results("mul", ru, rb);
}

static void test_div(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.div(env.a_bv, env.b_bv);
  bvt rb = env.lower(float_bvt{}.div(env.a_sym, env.b_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check_with_results("div", ru, rb);
}

static void test_fma(const ieee_float_spect &spec)
{
  test_environt env{spec};
  auto [c_sym, c_bv] = env.add_input_c();
  bvt ru = env.float_utils.fma(env.a_bv, env.b_bv, c_bv);
  bvt rb =
    env.lower(float_bvt{}.fma(env.a_sym, env.b_sym, c_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check_with_results("fma", ru, rb);
}

static void test_relations(const ieee_float_spect &spec)
{
  using fu_rel = float_utilst::relt;
  using fb_rel = float_bvt::relt;

  struct rel_pair
  {
    fu_rel utils_rel;
    fb_rel bv_rel;
    const char *name;
  };

  const rel_pair rels[] = {
    {fu_rel::LT, fb_rel::LT, "LT"},
    {fu_rel::LE, fb_rel::LE, "LE"},
    {fu_rel::GT, fb_rel::GT, "GT"},
    {fu_rel::GE, fb_rel::GE, "GE"},
    {fu_rel::EQ, fb_rel::EQ, "EQ"},
  };

  for(const auto &rel : rels)
  {
    SECTION(rel.name)
    {
      test_environt env{spec};
      literalt ru = env.float_utils.relation(env.a_bv, rel.utils_rel, env.b_bv);
      literalt rb = env.lower_bool(
        float_bvt::relation(env.a_sym, rel.bv_rel, env.b_sym, spec));
      env.assert_miter_lit(ru, rb);
      env.check(std::string{"relation_"} + rel.name);
    }
  }
}

static void test_is_equal(const ieee_float_spect &spec)
{
  test_environt env{spec};
  literalt ru =
    env.float_utils.relation(env.a_bv, float_utilst::relt::EQ, env.b_bv);
  literalt rb = env.lower_bool(float_bvt::is_equal(env.a_sym, env.b_sym, spec));
  env.assert_miter_lit(ru, rb);
  env.check("is_equal");
}

static void test_isnan(const ieee_float_spect &spec)
{
  test_environt env{spec};
  literalt ru = env.float_utils.is_NaN(env.a_bv);
  literalt rb = env.lower_bool(float_bvt::isnan(env.a_sym, spec));
  env.assert_miter_lit(ru, rb);
  env.check("isnan");
}

static void test_isinf(const ieee_float_spect &spec)
{
  test_environt env{spec};
  literalt ru = env.float_utils.is_infinity(env.a_bv);
  literalt rb = env.lower_bool(float_bvt::isinf(env.a_sym, spec));
  env.assert_miter_lit(ru, rb);
  env.check("isinf");
}

static void test_isnormal(const ieee_float_spect &spec)
{
  test_environt env{spec};
  literalt ru = env.float_utils.is_normal(env.a_bv);
  literalt rb = env.lower_bool(float_bvt::isnormal(env.a_sym, spec));
  env.assert_miter_lit(ru, rb);
  env.check("isnormal");
}

static void test_is_zero(const ieee_float_spect &spec)
{
  test_environt env{spec};
  literalt ru = env.float_utils.is_zero(env.a_bv);
  literalt rb = env.lower_bool(float_bvt::is_zero(env.a_sym));
  env.assert_miter_lit(ru, rb);
  env.check("is_zero");
}

static void test_from_signed_integer(const ieee_float_spect &spec)
{
  test_environt env{spec};
  const signedbv_typet int_type(spec.width());
  auto [int_sym, int_bv] =
    make_input(env.boolbv, env.symbol_table, "int_in", int_type);
  bvt ru = env.float_utils.from_signed_integer(int_bv);
  bvt rb =
    env.lower(float_bvt{}.from_signed_integer(int_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check("from_signed_integer");
}

static void test_from_unsigned_integer(const ieee_float_spect &spec)
{
  test_environt env{spec};
  const unsignedbv_typet int_type(spec.width());
  auto [int_sym, int_bv] =
    make_input(env.boolbv, env.symbol_table, "uint_in", int_type);
  bvt ru = env.float_utils.from_unsigned_integer(int_bv);
  bvt rb =
    env.lower(float_bvt{}.from_unsigned_integer(int_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check("from_unsigned_integer");
}

static void test_to_signed_integer(const ieee_float_spect &spec)
{
  // float_utilst::to_integer requires round_to_zero as a precondition.
  satcheckt satcheck{null_message_handler};
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  boolbvt boolbv{ns, satcheck, null_message_handler};
  bv_utilst bv_utils{satcheck};

  const floatbv_typet float_type{spec.to_type()};
  auto [a_sym, a_bv] = make_input(boolbv, symbol_table, "a", float_type);

  float_utilst float_utils{satcheck};
  float_utils.spec = spec;
  float_utils.rounding_mode_bits.set(ieee_floatt::ROUND_TO_ZERO);

  const std::size_t dest_width = spec.width();
  bvt ru = float_utils.to_signed_integer(a_bv, dest_width);

  const exprt rm_zero =
    from_integer(ieee_floatt::ROUND_TO_ZERO, signedbv_typet{32});
  bvt rb = boolbv.convert_bv(
    float_bvt::to_signed_integer(a_sym, dest_width, rm_zero, spec));

  satcheck.l_set_to_true(miter_not_equal(satcheck, bv_utils, ru, rb));
  check_unsat(satcheck, "to_signed_integer", spec);
}

static void test_to_unsigned_integer(const ieee_float_spect &spec)
{
  satcheckt satcheck{null_message_handler};
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  boolbvt boolbv{ns, satcheck, null_message_handler};
  bv_utilst bv_utils{satcheck};

  const floatbv_typet float_type{spec.to_type()};
  auto [a_sym, a_bv] = make_input(boolbv, symbol_table, "a", float_type);

  float_utilst float_utils{satcheck};
  float_utils.spec = spec;
  float_utils.rounding_mode_bits.set(ieee_floatt::ROUND_TO_ZERO);

  const std::size_t dest_width = spec.width();
  bvt ru = float_utils.to_unsigned_integer(a_bv, dest_width);

  const exprt rm_zero =
    from_integer(ieee_floatt::ROUND_TO_ZERO, signedbv_typet{32});
  bvt rb = boolbv.convert_bv(
    float_bvt::to_unsigned_integer(a_sym, dest_width, rm_zero, spec));

  satcheck.l_set_to_true(miter_not_equal(satcheck, bv_utils, ru, rb));
  check_unsat(satcheck, "to_unsigned_integer", spec);
}

static void test_float_to_float_conversion(
  const ieee_float_spect &src_spec,
  const ieee_float_spect &dest_spec)
{
  test_environt env{src_spec};
  bvt ru = env.float_utils.conversion(env.a_bv, dest_spec);
  bvt rb = env.lower(
    float_bvt{}.conversion(env.a_sym, env.rm_sym, src_spec, dest_spec));
  env.assert_miter_bv(ru, rb);
  env.check("float_to_float_conversion");
}

// ──────────────────────────────────────────────────────────────────
// CORE tests (tiny, small, half — run in CI)
// ──────────────────────────────────────────────────────────────────

#define EQUIVALENCE_CORE_LOOP(test_fn)                                         \
  for(const auto &spec : core_specs)                                           \
  {                                                                            \
    SECTION(spec_name(spec))                                                   \
    {                                                                          \
      test_fn(spec);                                                           \
    }                                                                          \
  }

TEST_CASE(
  "float_bv_utils_equivalence_abs",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_abs);
}

TEST_CASE(
  "float_bv_utils_equivalence_negate",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_negate);
}

TEST_CASE(
  "float_bv_utils_equivalence_add",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_add);
}

TEST_CASE(
  "float_bv_utils_equivalence_sub",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_sub);
}

TEST_CASE(
  "float_bv_utils_equivalence_mul",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_mul);
}

TEST_CASE(
  "float_bv_utils_equivalence_div",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_div);
}

TEST_CASE(
  "float_bv_utils_equivalence_fma",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_fma);
}

TEST_CASE(
  "float_bv_utils_equivalence_relations",
  "[core][solvers][floatbv][equivalence]")
{
  for(const auto &spec : core_specs)
  {
    SECTION(spec_name(spec))
    {
      test_relations(spec);
    }
  }
}

TEST_CASE(
  "float_bv_utils_equivalence_is_equal",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_is_equal);
}

TEST_CASE(
  "float_bv_utils_equivalence_isnan",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_isnan);
}

TEST_CASE(
  "float_bv_utils_equivalence_isinf",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_isinf);
}

TEST_CASE(
  "float_bv_utils_equivalence_isnormal",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_isnormal);
}

TEST_CASE(
  "float_bv_utils_equivalence_is_zero",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_is_zero);
}

TEST_CASE(
  "float_bv_utils_equivalence_from_signed_integer",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_from_signed_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_from_unsigned_integer",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_from_unsigned_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_to_signed_integer",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_to_signed_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_to_unsigned_integer",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_to_unsigned_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_float_to_float_conversion",
  "[core][solvers][floatbv][equivalence]")
{
  for(const auto &src_spec : core_specs)
  {
    for(const auto &dest_spec : core_specs)
    {
      if(src_spec == dest_spec)
        continue;
      SECTION(spec_name(src_spec) + " -> " + spec_name(dest_spec))
      {
        test_float_to_float_conversion(src_spec, dest_spec);
      }
    }
  }
}

// ──────────────────────────────────────────────────────────────────
// Thorough tests (single precision — nightly/manual only)
// Hidden by default via [.] tag; run with:
//   build/bin/unit "[thorough]"
// ──────────────────────────────────────────────────────────────────

#define EQUIVALENCE_THOROUGH_LOOP(test_fn)                                     \
  for(const auto &spec : thorough_specs)                                       \
  {                                                                            \
    SECTION(spec_name(spec))                                                   \
    {                                                                          \
      test_fn(spec);                                                           \
    }                                                                          \
  }

TEST_CASE(
  "float_bv_utils_equivalence_abs_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_abs);
}

TEST_CASE(
  "float_bv_utils_equivalence_negate_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_negate);
}

TEST_CASE(
  "float_bv_utils_equivalence_add_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_add);
}

TEST_CASE(
  "float_bv_utils_equivalence_sub_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_sub);
}

TEST_CASE(
  "float_bv_utils_equivalence_mul_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_mul);
}

TEST_CASE(
  "float_bv_utils_equivalence_div_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_div);
}

TEST_CASE(
  "float_bv_utils_equivalence_fma_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_fma);
}

TEST_CASE(
  "float_bv_utils_equivalence_relations_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  for(const auto &spec : thorough_specs)
  {
    SECTION(spec_name(spec))
    {
      test_relations(spec);
    }
  }
}

TEST_CASE(
  "float_bv_utils_equivalence_is_equal_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_is_equal);
}

TEST_CASE(
  "float_bv_utils_equivalence_isnan_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_isnan);
}

TEST_CASE(
  "float_bv_utils_equivalence_isinf_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_isinf);
}

TEST_CASE(
  "float_bv_utils_equivalence_isnormal_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_isnormal);
}

TEST_CASE(
  "float_bv_utils_equivalence_is_zero_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_is_zero);
}

TEST_CASE(
  "float_bv_utils_equivalence_from_signed_integer_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_from_signed_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_from_unsigned_integer_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_from_unsigned_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_to_signed_integer_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_to_signed_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_to_unsigned_integer_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_to_unsigned_integer);
}

TEST_CASE(
  "float_bv_utils_equivalence_float_to_float_conversion_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  // Convert between single and each core spec.
  const auto sp = ieee_float_spect::single_precision();
  for(const auto &other : core_specs)
  {
    SECTION(spec_name(sp) + " -> " + spec_name(other))
    {
      test_float_to_float_conversion(sp, other);
    }
    SECTION(spec_name(other) + " -> " + spec_name(sp))
    {
      test_float_to_float_conversion(other, sp);
    }
  }
}

// ──────────────────────────────────────────────────────────────────
// Formerly coverage gaps, now covered
// ──────────────────────────────────────────────────────────────────

static void test_isfinite(const ieee_float_spect &spec)
{
  test_environt env{spec};
  literalt ru = env.float_utils.is_finite(env.a_bv);
  literalt rb = env.lower_bool(float_bvt::isfinite(env.a_sym, spec));
  env.assert_miter_lit(ru, rb);
  env.check("isfinite");
}

static void test_is_plus_inf(const ieee_float_spect &spec)
{
  test_environt env{spec};
  // is_plus_inf = !sign AND is_infinity
  literalt ru =
    env.satcheck.land(!env.float_utils.sign_bit(env.a_bv),
                      env.float_utils.is_infinity(env.a_bv));
  const exprt sign = extractbit_exprt(env.a_sym, spec.width() - 1);
  literalt rb = env.lower_bool(
    and_exprt(not_exprt(sign), float_bvt::isinf(env.a_sym, spec)));
  env.assert_miter_lit(ru, rb);
  env.check("is_plus_inf");
}

static void test_is_minus_inf(const ieee_float_spect &spec)
{
  test_environt env{spec};
  // is_minus_inf = sign AND is_infinity
  literalt ru =
    env.satcheck.land(env.float_utils.sign_bit(env.a_bv),
                      env.float_utils.is_infinity(env.a_bv));
  const exprt sign = extractbit_exprt(env.a_sym, spec.width() - 1);
  literalt rb = env.lower_bool(
    and_exprt(sign, float_bvt::isinf(env.a_sym, spec)));
  env.assert_miter_lit(ru, rb);
  env.check("is_minus_inf");
}

static void test_fmod(const ieee_float_spect &spec)
{
  // float_utilst::rem with ROUND_TO_ZERO = fmod (exact integer arithmetic)
  // float_bvt::mod = fmod (via float div/trunc/mul/sub)
  // NOTE: float_bvt::mod uses floating-point arithmetic internally, which
  // can produce different results from the exact integer approach when the
  // quotient is large. The miter may be SAT for small formats where the
  // limited exponent range triggers these edge cases.
  satcheckt satcheck{null_message_handler};
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  boolbvt boolbv{ns, satcheck, null_message_handler};
  bv_utilst bv_utils{satcheck};

  const floatbv_typet float_type{spec.to_type()};
  auto [a_sym, a_bv] = make_input(boolbv, symbol_table, "a", float_type);
  auto [b_sym, b_bv] = make_input(boolbv, symbol_table, "b", float_type);

  float_utilst float_utils{satcheck};
  float_utils.spec = spec;
  float_utils.rounding_mode_bits.set(ieee_floatt::ROUND_TO_ZERO);

  bvt ru = float_utils.rem(a_bv, b_bv);
  bvt rb = boolbv.convert_bv(float_bvt{}.mod(a_sym, b_sym));

  // Allow NaN bit pattern differences (IEEE 754 permits any NaN payload)
  auto is_nan_bv = [&](const bvt &bv) -> literalt
  {
    bvt exp_bits(bv.begin() + spec.f, bv.begin() + spec.f + spec.e);
    bvt frac_bits(bv.begin(), bv.begin() + spec.f);
    return satcheck.land(
      bv_utils.is_all_ones(exp_bits), bv_utils.is_not_zero(frac_bits));
  };
  const literalt both_nan = satcheck.land(is_nan_bv(ru), is_nan_bv(rb));
  satcheck.l_set_to_true(satcheck.land(!bv_utils.equal(ru, rb), !both_nan));
  check_unsat(satcheck, "fmod", spec, a_bv, b_bv, {}, ru, rb);
}

static void test_ieee_remainder(const ieee_float_spect &spec)
{
  // float_utilst::rem with ROUND_TO_EVEN = IEEE remainder (exact integer arith)
  // float_bvt::rem = IEEE remainder (via float div/trunc/mul/sub + correction)
  // Same caveat as test_fmod above.
  satcheckt satcheck{null_message_handler};
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  boolbvt boolbv{ns, satcheck, null_message_handler};
  bv_utilst bv_utils{satcheck};

  const floatbv_typet float_type{spec.to_type()};
  auto [a_sym, a_bv] = make_input(boolbv, symbol_table, "a", float_type);
  auto [b_sym, b_bv] = make_input(boolbv, symbol_table, "b", float_type);

  float_utilst float_utils{satcheck};
  float_utils.spec = spec;
  float_utils.rounding_mode_bits.set(ieee_floatt::ROUND_TO_EVEN);

  bvt ru = float_utils.rem(a_bv, b_bv);
  bvt rb = boolbv.convert_bv(float_bvt{}.rem(a_sym, b_sym));

  // Allow NaN bit pattern differences (IEEE 754 permits any NaN payload)
  auto is_nan_bv = [&](const bvt &bv) -> literalt
  {
    // exponent all ones AND fraction not all zeros
    bvt exp_bits(bv.begin() + spec.f, bv.begin() + spec.f + spec.e);
    bvt frac_bits(bv.begin(), bv.begin() + spec.f);
    return satcheck.land(
      bv_utils.is_all_ones(exp_bits), bv_utils.is_not_zero(frac_bits));
  };
  const literalt both_nan_lit = satcheck.land(is_nan_bv(ru), is_nan_bv(rb));
  const literalt results_equal = bv_utils.equal(ru, rb);
  // Miter: NOT (results_equal OR both_nan)
  satcheck.l_set_to_true(satcheck.land(!results_equal, !both_nan_lit));
  check_unsat(satcheck, "ieee_remainder", spec, a_bv, b_bv, {}, ru, rb);
}

static void test_round_to_integral(const ieee_float_spect &spec)
{
  test_environt env{spec};
  bvt ru = env.float_utils.round_to_integral(env.a_bv);
  bvt rb =
    env.lower(float_bvt{}.round_to_integral(env.a_sym, env.rm_sym, spec));
  env.assert_miter_bv(ru, rb);
  env.check_with_results("round_to_integral", ru, rb);
}

TEST_CASE(
  "float_bv_utils_equivalence_isfinite",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_isfinite);
}

TEST_CASE(
  "float_bv_utils_equivalence_is_plus_inf",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_is_plus_inf);
}

TEST_CASE(
  "float_bv_utils_equivalence_is_minus_inf",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_is_minus_inf);
}

TEST_CASE(
  "float_bv_utils_equivalence_round_to_integral",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_round_to_integral);
}

TEST_CASE(
  "float_bv_utils_equivalence_fmod",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_fmod);
}

TEST_CASE(
  "float_bv_utils_equivalence_ieee_remainder",
  "[core][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_CORE_LOOP(test_ieee_remainder);
}

TEST_CASE(
  "float_bv_utils_equivalence_isfinite_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_isfinite);
}

TEST_CASE(
  "float_bv_utils_equivalence_is_plus_inf_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_is_plus_inf);
}

TEST_CASE(
  "float_bv_utils_equivalence_is_minus_inf_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_is_minus_inf);
}

TEST_CASE(
  "float_bv_utils_equivalence_round_to_integral_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_round_to_integral);
}

TEST_CASE(
  "float_bv_utils_equivalence_fmod_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_fmod);
}

TEST_CASE(
  "float_bv_utils_equivalence_ieee_remainder_thorough",
  "[.][thorough][solvers][floatbv][equivalence]")
{
  EQUIVALENCE_THOROUGH_LOOP(test_ieee_remainder);
}

// ──────────────────────────────────────────────────────────────────
// All shared operations are now covered.
// ──────────────────────────────────────────────────────────────────
//
// ──────────────────────────────────────────────────────────────────
// All shared operations are now covered.
// ──────────────────────────────────────────────────────────────────

// ──────────────────────────────────────────────────────────────────
// x86 extended precision (explicit integer bit) smoke tests.
// Uses a tiny x86-extended format (f=3, e=3, 8-bit) to verify that
// the explicit integer bit is handled correctly.
// ──────────────────────────────────────────────────────────────────

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_abs",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_abs(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_negate",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_negate(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_add",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_add(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_mul",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_mul(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_div",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_div(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_relations",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_relations(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_isnan",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_isnan(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_round_to_integral",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_round_to_integral(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_from_signed_integer",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_from_signed_integer(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_to_signed_integer",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_to_signed_integer(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_sub",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_sub(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_fma",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_fma(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_is_equal",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_is_equal(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_isinf",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_isinf(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_isnormal",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_isnormal(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_is_zero",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_is_zero(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_isfinite",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_isfinite(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_is_plus_inf",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_is_plus_inf(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_is_minus_inf",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_is_minus_inf(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_from_unsigned_integer",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_from_unsigned_integer(x86_ext_tiny());
}

TEST_CASE(
  "float_bv_utils_equivalence_x86ext_to_unsigned_integer",
  "[core][solvers][floatbv][equivalence][x86ext]")
{
  test_to_unsigned_integer(x86_ext_tiny());
}

// Mul, div, and fma equivalence is proven at 7-bit and 10-bit formats.
// Half precision (16-bit) miters exceed SAT solver time limits even
// with fixed rounding modes. CaDiCaL or a different SAT strategy
// would be needed to push the boundary further.

// ──────────────────────────────────────────────────────────────────
// All shared operations are now covered.
// ──────────────────────────────────────────────────────────────────
