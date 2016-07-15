/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#include <solvers/refinement/string_refinement.h>

string_refinementt::string_refinementt(const namespacet &_ns, propt &_prop):
    SUB(_ns, _prop)
{
  string_literal_func = "__CPROVER_uninterpreted_string_literal";
  char_literal_func = "__CPROVER_uninterpreted_char_literal";
  string_length_func = "__CPROVER_uninterpreted_strlen";
  string_equal_func = "__CPROVER_uninterpreted_string_equal";
  string_char_at_func = "__CPROVER_uninterpreted_char_at";
  string_concat_func = "__CPROVER_uninterpreted_strcat";
  string_substring_func = "__CPROVER_uninterpreted_substring";
  string_is_prefix_func = "__CPROVER_uninterpreted_strprefixof";
  string_is_suffix_func = "__CPROVER_uninterpreted_strsuffixof";
  string_char_set_func = "__CPROVER_uninterpreted_char_set";
  string_length_width = 32; // TODO!
  next_symbol_id = 1;
}


string_refinementt::~string_refinementt()
{
}


void string_refinementt::post_process()
{
  // Ackermann expansion for string lengths
  for (expr_mapt::iterator i = string2length.begin(), end = string2length.end();
       i != end; ++i) {
    exprt si = make_array(i->first);
    exprt leni = i->second;
    
    expr_mapt::iterator j = i;
    for (++j; j != end; ++j) {
      exprt sj = make_array(j->first);
      exprt lenj = j->second;

      implies_exprt lemma(equal_exprt(si, sj), equal_exprt(leni, lenj));
      prop.l_set_to_true(convert(lemma));
    }
  }

  add_instantiations();
}


bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  const irep_idt &identifier = expr.get(ID_identifier);
  
  if (is_string_type(type)) {
    bvt ret = convert_bv(make_array(expr));
    make_length(expr); // ensure there is a length for this string
    map.set_literals(identifier, type, ret);
    return ret;
  } else if (is_char_type(expr.type())) {
    symbol_exprt c = fresh_symbol("char", char_type());
    bvt ret = SUB::convert_symbol(c);
    map.set_literals(identifier, type, ret);
    return ret;
  } else {
    return SUB::convert_symbol(expr);
  }
}


bvt string_refinementt::convert_struct(const struct_exprt &expr)
{
  if (is_string_type(expr.type()) || is_char_type(expr.type())) {
    return bvt();
  } else {
    return SUB::convert_struct(expr);
  }
}


bvt string_refinementt::convert_function_application(
  const function_application_exprt &expr)
{
  const exprt &name = expr.function();
  bool ok = false;

  // check if this is something we recognize
  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    if (id == string_literal_func) {
      return convert_string_literal(expr);
    } else if (id == char_literal_func) {
      return convert_char_literal(expr);
    } else if (id == string_length_func) {
      return convert_string_length(expr);
    } else if (id == string_equal_func) {
      return convert_string_equal(expr);
    } else if (id == string_char_at_func) {
      return convert_string_char_at(expr);
    } else if (id == string_concat_func) {
      return convert_string_concat(expr);
    } else if (id == string_substring_func) {
      return convert_string_substring(expr);
    } else if (id == string_is_prefix_func) {
      return convert_string_is_prefix(expr);
    } else if (id == string_is_suffix_func) {
      return convert_string_is_suffix(expr);
    } else if (id == string_char_set_func) {
      return convert_string_char_set(expr);
    }
  }

  return SUB::convert_function_application(expr);
}


void string_refinementt::check_SAT()
{
  SUB::check_SAT();
  if (!progress) {
    if (!check_axioms()) {
      progress = true;
      add_instantiations();
    }
  }
}


bool string_refinementt::is_string_type(const typet &type)
{
  if (type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return tag == irep_idt("__CPROVER_string");
  }
  return false;
}


bool string_refinementt::is_char_type(const typet &type)
{
  if (type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return tag == irep_idt("__CPROVER_char");
  }
  return false;
}


bvt string_refinementt::convert_bool_bv(const exprt &boole, const exprt &orig)
{
  bvt ret;
  ret.push_back(convert(boole));
  size_t width = boolbv_width(orig.type());
  for (size_t i = 1; i < width; ++i) {
    ret.push_back(const_literal(false));
  }
  return ret;
}


bvt string_refinementt::convert_string_equal(
  const function_application_exprt &f)
{
  symbol_exprt eq = fresh_symbol("equal");
  bvt bv = convert_bool_bv(eq, f);   

  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string equal");

  const exprt &s1 = args[0];
  const exprt &s2 = args[1];

  symbol_exprt witness = fresh_symbol("index", index_type());
  exprt s1len = make_length(s1);
  exprt s2len = make_length(s2);

  implies_exprt lemma1(eq, equal_exprt(s1len, s2len));
  prop.l_set_to_true(convert(lemma1));

  string_axiomt a(string_axioms.size());
  a.idx = witness;
  a.lit = bv[0];
  exprt s1arr = make_array(s1);
  exprt s2arr = make_array(s2);
  a.premise = binary_relation_exprt(witness, ID_lt, s1len);
  a.body = equal_exprt(index_exprt(s1arr, witness),
                       index_exprt(s2arr, witness));
  string_axioms.push_back(a);

  implies_exprt lemma2(
    not_exprt(eq),
    or_exprt(notequal_exprt(s1len, s2len),
             and_exprt(binary_relation_exprt(witness, ID_lt, s1len),
                       notequal_exprt(index_exprt(s1arr, witness),
                                      index_exprt(s2arr, witness)))));
  prop.l_set_to_true(convert(lemma2));

  return bv;
}


bvt string_refinementt::convert_string_length(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 1, "bad args to string length");

  expr len = make_length(args[0]);
  bv = convert_bv(len);
  return bv;
}


bvt string_refinementt::convert_string_concat(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string concat");
  
  exprt arr = make_array(f);
  bv = convert_bv(arr);
  
  const exprt &s1 = args[0];
  const exprt &s2 = args[1];

  exprt len = make_length(f);
  exprt s1len = make_length(s1);
  exprt s2len = make_length(s2);

  exprt s1arr = make_array(s1);
  exprt s2arr = make_array(s2);

  equal_exprt lemma1(len, plus_exprt(s1len, s2len));
  prop.l_set_to_true(convert(lemma1));

  binary_relation_exprt lemma2(len, ID_ge, s1len);
  prop.l_set_to_true(convert(lemma2));

  binary_relation_exprt lemma3(len, ID_ge, s2len);
  prop.l_set_to_true(convert(lemma3));

  symbol_exprt idx = fresh_symbol("index", index_type());

  string_axiomt a1(string_axioms.size());
  a1.idx = idx;
  a1.lit = literalt();
  a1.premise = binary_relation_exprt(idx, ID_lt, s1len);
  a1.body = equal_exprt(index_exprt(s1arr, idx),
                        index_exprt(arr, idx));
  string_axioms.push_back(a1);

  string_axiomt a2(string_axioms.size());
  a2.idx = idx;
  a2.lit = literalt();
  a2.premise = binary_relation_exprt(idx, ID_lt, s2len);
  a2.body = equal_exprt(index_exprt(s2arr, idx),
                        index_exprt(arr, plus_exprt(s1len, idx)));
  string_axioms.push_back(a2);

  return bv;
}


bvt string_refinementt::convert_string_substring(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();  
  expect(args.size() == 3, "bad args to string substring");

  exprt arr = make_array(f);
  bv = convert_bv(arr);

  exprt len = make_length(f);

  exprt sarr = make_array(args[0]);
  exprt slen = make_length(args[0]);
  typecast_exprt i(args[1], index_type());
  typecast_exprt j(args[2], index_type());

  exprt idx = fresh_symbol("index", index_type());

  string_axiomt a(string_axioms.size());
  a.idx = idx;
  a.lit = literalt();
  a.premise = binary_relation_exprt(idx, ID_lt, len);
  a.body = equal_exprt(index_exprt(arr, idx),
                       index_exprt(sarr, plus_exprt(i, idx)));
  string_axioms.push_back(a);

  and_exprt lemma1(binary_relation_exprt(i, ID_lt, j),
                   and_exprt(binary_relation_exprt(j, ID_le, slen),
                             equal_exprt(len, minus_exprt(j, i))));
  prop.l_set_to_true(convert(lemma1));

  binary_relation_exprt lemma2(slen, ID_ge, len);
  prop.l_set_to_true(convert(lemma2));

  return bv;
}


bvt string_refinementt::convert_string_is_prefix(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string isprefix");

  symbol_exprt isprefix = fresh_symbol("isprefix");
  bv = convert_bool_bv(isprefix, f);

  exprt slen = make_length(args[0]);
  exprt sarr = make_array(args[0]);
  exprt s1len = make_length(args[1]);
  exprt s1arr = make_array(args[1]);

  implies_exprt lemma1(isprefix, binary_relation_exprt(slen, ID_ge, s1len));
  prop.l_set_to_true(convert(lemma1));

  symbol_exprt witness = fresh_symbol("index", index_type());

  string_axiomt a(string_axioms.size());
  a.idx = witness;
  a.lit = bv[0];
  a.premise = binary_relation_exprt(witness, ID_lt, s1len);
  a.body = equal_exprt(index_exprt(s1arr, witness),
                       index_exprt(sarr, witness));
  string_axioms.push_back(a);

  implies_exprt lemma2(
    not_exprt(isprefix),
    or_exprt(not_exprt(binary_relation_exprt(slen, ID_ge, s1len)),
             and_exprt(binary_relation_exprt(witness, ID_lt, s1len),
                       notequal_exprt(index_exprt(s1arr, witness),
                                      index_exprt(sarr, witness)))));
  prop.l_set_to_true(convert(lemma2));

  return bv;
}


bvt string_refinementt::convert_string_is_suffix(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string issuffix");

  symbol_exprt issuffix = fresh_symbol("issuffix");
  bv = convert_bool_bv(issuffix, f);

  exprt slen = make_length(args[0]);
  exprt sarr = make_array(args[0]);
  exprt s1len = make_length(args[1]);
  exprt s1arr = make_array(args[1]);

  implies_exprt lemma1(isprefix, binary_relation_exprt(slen, ID_ge, s1len));
  prop.l_set_to_true(convert(lemma1));

  symbol_exprt witness = fresh_symbol("index", index_type());

  string_axiomt a(string_axioms.size());
  a.idx = witness;
  a.lit = bv[0];
  a.premise = binary_relation_exprt(witness, ID_lt, s1len);
  a.body = equal_exprt(
    index_exprt(s1arr, witness),
    index_exprt(sarr,
                plus_exprt(witness, minus_exprt(slen, s1len))));
  string_axioms.push_back(a);

  implies_exprt lemma2(
    not_exprt(isprefix),
    or_exprt(not_exprt(binary_relation_exprt(slen, ID_ge, s1len)),
             and_exprt(binary_relation_exprt(witness, ID_lt, s1len),
                       notequal_exprt(
                         index_exprt(s1arr, witness),
                         index_exprt(sarr,
                                     plus_exprt(witness,
                                                minus_exprt(slen, s1len)))))));
  prop.l_set_to_true(convert(lemma2));

  return bv;
}


bvt string_refinementt::convert_string_literal(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 1, "bad args to string literal");

  const exprt &arg = args[0];
  if (arg.operands().size() == 1 &&
      arg.operands()[0].operands().size() == 1 &&
      arg.operands()[0].operands()[0].operands().size() == 2 &&
      arg.operands()[0].operands()[0].operands()[0].id() == ID_string_constant){
    const exprt &s = arg.operands()[0].operands()[0].operands()[0];
    irep_idt sval = to_string_constant(s).get_value();
    exprt arr = make_array(f);
    bv = convert_bv(arr);

    for (std::size_t i = 0; i < sval.size(); ++i) {
      constant_exprt idx(i2string(i), index_type());
      constant_exprt c(i2string(int(sval[i])), char_type());
      equal_exprt lemma(index_exprt(arr, idx), c);
      prop.l_set_to_true(convert(lemma));
    }
    exprt len = make_length(f);
    equal_exprt lemma(len, constant_exprt(sval.size(), index_type()));
    prop.l_set_to_true(convert(lemma));
  } else {
    expect(false, "bad arg to string literal");
  }

  return bv;
}


bvt string_refinementt::convert_char_literal(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 1, "bad args to char literal");
  
  const exprt &arg = args[0];
  if (arg.operands().size() == 1 &&
      arg.operands()[0].operands().size() == 1 &&
      arg.operands()[0].operands()[0].operands().size() == 2 &&
      arg.operands()[0].operands()[0].operands()[0].id() == ID_string_constant){
    const exprt &s = arg.operands()[0].operands()[0].operands()[0];
    irep_idt sval = to_string_constant(s).get_value();
    expect(sval.size() == 1, "bad literal in char literal");

    bv = convert_bv(constant_exprt(int(sval[0]), char_type()));
  } else {
    expect(false, "char literal");
  }

  return bv;
}


bvt string_refinementt::convert_string_char_at(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string_char_at");

  exprt arr = make_array(args[0]);
  typecast_exprt pos(args[1], index_type());
  bv = convert_bv(index_exprt(arr, pos));
  return bv;
}


bvt string_refinementt::convert_string_char_set(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();  
  expect(args.size() == 3, "bad args to string_char_set");

  exprt arr = make_array(f);
  bv = convert_bv(arr);
  exprt len = make_length(f);
  
  exprt sarr = make_array(args[0]);
  exprt slen = make_length(args[0]);
  typecast_exprt idx(args[1], index_type());

  symbol_exprt c = fresh_symbol("char", char_type());
  bvt bva = convert_bv(args[2]);
  bvt bvc = convert_bv(c);
  bva.resize(bvc.size(), const_literal(false));
  for (size_t i = 0; i < bvc.size(); ++i) {
    prop.set_equal(bva[i], bvc[i]);
  }

  implies_exprt lemma(binary_relation_exprt(idx, ID_lt, slen),
                      and_exprt(equal_exprt(arr, update_exprt(sarr, idx, c)),
                                equal_exprt(len, slen)));
  prop.l_set_to_true(convert(lemma));

  return bv;
}


void string_refinementt::add_instantiations()
{
}


bool string_refinementt::check_axioms()
{
  return false;
}


void string_refinementt::update_index_set(const exprt &formula)
{
}


exprt string_refinementt::instantiate(const string_axiomt &axiom,
                                      const exprt &str, const exprt &val)
{
}


symbol_exprt string_refinementt::fresh_symbol(const irep_idt &prefix,
                                              const typet &tp)
{
  irep_idt name("string_refinement#");
  name += prefix + "#" + i2string(next_symbol_id++);
  return symbol_exprt(name, tp);
}


typet string_refinementt::index_type()
{
  return unsignedbv_typet(string_length_width);
}


typet string_refinementt::char_type()
{
  return unsignedbv_typet(8);
}


exprt string_refinementt::make_length(const exprt &str)
{
  expr_mapt::iterator it = string2length.find(str);
  if (it != string2length.end()) {
    return it->second;
  }
  symbol_exprt len = fresh_symbol("string_length", index_type());
  string2length[str] = len;
  length2string[len] = str;
  return len;
}


exprt string_refinementt::make_array(const exprt &str)
{
  expr_mapt::iterator it = string2array.find(str);
  if (it != string2array.end()) {
    return it->second;
  }
  symbol_exprt arr = fresh_symbol("string_array",
                                  array_typet(char_type(), nil_exprt()));
  // TODO - is nil ok here for size?
  string2array[str] = arr;
  return arr;
}


void string_refinementt::expect(bool cond, const char *msg)
{
  assert(cond);
  if (!cond) {
    throw (msg ? msg : "assertion failure!");
  }
}
