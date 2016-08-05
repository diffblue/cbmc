/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#include <solvers/refinement/string_refinement.h>
#include <ansi-c/string_constant.h>
#include <util/i2string.h>
#include <util/replace_expr.h>
#include <solvers/sat/satcheck.h>
#include <sstream>

#include <iostream>

#define STRING_LENGTH_WIDTH 32
#define CHAR_WIDTH 8

// Defines the type of strings that will be used by our refinement
typet make_string_type(const typet & index_type, const typet & char_type)
{
  // Type for strings that corresponds to : 
  // struct { index_type length; char_type * content }
  struct_typet s;

  s.components().resize(2);

  s.components()[0].set_name("length");
  s.components()[0].set_pretty_name("length");
  s.components()[0].type()=index_type;

  array_typet char_array(char_type,infinity_exprt(index_type));
  s.components()[1].set_name("content");
  s.components()[1].set_pretty_name("content");
  s.components()[1].type()=char_array;
  return s;
}

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
  next_symbol_id = 1;

  index_type  = unsignedbv_typet(STRING_LENGTH_WIDTH);
  char_type   = unsignedbv_typet(CHAR_WIDTH);
  string_type = make_string_type(index_type,char_type);
  debug() << "string_type : " << string_type.pretty() << eom;

}

string_refinementt::~string_refinementt()
{
}


symbol_exprt string_refinementt::fresh_symbol(const irep_idt &prefix,
                                              const typet &tp)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  std::string s = buf.str();
  irep_idt name(s.c_str());
  return symbol_exprt(name, tp);
}

exprt string_refinementt::make_string(const exprt &str)
{
  expr_mapt::iterator it = refined_string.find(str);
  if (it != refined_string.end()) {
    debug() << "string "<< str.get(ID_identifier) <<" found in refined_string" << eom;
    return it->second;
  }
  
  symbol_exprt length = fresh_symbol("string_length",get_string_length_type());
  symbol_exprt content = fresh_symbol("string_content",get_string_content_type());

  struct_exprt struct_string(string_type);
  struct_string.move_to_operands(length,content);
  refined_string[str] = struct_string;
  debug() << "string_refinementt::string(" << str.get(ID_identifier) << ")" << eom;
  //returns " << struct_string.pretty() << eom;
  
  return struct_string;
}


void string_refinementt::post_process()
{
  // Ackermann expansion for string lengths
  //for (expr_mapt::iterator i = string2length.begin(), end = string2length.end();
  debug() << "Not sure about what string_refinementt::post_process() does" << eom;
  
  for (expr_mapt::iterator i = refined_string.begin(),
       end = refined_string.end(); 
       i != end; ++i) 
    {
      exprt unrefined_i = i -> first;
      exprt stri = i->second;
      //exprt leni = expr_length(stri);
      //exprt si = expr_content(stri);
    
      expr_mapt::iterator j = i;
      for (++j; j != end; ++j) {
	exprt unrefined_j = j -> first;
	exprt strj = j->second;
	//exprt lenj = expr_length(strj);
	//exprt sj = expr_content(strj);
      
	implies_exprt lemma(equal_exprt(unrefined_i, unrefined_j), equal_exprt(stri, strj));
	prop.l_set_to_true(convert(lemma));
	//implies_exprt lemma(equal_exprt(stri, strj), equal_exprt(leni, lenj));prop.l_set_to_true(convert(lemma));
	//implies_exprt lemma1(equal_exprt(stri, strj), equal_exprt(si, sj));
	//prop.l_set_to_true(convert(lemma1));
    }
  }
  add_instantiations(true);
}

bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  const irep_idt &identifier = expr.get(ID_identifier);
  debug() << "string_refinementt::convert_symbol(" << identifier << ")" << eom;
 
  if (is_unrefined_string_type(type)) {
    bvt ret = convert_bv(make_string(expr));
    debug() << "Warning: what is the effect of map.set_literals?" << eom;
    map.set_literals(identifier, type, ret);
    return ret;
  } else if (is_unrefined_char_type(expr.type())) {
    symbol_exprt c = fresh_symbol("char", char_type);
    bvt ret = SUB::convert_symbol(c);
    map.set_literals(identifier, type, ret);
    return ret;
  } else {
    return SUB::convert_symbol(expr);
  }
}


bvt string_refinementt::convert_struct(const struct_exprt &expr)
{
  if (is_unrefined_string_type(expr.type()) || is_unrefined_char_type(expr.type())) {
    return bvt();
  } else {
    return SUB::convert_struct(expr);
  }
}


bvt string_refinementt::convert_function_application(
  const function_application_exprt &expr)
{
  const exprt &name = expr.function();

  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    debug() << "string_refinement::convert_function_application" 
	    << "({id = " << id <<"})" << eom;
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


bool string_refinementt::is_unrefined_string_type(const typet &type)
{
  if (type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return tag == irep_idt("__CPROVER_string");
  }
  return false;
}

bool string_refinementt::is_unrefined_char_type(const typet &type)
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
  debug() << "string_refinementt::convert_bool_bv: why start at i = 1?" << eom;
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

  exprt s1string = make_string(s1);
  exprt s2string = make_string(s2);
  exprt s1len = expr_length(s1string);
  exprt s1arr = expr_content(s1string);
  exprt s2len = expr_length(s2string);
  exprt s2arr = expr_content(s2string);

  symbol_exprt witness = fresh_symbol("index", index_type);

  implies_exprt lemma1(eq, equal_exprt(s1len, s2len));
  add_lemma(lemma1);

  string_axiomt a(string_axioms.size());
  a.idx = witness;
  a.lit = eq;
  a.premise = and_exprt(eq, binary_relation_exprt(witness, ID_lt, s1len));
  a.body = equal_exprt(index_exprt(s1arr, witness),
                       index_exprt(s2arr, witness));
  string_axioms.push_back(a);

  implies_exprt lemma2(
    not_exprt(eq),
    or_exprt(notequal_exprt(s1len, s2len),
             and_exprt(binary_relation_exprt(witness, ID_lt, s1len),
                       notequal_exprt(index_exprt(s1arr, witness),
                                      index_exprt(s2arr, witness)))));
  add_lemma(lemma2);

  return bv;
}

exprt string_refinementt::expr_length(const exprt & str)
{
  debug() << "string_refinementt::expr_length : "
	  << "would need more assertions to check the type of str"
	  << eom;
  assert(str.operands().size() == 2);
  return str.op0();
}

exprt string_refinementt::expr_content(const exprt & str)
{
  debug() << "string_refinementt::expr_content : "
	  << "would need more assertions to check the type of str"
	  << eom;
  assert(str.operands().size() == 2);
  return str.op1();
}


bvt string_refinementt::convert_string_length(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 1, "bad args to string length");

  exprt str = make_string(args[0]);
  exprt length = expr_length(str);
  debug() << "string_refinementt::string_length : " 
	  << length.pretty() << eom;
  bv = convert_bv(length);
  return bv;
}


bvt string_refinementt::convert_string_concat(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string concat");
  
  const exprt &s1 = args[0];
  const exprt &s2 = args[1];
  exprt str = make_string(f);
  exprt s1string = make_string(s1);
  exprt s2string = make_string(s2);
  exprt len = expr_length(f);
  exprt s1len = expr_length(s1string);
  exprt s2len = expr_length(s2string);
  exprt arr = expr_content(str);
  exprt s1arr = expr_content(s1string);
  exprt s2arr = expr_content(s2string);
  bvt bv = convert_bv(str);

  equal_exprt lemma1(len, plus_exprt(s1len, s2len));
  add_lemma(lemma1);

  binary_relation_exprt lemma2(len, ID_ge, s1len);
  add_lemma(lemma2);

  binary_relation_exprt lemma3(len, ID_ge, s2len);
  add_lemma(lemma3);

  symbol_exprt idx = fresh_symbol("index", index_type);

  string_axiomt a1(string_axioms.size());
  a1.idx = idx;
  a1.lit = nil_exprt();
  a1.premise = binary_relation_exprt(idx, ID_lt, s1len);
  a1.body = equal_exprt(index_exprt(s1arr, idx),
                        index_exprt(arr, idx));
  string_axioms.push_back(a1);

  string_axiomt a2(string_axioms.size());
  a2.idx = idx;
  a2.lit = nil_exprt();
  a2.premise = binary_relation_exprt(idx, ID_lt, s2len);
  a2.body = equal_exprt(index_exprt(s2arr, idx),
                        index_exprt(arr, plus_exprt(s1len, idx)));
  string_axioms.push_back(a2);

  return bv;
}


bvt string_refinementt::convert_string_substring(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  expect(args.size() == 3, "bad args to string substring");

  exprt str = make_string(f);
  exprt len = expr_length(str);
  exprt arr = expr_content(str);
  exprt arg_str = make_string(args[0]);
  exprt arg_len = expr_length(arg_str);
  exprt arg_arr = expr_content(arg_str);
  typecast_exprt i(args[1], index_type);
  typecast_exprt j(args[2], index_type);
  bvt bv = convert_bv(arr);
  exprt idx = fresh_symbol("index", index_type);

  string_axiomt a(string_axioms.size());
  a.idx = idx;
  a.lit = nil_exprt();
  a.premise = binary_relation_exprt(idx, ID_lt, len);
  a.body = equal_exprt(index_exprt(arr, idx),
                       index_exprt(arg_arr, plus_exprt(i, idx)));
  string_axioms.push_back(a);

  and_exprt lemma1(binary_relation_exprt(i, ID_lt, j),
                   and_exprt(binary_relation_exprt(j, ID_le, arg_len),
                             equal_exprt(len, minus_exprt(j, i))));
  add_lemma(lemma1);

  binary_relation_exprt lemma2(arg_len, ID_ge, len);
  add_lemma(lemma2);

  return bv;
}


bvt string_refinementt::convert_string_is_prefix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string isprefix");

  symbol_exprt isprefix = fresh_symbol("isprefix");

  exprt s0str = make_string(args[0]);
  exprt s0len = expr_length(s0str);
  exprt s0arr = expr_content(s0str);
  exprt s1str = make_string(args[1]);
  exprt s1len = expr_length(s1str);
  exprt s1arr = expr_content(s1str);
  bvt bv = convert_bool_bv(isprefix, f);

  implies_exprt lemma1(isprefix, binary_relation_exprt(s0len, ID_ge, s1len));
  add_lemma(lemma1);

  symbol_exprt witness = fresh_symbol("index", index_type);

  string_axiomt a(string_axioms.size());
  a.idx = witness;
  a.lit = isprefix;
  a.premise = and_exprt(isprefix, binary_relation_exprt(witness, ID_lt, s1len));
  a.body = equal_exprt(index_exprt(s1arr, witness),
                       index_exprt(s0arr, witness));
  string_axioms.push_back(a);

  implies_exprt lemma2(
    not_exprt(isprefix),
    or_exprt(not_exprt(binary_relation_exprt(s0len, ID_ge, s1len)),
             and_exprt(binary_relation_exprt(witness, ID_lt, s1len),
                       notequal_exprt(index_exprt(s1arr, witness),
                                      index_exprt(s0arr, witness)))));
  add_lemma(lemma2);

  return bv;
}


bvt string_refinementt::convert_string_is_suffix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "bad args to string issuffix");

  symbol_exprt issuffix = fresh_symbol("issuffix");
  bvt bv = convert_bool_bv(issuffix, f);

  exprt s0 = make_string(args[0]);
  exprt s0len = expr_length(s0);
  exprt s0arr = expr_content(s0);
  exprt s1 = make_string(args[1]);
  exprt s1len = expr_length(s1);
  exprt s1arr = expr_content(s1);

  implies_exprt lemma1(issuffix, binary_relation_exprt(s0len, ID_ge, s1len));
  add_lemma(lemma1);

  symbol_exprt witness = fresh_symbol("index", index_type);

  string_axiomt a(string_axioms.size());
  a.idx = witness;
  a.lit = issuffix;
  a.premise = and_exprt(issuffix, binary_relation_exprt(witness, ID_lt, s1len));
  a.body = equal_exprt(
    index_exprt(s1arr, witness),
    index_exprt(s0arr,
                plus_exprt(witness, minus_exprt(s0len, s1len))));
  string_axioms.push_back(a);

  implies_exprt lemma2(
    not_exprt(issuffix),
    or_exprt(not_exprt(binary_relation_exprt(s0len, ID_ge, s1len)),
             and_exprt(binary_relation_exprt(witness, ID_lt, s1len),
                       notequal_exprt(
                         index_exprt(s1arr, witness),
                         index_exprt(s0arr,
                                     plus_exprt(witness,
                                                minus_exprt(s0len, s1len)))))));
  add_lemma(lemma2);

  return bv;
}

bvt string_refinementt::convert_string_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 1, "bad args to string literal");
  const exprt &arg = args[0];
  bvt bv;
  size_t char_width = get_char_width();
  size_t string_length_width = get_string_length_width();

  if (arg.operands().size() == 1 &&
      arg.op0().operands().size() == 1 &&
      arg.op0().op0().operands().size() == 2 &&
      arg.op0().op0().op0().id() == ID_string_constant)
    {
      
      const exprt &s = arg.op0().op0().op0();
      irep_idt sval = to_string_constant(s).get_value();
      exprt str = make_string(f);
      bv = convert_bv(str);
      exprt content = expr_content(str);
      
      for (std::size_t i = 0; i < sval.size(); ++i) {
	std::string idx_binary = integer2binary(i,string_length_width);
	constant_exprt idx(idx_binary, index_type);
	std::string sval_binary=integer2binary(unsigned(sval[i]), char_width);
	constant_exprt c(sval_binary,char_type);
	equal_exprt lemma(index_exprt(content, idx), c);
	add_lemma(lemma);
      }
      
      std::string s_length_binary = integer2binary(unsigned(sval.size()),32);
      exprt s_length = constant_exprt(s_length_binary, get_string_length_type());
      exprt length = expr_length(str);
      equal_exprt lemma(length,s_length);
      debug() << "adding length constraint : " << length.pretty() << " == " << s_length.pretty() << eom;

      add_lemma(lemma);
  } else {
    expect(false, "bad arg to string literal");
  }

  return bv;
}



bvt string_refinementt::convert_char_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 1, "there should be exactly 1 argument to char literal");

  const exprt &arg = args[0];
  expect(arg.operands().size() == 1 &&
	 arg.op0().operands().size() == 1 &&
	 arg.op0().op0().operands().size() == 2 &&
	 arg.op0().op0().op0().id() == ID_string_constant, "argument to char literal should be one string constant");

  const string_constantt s = to_string_constant(arg.op0().op0().op0());
  irep_idt sval = s.get_value();
  expect(sval.size() == 1, "the argument to char literal should be a string of size 1");

  size_t char_width = get_char_width();
  std::string binary=integer2binary(unsigned(sval[0]), char_width);
  constant_exprt e(binary, char_type);
  bvt bv = convert_bv(e);
  return bv;
}


bvt string_refinementt::convert_string_char_at(
  const function_application_exprt &f)
{
  bvt bv;
  const function_application_exprt::argumentst &args = f.arguments();
  expect(args.size() == 2, "string_char_at expects 2 arguments");

  exprt str = make_string(args[0]);
  exprt content = expr_content(str);
  typecast_exprt pos(args[1], index_type);
  bv = convert_bv(index_exprt(content, pos));
  return bv;
}


bvt string_refinementt::convert_string_char_set(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  expect(args.size() == 3, "bad args to string_char_set");

  exprt str = make_string(f);
  exprt arr = expr_content(str);
  exprt len = expr_length(str);
  bvt bv = convert_bv(arr);

  exprt sarg = make_string(args[0]);
  exprt sarr = expr_content(sarg);
  exprt slen = expr_length(sarg);
  typecast_exprt idx(args[1], index_type);

  symbol_exprt c = fresh_symbol("char", char_type);
  bvt bva = convert_bv(args[2]);
  bvt bvc = convert_bv(c);
  bva.resize(bvc.size(), const_literal(false));
  debug() << "convert_string_char_set: Why don't we include 0?" << eom;
  for (size_t i = 0; i < bvc.size(); ++i) {
    prop.set_equal(bva[i], bvc[i]);
  }

  implies_exprt lemma(binary_relation_exprt(idx, ID_lt, slen),
                      and_exprt(equal_exprt(arr, update_exprt(sarr, idx, c)),
                                equal_exprt(len, slen)));
  add_lemma(lemma);

  return bv;
}


void string_refinementt::add_lemma(const exprt &lemma)
{
  prop.l_set_to_true(convert(lemma));
  cur.push_back(lemma);
}


void string_refinementt::add_instantiations(bool first)
{
  if (first) {
    for (size_t i = 0; i < string_axioms.size(); ++i) {
      update_index_set(string_axioms[i]);
    }
  }
  for (size_t i = 0; i < cur.size(); ++i) {
    update_index_set(cur[i]);
  }

  cur.clear();

  for (index_sett::iterator i = index_set.begin(), end = index_set.end();
       i != end; ++i) {
    const exprt &s = i->first;
    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j) {
      const exprt &val = *j;
      for (size_t k = 0; k < string_axioms.size(); ++k) {
        exprt lemma = instantiate(string_axioms[k], s, val);
        if (lemma.is_not_nil() && seen_instances.insert(lemma).second) {
          add_lemma(lemma);
        }
      }
    }
  }
}

std::ostream & print_array(std::ostream & out, const exprt &val) {
  exprt e = val; 
  while(e.operands().size() == 3) {  
    exprt tmp_index = e.op1();
    exprt tmp_value = e.op2();
    out << tmp_index.get(ID_value) << "->" << ((tmp_value.get(ID_value)!="")?tmp_value.get(ID_value):tmp_value.pretty()) << " ; ";
    e = e.op0();
  }
  return out;
}

bool string_refinementt::check_axioms()
{
  // build the interpretation from the model of the prop_solver
  debug() << "string_refinementt::check_axioms: build the interpretation from the model of the prop_solver" << eom;
  replace_mapt fmodel;
  
  for (expr_mapt::iterator it = refined_string.begin(),      
	 end = refined_string.end(); it != end; ++it) {
    const exprt &unrefined = it->first;
    const exprt &refined = it->second;
    exprt str = get(refined);
    debug() << "check_axioms adds to the model:" << unrefined.get(ID_identifier) << " := ";
    debug() << str.pretty() << eom;

    const exprt &a = expr_content(refined);
    const exprt &l = expr_length(refined);

    exprt len = get(l);
    debug() << "string_refinementt::check_axioms: get_array(" << a.get(ID_identifier) << ","<< len.get(ID_value) << ")" << eom;
    //exprt arr = get_array(a, len);
    fmodel[l] = len;
    //fmodel[a] = arr;
    debug() << "check_axioms adds to the model:" << a.get(ID_identifier) << " length = ";
    //print_array(debug(), arr);
    debug() << len.pretty() << eom;
  }

  std::vector< std::pair<size_t, exprt> > violated;

  for (size_t i = 0; i < string_axioms.size(); ++i) {
    debug() << "string axiom " << i << eom;
    const string_axiomt &axiom = string_axioms[i];
    if (axiom.lit.is_not_nil()) {
      exprt lit = get(axiom.lit);
      fmodel[axiom.lit] = lit;
    }

    exprt negaxiom = and_exprt(axiom.premise, not_exprt(axiom.body));
    replace_expr(fmodel, negaxiom);

    satcheck_no_simplifiert sat_check;
    SUB solver(ns, sat_check);
    solver << negaxiom;

    switch (solver()) {
    case decision_proceduret::D_SATISFIABLE: {
      debug() << "satisfiable" << eom;
      exprt val = solver.get(axiom.idx);
      violated.push_back(std::make_pair(i, val));
    } break;
    case decision_proceduret::D_UNSATISFIABLE:
      debug() << "unsatisfiable" << eom;
      break;
    default:
      expect(false, "failure in checking axiom");
    }
  }

  if (violated.empty()) {
    debug() << "no violated property" << eom;
    return true;
  }

  for (size_t i = 0; i < violated.size(); ++i) {
    debug() << "violated " << i << eom;
    const exprt &val = violated[i].second;
    const string_axiomt &axiom = string_axioms[violated[i].first];
    exprt premise(axiom.premise);
    exprt body(axiom.body);
    replace_expr(axiom.idx, val, premise);
    replace_expr(axiom.idx, val, body);
    implies_exprt instance(premise, body);
    if (seen_instances.insert(instance).second) {
      add_lemma(instance);
    }
    // TODO - add backwards instantiations
  }
  
  return false;
}


namespace {

void get_bounds(const exprt &qvar, const exprt &expr, std::vector<exprt> &out)
{
  if (expr.id() == ID_lt && expr.op0() == qvar) {
    const exprt &b = expr.op1();
    constant_exprt one("1", b.type());
    out.push_back(minus_exprt(b, one));
  } else if (expr.id() == ID_le && expr.op0() == qvar) {
    out.push_back(expr.op1());
  } else {
    forall_operands(it, expr) {
      get_bounds(qvar, *it, out);
    }
  }
}


struct stop_visit {};

class find_index_visitor: public const_expr_visitort {
public:
  find_index_visitor(const exprt &str):
    str_(str)
  {
    idx = nil_exprt();
  }
  
  void operator()(const exprt &expr)
  {
    if (expr.id() == ID_index) {
      const index_exprt &i = to_index_expr(expr);
      if (i.array() == str_) {
        idx = i.index();
        throw stop_visit();
      }
    }
  }

  const exprt &str_;
  exprt idx;
};


class find_qvar_visitor: public const_expr_visitort {
public:
  find_qvar_visitor(const exprt &qvar):
    qvar_(qvar), found(false) {}

  void operator()(const exprt &expr)
  {
    if (expr == qvar_) {
      found = true;
      throw stop_visit();
    }
  }

  const exprt &qvar_;
  bool found;
};

  //////////////////////////////////////////////////////////
  // For expressions f of a certain form, 		  //
  // returns an expression corresponding to $f^{−1}(val)$.//
  // Takes an expression containing + and − operations 	  //
  // in which qvar appears exactly once. 		  //
  // Rewrites it as a sum of qvar and elements in list	  //
  // elems different from qvar. 			  //
  // Takes e minus the sum of the element in elems.	  //
  //////////////////////////////////////////////////////////
exprt compute_subst(const exprt &qvar, const exprt &val, const exprt &f)
{
  std::cout << "string_refinement::compute_subst" << std::endl ;
  std::vector< std::pair<exprt, bool> > to_process, elems;
  to_process.push_back(std::make_pair(f, true));

  while (!to_process.empty()) {
    exprt cur = to_process.back().first;
    bool positive = to_process.back().second;
    to_process.pop_back();

    if (cur.id() == ID_plus) {
      to_process.push_back(std::make_pair(cur.op1(), positive));
      to_process.push_back(std::make_pair(cur.op0(), positive));
    } else if (cur.id() == ID_minus) {
      to_process.push_back(std::make_pair(cur.op1(), !positive));
      to_process.push_back(std::make_pair(cur.op0(), positive));
    } else if (cur.id() == ID_unary_minus) {
      to_process.push_back(std::make_pair(cur.op0(), !positive));
    } else {
      elems.push_back(std::make_pair(cur, positive));
    }
  }

  exprt ret = nil_exprt();
  bool neg = false;
  bool found = false;
  
  for (size_t i = 0; i < elems.size(); ++i) {
    exprt &t = elems[i].first;
    if (t == qvar) {
      assert(!found);
      found = true;
      neg = !elems[i].second;
    } else {
      if (!elems[i].second) {
        t = unary_minus_exprt(t);
      }
      if (ret.is_nil()) {
        ret = t;
      } else {
        ret = plus_exprt(ret, t);
      }
    }
  }

  assert(found);
  if (ret.is_nil()) {
    ret = minus_exprt(val, ret);
  } else {
    ret = val;
  }

  if (neg) {
    ret = unary_minus_exprt(ret);
  }

  return ret;
}
  
} // namespace


void string_refinementt::update_index_set(const string_axiomt &axiom)
{
  std::vector<exprt> bounds;
  get_bounds(axiom.idx, axiom.premise, bounds);

  std::vector<exprt> to_process;
  to_process.push_back(axiom.body);

  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();

      find_qvar_visitor v(axiom.idx);
      try {
        i.visit(v);
      } catch (stop_visit &) {}
      if (!v.found) {
        expr_sett &idxs = index_set[s];
        idxs.insert(bounds.begin(), bounds.end());
        idxs.insert(i);
      }
    } else {
      forall_operands(it, cur) {
        to_process.push_back(*it);
      }
    }
  }
}


void string_refinementt::update_index_set(const exprt &formula)
{
  std::vector<exprt> to_process;
  to_process.push_back(formula);

  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();

      index_set[s].insert(i);
    } else {
      forall_operands(it, cur) {
        to_process.push_back(*it);
      }
    }
  }
}


exprt string_refinementt::instantiate(const string_axiomt &axiom,
                                      const exprt &str, const exprt &val)
{
  find_index_visitor v1(str);
  try {
    axiom.body.visit(v1);
  } catch (stop_visit &) {}

  if (v1.idx.is_nil()) {
    return nil_exprt();
  }

  find_qvar_visitor v2(axiom.idx);
  try {
    v1.idx.visit(v2);
  } catch (stop_visit &) {}

  if (!v2.found) {
    return nil_exprt();
  }

  exprt r = compute_subst(axiom.idx, val, v1.idx);
  exprt premise(axiom.premise);
  replace_expr(axiom.idx, r, premise);
  exprt body(axiom.body);
  replace_expr(axiom.idx, r, body);
  implies_exprt instance(premise, body);

  return instance;
}

exprt string_refinementt::get_array(const exprt &arr, const exprt &size)
{
  debug() << "string_refinementt::get_array(" << arr.pretty() << "," << size.get(ID_value) << ")" << eom;
  exprt val = get(arr);
  debug() << "model :: " << val.pretty() << eom;
  expect(val.id() == "array-list", "unable to get array-list value");

  exprt ret =
    array_of_exprt(to_unsignedbv_type(char_type).zero_expr(),
                   array_typet(char_type, size));

  for (size_t i = 0; i < val.operands().size()/2; ++i) {  
    exprt tmp_index = val.operands()[i*2];
    debug() << "string_refinementt::get_array: warning: removed typecast" << eom;
    //typecast_exprt idx(tmp_index, index_type);
    exprt tmp_value = val.operands()[i*2+1];
    //typecast_exprt value(tmp_value, char_type);
    ret = update_exprt(ret, tmp_index, tmp_value);
  }

  return ret;
}
 

void string_refinementt::expect(bool cond, const char *msg)
{
  if (!cond) {
    throw (msg ? msg : "assertion failure!");
  }
  assert(cond);
}
