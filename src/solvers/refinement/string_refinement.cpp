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

// Types used in this refinement
unsignedbv_typet ref_char_typet(CHAR_WIDTH);
unsignedbv_typet ref_index_typet(INDEX_WIDTH);


// Succinct version of pretty()
std::string pretty_short(exprt expr) {
  std::ostringstream buf;
  if(expr.get(ID_identifier) != "") {
    buf << expr.get(ID_identifier);
  } else if (expr.operands().size() > 0) {
    for (int i =0; i<expr.operands().size(); i++)
      buf << expr.operands()[i].get(ID_identifier) << ";";
  } else if(expr.get(ID_value) != "") {
    buf << expr.get(ID_value);
  } else buf << expr.pretty();
  return buf.str();
}

// associate a string to symbols
std::map<irep_idt, string_exprt> symbol_to_string;



string_ref_typet::string_ref_typet() : struct_typet() {
  components().resize(2);

  components()[0].set_name("length");
  components()[0].set_pretty_name("length");
  components()[0].type()=ref_index_typet;

  array_typet char_array(ref_char_typet,infinity_exprt(ref_index_typet));
  components()[1].set_name("content");
  components()[1].set_pretty_name("content");
  components()[1].type()=char_array;
}

string_axiomt::string_axiomt(symbol_exprt index, exprt prem, exprt bod)
{
  idx = index;
  premise = prem;
  body = bod;
  lit = nil_exprt();
}

string_axiomt::string_axiomt(exprt bod)
{
  premise = true_exprt();
  body = bod;
  lit = nil_exprt();
}

string_refinementt::string_refinementt(const namespacet &_ns, propt &_prop):
  SUB(_ns, _prop)
{
  string_literal_func = "__CPROVER_uninterpreted_string_literal";
  char_literal_func = "__CPROVER_uninterpreted_char_literal";
  string_length_func = "__CPROVER_uninterpreted_strlen";
  string_equal_func = "__CPROVER_uninterpreted_string_equal";
  string_copy_func = "__CPROVER_uninterpreted_string_copy";
  string_char_at_func = "__CPROVER_uninterpreted_char_at";
  string_concat_func = "__CPROVER_uninterpreted_strcat";
  string_substring_func = "__CPROVER_uninterpreted_substring";
  string_is_prefix_func = "__CPROVER_uninterpreted_strprefixof";
  string_is_suffix_func = "__CPROVER_uninterpreted_strsuffixof";
  string_char_set_func = "__CPROVER_uninterpreted_char_set";
}

string_refinementt::~string_refinementt()
{
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

unsigned string_refinementt::next_symbol_id = 1;

symbol_exprt string_refinementt::fresh_symbol(const irep_idt &prefix,
                                              const typet &tp)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  std::string s = buf.str();
  irep_idt name(s.c_str());
  return symbol_exprt(name, tp);
}

string_exprt::string_exprt(exprt length, exprt content) : struct_exprt(string_ref_typet())
{
  string_ref_typet t;
  assert(length.type() == ref_index_typet);
  assert(content.type() == t.get_content_type());
  move_to_operands(length,content);
}

string_exprt::string_exprt() : struct_exprt(string_ref_typet())
{
  string_ref_typet t;
  symbol_exprt length = string_refinementt::fresh_symbol("string_length",ref_index_typet);
  symbol_exprt content = string_refinementt::fresh_symbol("string_content",t.get_content_type());
  move_to_operands(length,content);
}


string_exprt::string_exprt(symbol_exprt sym) : string_exprt()
{
  symbol_to_string[sym.get_identifier()] = *this;
}

axiom_vect string_exprt::of_expr(exprt unrefined_string)
{
  if(unrefined_string.id()==ID_function_application)
    return of_function_application(to_function_application_expr(unrefined_string));
  else if(unrefined_string.id()==ID_symbol) {
    return of_symbol(to_symbol_expr(unrefined_string));
  }
  else
    throw "string_exprt of something else than function application not implemented";
}

axiom_vect string_exprt::of_symbol(const symbol_exprt & expr) {
  axiom_vect lemmas;
  string_exprt s = symbol_to_string[expr.get_identifier()];
  lemmas.push_back(string_axiomt(equal_exprt(s.content(),content())));
  lemmas.push_back(string_axiomt(equal_exprt(s.length(),length())));
  return lemmas;
}

axiom_vect string_exprt::of_function_application(const function_application_exprt & expr)
{
  const exprt &name = expr.function();
  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    std::cout << "string_exprt::of_function_application(" 
	      << id << ")" << std::endl;
    if (id == "__CPROVER_uninterpreted_string_literal") {
      return of_string_literal(expr);
    } else if (id == "__CPROVER_uninterpreted_strcat") {
      return of_string_concat(expr);
    } else if (id == "__CPROVER_uninterpreted_substring") {
      return of_string_substring(expr);
    } 
  }
  throw "non string function";
}

axiom_vect string_exprt::of_string_literal(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string literal?
  const exprt &arg = args[0];
  axiom_vect lemmas;

  assert (arg.operands().size() == 1 &&
	  arg.op0().operands().size() == 1 &&
	  arg.op0().op0().operands().size() == 2 &&
	  arg.op0().op0().op0().id() == ID_string_constant); // bad arg to string literal?
      
  const exprt &s = arg.op0().op0().op0();
  irep_idt sval = to_string_constant(s).get_value();

  //  debug() << 
  std::cout << "string_exprtt::convert_string_literal(" << sval << ")" << std::endl;

  for (std::size_t i = 0; i < sval.size(); ++i) {
    std::string idx_binary = integer2binary(i,INDEX_WIDTH);
    constant_exprt idx(idx_binary, ref_index_typet);
    std::string sval_binary=integer2binary(unsigned(sval[i]), CHAR_WIDTH);
    constant_exprt c(sval_binary,ref_char_typet);
    equal_exprt lemma(index_exprt(content(), idx), c);
    lemmas.push_back(string_axiomt(lemma));
  }

  std::string s_length_binary = integer2binary(unsigned(sval.size()),INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, ref_index_typet);

  lemmas.push_back(string_axiomt(equal_exprt(length(),s_length)));
  return lemmas;
}


axiom_vect string_exprt::of_string_concat(const function_application_exprt &f)
{
  axiom_vect axioms;
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1,s2;
  s1.of_expr(args[0]);
  s2.of_expr(args[1]);

  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.push_back(string_axiomt(length_sum_lem));
  binary_relation_exprt lem1(length(), ID_ge, s1.length());
  axioms.push_back(string_axiomt(lem1));
  binary_relation_exprt lem2(length(), ID_ge, s2.length());
  axioms.push_back(string_axiomt(lem2));

  symbol_exprt idx = string_refinementt::fresh_symbol("index", ref_index_typet);
  
  //string_axiomt a1(string_axioms.size());
  string_axiomt a1(idx, binary_relation_exprt(idx, ID_lt, s1.length()),
		   equal_exprt(index_exprt(s1.content(), idx),
			       index_exprt(content(), idx)));
  axioms.push_back(a1);

  string_axiomt a2(idx, binary_relation_exprt(idx, ID_lt, s2.length()),
		   equal_exprt(index_exprt(s2.content(), idx),
			       index_exprt(content(), 
					   plus_exprt(s1.length(), idx))));
  axioms.push_back(a2);
  return axioms;
}

axiom_vect string_exprt::of_string_substring(const function_application_exprt &expr)
{
  throw "of_string_substring: not implemented";
}

/*
exprt string_refinementt::expr_length(const exprt & str)
{
  assert(str.type() == string_type);
  member_exprt m (str,"length",string_type.get_length_type());
  return m;
}

bvt string_refinementt::bv_component(const bvt & struct_bv, const std::string & name, const typet & subtype) {
  const struct_typet::componentst &components=
    to_struct_type(string_type).components();
  
  std::size_t offset=0;
  
  for(struct_typet::componentst::const_iterator it=components.begin();
      it!=components.end(); it++)
    {
      const typet &subtype=it->type();
      std::size_t sub_width=boolbv_width(subtype);

      if(it->get_name()==name)
      {
        assert(subtype == subtype);
        bvt bv;
        bv.resize(sub_width);
        assert(offset+sub_width<=struct_bv.size());

        for(std::size_t i=0; i<sub_width; i++)
          bv[i]=struct_bv[offset+i];
        return bv;
      }

      offset+=sub_width;
    }

  error() << "component " << name << " not found in structure" << eom;
  throw 0;

}

exprt string_refinementt::expr_content(const exprt & str)
{
  assert(str.type() == string_type);
  return member_exprt(str,"content",string_type.get_content_type());
}

exprt string_refinementt::make_char(const exprt &chr)
{
  assert(string_refinementt::is_unrefined_char_type(chr.type())); 
  symbol_exprt c = string_refinementt::fresh_symbol("char", string_ref_typet().get_char_type());
  refined_char[chr] = c;
  return c;
}
*/

// Nothing particular is done there for now
void string_refinementt::post_process()
{  
  debug() << "string_refinementt::post_process()" << eom;
  SUB::post_process();
}


// This is not much different from the function from boolbv.
// We simply record the string in the map [refined_string]
bool string_refinementt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation) return true;

  const typet &type=ns.follow(expr.lhs().type());

  if(expr.lhs().id()==ID_symbol &&
     type==ns.follow(expr.rhs().type()) &&
     type.id()!=ID_bool)
  {
    if(is_unrefined_string_type(type)) {
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      make_string(sym,expr.rhs());
      return false;
    }
    else if(is_unrefined_char_type(type)) {
      const bvt &bv1=convert_bv(expr.rhs());
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      const irep_idt &identifier = sym.get_identifier();
      map.set_literals(identifier, ref_char_typet, bv1);
      if(freeze_all) set_frozen(bv1);
      return false;
    } else return SUB::boolbv_set_equality_to_true(expr);
  }

  return true;
}

bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  const irep_idt &identifier = expr.get(ID_identifier);
  if(identifier.empty())
    throw "string_refinementt::convert_symbol got empty identifier";

  debug() << "string_refinementt::convert_symbol(" << identifier << ")" << eom;
  
  if (is_unrefined_string_type(type)) {
    debug() << "string_refinementt::convert_symbol of unrefined string"
	    << " (this can happen because of boolbvt::convert_equality)" 
	    << eom;
    string_exprt str = string_exprt(to_symbol_expr(expr));
    debug() << "convert_bv(" << str.pretty() << eom;
    bvt bv = convert_bv(str);
    return bv;
  } else if (is_unrefined_char_type(expr.type())) {
    bvt bv;
    bv.resize(CHAR_WIDTH);
    map.get_literals(identifier, ref_char_typet, CHAR_WIDTH, bv);

    forall_literals(it, bv)
      if(it->var_no()>=prop.no_variables() && !it->is_constant())
	{
	  error() << identifier << eom;
	  assert(false);
	}
    return bv;
  } else return SUB::convert_symbol(expr);
}

// This does nothing special
bvt string_refinementt::convert_struct(const struct_exprt &expr)
{
  debug() << "string_refinementt::convert_struct(" 
	  << pretty_short(expr) << eom;
  return SUB::convert_struct(expr);
}


bvt string_refinementt::convert_function_application(
       const function_application_exprt &expr)
{
  const exprt &name = expr.function();

  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    debug() << "string_refinementt::convert_function_application(" 
	    << id << ")" << eom;
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

void string_refinementt::add_lemma(const exprt &lemma)
{
  if(lemma.operands().size() == 2) 
    {
      debug() << "adding lemma " << pretty_short(lemma.op0())
	      << " = " << pretty_short(lemma.op1()) << eom;
    }
  prop.l_set_to_true(convert(lemma));
  cur.push_back(lemma);
}

void string_refinementt::add_lemmas(axiom_vect & lemmas)
{
  axiom_vect::iterator it;
  for(it = lemmas.begin(); it != lemmas.end(); it++)
    {
      // distinguished between lemmas that are not universaly quantified
      if(!(it->is_quantified()))
	add_lemma(it->body);
      else 
	string_axioms.push_back(*it);
    }
}

void string_refinementt::make_string(const symbol_exprt & sym, const exprt & str) 
{
  string_exprt s(sym);
  debug() << "make_string of symbol " << pretty_short(sym) << eom;
  axiom_vect lemmas = s.of_expr(str);
  add_lemmas(lemmas);
}

string_exprt string_refinementt::make_string(const exprt & str) 
{
  string_exprt s;
  axiom_vect lemmas = s.of_expr(str);
  add_lemmas(lemmas);
  return s;
}

bvt string_refinementt::convert_string_equal(
  const function_application_exprt &f)
{
  symbol_exprt eq = fresh_symbol("equal");
  bvt bv = convert_bool_bv(eq, f);   

  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string equal?

  const exprt &s1 = args[0];
  const exprt &s2 = args[1];

  string_exprt s1string = make_string(s1);
  string_exprt s2string = make_string(s2);
  exprt s1len = s1string.length();
  exprt s1arr = s1string.content();
  exprt s2len = s2string.length();
  exprt s2arr = s2string.content();
  throw "string_refinementt::convert_string_equal not implemented";
  /*
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
  */
  return bv;
}


bvt string_refinementt::convert_string_length(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string length?
  debug() << "string_refinementt::convert_string_length(" 
	  << pretty_short(args[0]) << " ) " << eom;

  string_exprt str = make_string(args[0]);
  exprt length = str.length();
  bvt bv = convert_bv(length);
  return bv;
}


bvt string_refinementt::convert_string_concat(
  const function_application_exprt &f)
{
  string_exprt str;
  str.of_expr(f);
  bvt bv = convert_bv(str);
  return bv;
}


bvt string_refinementt::convert_string_substring(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 3); // bad args to string substring?

  string_exprt str = make_string(f);
  exprt len = str.length();
  exprt arr = str.content();
  string_exprt arg_str = make_string(args[0]);
  exprt arg_len = arg_str.length();
  exprt arg_arr = arg_str.content();
  typecast_exprt i(args[1], ref_index_typet);
  typecast_exprt j(args[2], ref_index_typet);
  bvt bv = convert_bv(arr);
  throw "string_refinementt::convert_string_substring unimplemented";
  /*exprt idx = fresh_symbol("index", index_type);

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
  */
  return bv;
}


bvt string_refinementt::convert_string_is_prefix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string isprefix

  symbol_exprt isprefix = fresh_symbol("isprefix");

  string_exprt s0str = make_string(args[0]);
  exprt s0len = s0str.length();
  exprt s0arr = s0str.content();
  string_exprt s1str = make_string(args[1]);
  exprt s1len = s1str.length();
  exprt s1arr = s1str.content();
  bvt bv = convert_bool_bv(isprefix, f);
  throw "string_refinementt::convert_string_is_prefix unimplemented" ;
  /*
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
  */
  return bv;
}


bvt string_refinementt::convert_string_is_suffix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string issuffix?

  symbol_exprt issuffix = fresh_symbol("issuffix");
  bvt bv = convert_bool_bv(issuffix, f);

  throw "string_refinementt::convert_string_is_suffix unimplemented";
  /*
  string_exprt s0 = make_string(args[0]);
  exprt s0len = s0.length();
  exprt s0arr = s0.content();
  string_exprt s1 = make_string(args[1]);
  exprt s1len = s1.length();
  exprt s1arr = s1.content();

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
  */
  return bv;
}

bvt string_refinementt::convert_string_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string literal?
  const exprt &arg = args[0];


  assert (arg.operands().size() == 1 &&
	  arg.op0().operands().size() == 1 &&
	  arg.op0().op0().operands().size() == 2 &&
	  arg.op0().op0().op0().id() == ID_string_constant); // bad arg to string literal?
      
  const exprt &s = arg.op0().op0().op0();
  irep_idt sval = to_string_constant(s).get_value();

  debug() << "Warning : string_refinementt::convert_string_literal("
	  << sval << ") should not be used anymore" << eom;
  throw "string_refinementt::convert_string_literal";

  exprt str = make_string(f);
  bvt bv_str = convert_bv(str);
  /*

  bvt content = bv_content(bv_str);

  for (std::size_t i = 0; i < sval.size(); ++i) {
    std::string idx_binary = integer2binary(i,string_length_width);
    constant_exprt idx(idx_binary, index_type);
    std::string sval_binary=integer2binary(unsigned(sval[i]), char_width);
    constant_exprt c(sval_binary,char_type);
    equal_exprt lemma(index_exprt(symbol_content(str), idx), c);
    add_lemma(lemma);
  }

  std::string s_length_binary = integer2binary(unsigned(sval.size()),32);
  exprt s_length = constant_exprt(s_length_binary, string_type.get_length_type());
  exprt length = expr_length(str);
  equal_exprt lemma(length,s_length);

  add_lemma(lemma);
  */
  return bv_str;
}



bvt string_refinementt::convert_char_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); // there should be exactly 1 argument to char literal

  const exprt &arg = args[0];
  assert(arg.operands().size() == 1 &&
	 arg.op0().operands().size() == 1 &&
	 arg.op0().op0().operands().size() == 2 &&
	 arg.op0().op0().op0().id() == ID_string_constant); // argument to char literal should be one string constant

  const string_constantt s = to_string_constant(arg.op0().op0().op0());
  irep_idt sval = s.get_value();
  assert(sval.size() == 1); //the argument to char literal should be a string of size 1

  std::string binary=integer2binary(unsigned(sval[0]), CHAR_WIDTH);
  constant_exprt e(binary, ref_char_typet);
  //refined_char[f] = e;
  bvt bv = convert_bv(e);
  return bv;
}


bvt string_refinementt::convert_string_char_at(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //string_char_at expects 2 arguments
  debug() << "string_refinementt::convert_char_at("
	  << pretty_short(args[0]) << "," 
	  << pretty_short(args[1]) << ")" << eom;

  string_exprt str = make_string(args[0]);
  typecast_exprt pos(args[1], ref_index_typet);
  index_exprt char_at(str.content(), pos);
  debug() << " --> " << char_at.pretty() << eom;
  bvt bv = convert_bv(char_at);
  return bv;
}


bvt string_refinementt::convert_string_char_set(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str = make_string(f);
  exprt arr = str.content();
  exprt len = str.length();
  bvt bv = convert_bv(arr);

  string_exprt sarg = make_string(args[0]);
  exprt sarr = sarg.content();
  exprt slen = sarg.length();
  typecast_exprt idx(args[1], ref_index_typet);

  symbol_exprt c = fresh_symbol("char", ref_char_typet);
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

bool string_refinementt::check_axioms()
{
  // build the interpretation from the model of the prop_solver
  
  debug() << "string_refinementt::check_axioms: ==============="
	  << "===========================================" << eom;
  debug() << "string_refinementt::check_axioms: build the" 
	  << " interpretation from the model of the prop_solver" << eom;
  replace_mapt fmodel;

  debug() << "We should look at the strings in symbol_to_string" << eom;

  std::map<irep_idt, string_exprt>::iterator it;
  for (it = symbol_to_string.begin(); it != symbol_to_string.end(); ++it) 
    {
      string_exprt refined = it->second;
      const exprt &econtent = refined.content();
      const exprt &elength  = refined.length();
      
      exprt len = get(elength);
      exprt arr = get_array(econtent, len);
      fmodel[elength] = len;
      fmodel[econtent] = arr;
      debug() << "check_axioms adds to the model:" 
	      << it->first << " := " << arr.pretty() << eom;
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
      throw "failure in checking axiom";
      //expect(false, "failure in checking axiom");
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
  debug() << "string_refinementt::get_array(" << arr.get(ID_identifier) 
	  << "," << size.get(ID_value) << ")" << eom;
  exprt val = get(arr);
  
  if(val.id() == "array-list") {
    exprt ret =
      array_of_exprt(to_unsignedbv_type(ref_char_typet).zero_expr(),
		     array_typet(ref_char_typet, size));
    
    for (size_t i = 0; i < val.operands().size()/2; ++i) {  
      exprt tmp_index = val.operands()[i*2];
      typecast_exprt idx(tmp_index, ref_index_typet);
      exprt tmp_value = val.operands()[i*2+1];
      typecast_exprt value(tmp_value, ref_char_typet);
      ret = update_exprt(ret, idx, value);
    }
    return ret;
  
  } else {
    debug() << "unable to get array-list value of " 
	    << val.pretty() << eom;
    return arr;
  }
}
 
