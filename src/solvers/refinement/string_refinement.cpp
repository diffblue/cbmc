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
unsignedbv_typet char_type(CHAR_WIDTH);
unsignedbv_typet index_type(INDEX_WIDTH);


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
  components()[0].type()=index_type;

  array_typet char_array(char_type,infinity_exprt(index_type));
  components()[1].set_name("content");
  components()[1].set_pretty_name("content");
  components()[1].type()=char_array;
}

string_axiomt::string_axiomt(symbol_exprt index, exprt prem, exprt bod)
{
  qvar = index;
  premise = prem;
  body = bod;
}

string_axiomt::string_axiomt(exprt bod)
{
  premise = true_exprt();
  body = bod;
}

std::string string_axiomt::to_string() const
{
  std::ostringstream buf;
  buf << "forall " << qvar.get_identifier() << ". (" 
      << premise.pretty() << ") ==> " << body.pretty();
  return buf.str();
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

// finds the string from which the content expression comes
std::map<irept, string_exprt*> map_content_to_string;

/*
string_exprt & string_exprt::by_content (const exprt & content)
{ return *(map_content_to_string.at(content.get_identifier())); } 

void associate_content (string_exprt * str, const exprt & content)
{ 
  std::cout << "associate " << pretty_short(content) << " to " << pretty_short(*str) << std::endl;
  map_content_to_string[content]=str;
} 
*/

string_exprt::string_exprt(exprt length, exprt content) : struct_exprt(string_ref_typet())
{
  string_ref_typet t;
  assert(length.type() == index_type);
  assert(content.type() == t.get_content_type());
  //associate_content(this,content);
  move_to_operands(length,content);
}

string_exprt::string_exprt() : struct_exprt(string_ref_typet())
{
  string_ref_typet t;
  symbol_exprt length = string_refinementt::fresh_symbol("string_length",index_type);
  symbol_exprt content = string_refinementt::fresh_symbol("string_content",t.get_content_type());
  //associate_content(this,content);
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
    } else if (id == "__CPROVER_uninterpreted_char_set") {
      return of_string_char_set(expr);
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
    constant_exprt idx(idx_binary, index_type);
    std::string sval_binary=integer2binary(unsigned(sval[i]), CHAR_WIDTH);
    constant_exprt c(sval_binary,char_type);
    equal_exprt lemma(index_exprt(content(), idx), c);
    lemmas.push_back(string_axiomt(lemma));
  }

  std::string s_length_binary = integer2binary(unsigned(sval.size()),INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, index_type);

  lemmas.push_back(string_axiomt(equal_exprt(length(),s_length)));
  return lemmas;
}


axiom_vect string_exprt::of_string_concat(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1,s2;
  axiom_vect axioms = s1.of_expr(args[0]);
  axiom_vect s2axioms = s2.of_expr(args[1]);
  axioms.insert(axioms.end(), s2axioms.begin(), s2axioms.end());

  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.push_back(string_axiomt(length_sum_lem));
  binary_relation_exprt lem1(length(), ID_ge, s1.length());
  axioms.push_back(string_axiomt(lem1));
  binary_relation_exprt lem2(length(), ID_ge, s2.length());
  axioms.push_back(string_axiomt(lem2));

  symbol_exprt idx = string_refinementt::fresh_symbol("index", index_type);
  
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

axiom_vect string_exprt::of_string_substring
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); // bad args to string substring?

  string_exprt str;
  axiom_vect axioms = str.of_expr(args[0]);
  typecast_exprt i(args[1], index_type);
  typecast_exprt j(args[2], index_type);

  symbol_exprt idx = string_refinementt::fresh_symbol("index", index_type);

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_axiomt a(idx,
		  binary_relation_exprt(idx, ID_lt, length()),
		  equal_exprt(index_exprt(content(),idx), 
			      str[plus_exprt(i, idx)]));
  axioms.push_back(a);

  and_exprt lemma1(binary_relation_exprt(i, ID_lt, j),
                   and_exprt(binary_relation_exprt(j, ID_le, str.length()),
                             equal_exprt(length(), minus_exprt(j, i))));
  axioms.push_back(string_axiomt(lemma1));

  binary_relation_exprt lemma2(str.length(), ID_ge, length());
  axioms.push_back(string_axiomt(lemma2));

  return axioms;
}

axiom_vect string_exprt::of_string_char_set
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str;
  axiom_vect axioms = str.of_expr(args[0]);
  symbol_exprt c = string_refinementt::fresh_symbol("char", char_type);
  
  std::cout << "of_string_char_set : this has to be checked" << std::endl;
  
  axioms.push_back(equal_exprt(c,args[2]));
  with_exprt sarrnew(str.content(), args[1], c);
  implies_exprt lemma(binary_relation_exprt(args[1], ID_lt, str.length()),
                      and_exprt(equal_exprt(content(), 
					    // update_exprt(str.content(), args[1], c)),
					    sarrnew),
                                equal_exprt(length(), str.length())));
  axioms.push_back(lemma);

  return axioms;
}



///////////////////////
// String refinement //
///////////////////////


// Nothing particular is done there for now
void string_refinementt::post_process()
{  
  debug() << "string_refinementt::post_process()" << eom;
  SUB::post_process();
}

bvt string_refinementt::convert_struct(const struct_exprt &expr)
{
  debug() << "string_refinementt::convert_struct" << eom;
  return SUB::convert_struct(expr);
}


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
      map.set_literals(identifier, char_type, bv1);
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
    debug() << "string_refinementt::convert_symbol of unrefined string" << eom;
    // this can happen because of boolbvt::convert_equality
    string_exprt str = string_exprt(to_symbol_expr(expr));
    bvt bv = convert_bv(str);
    return bv;
  } else if (is_unrefined_char_type(expr.type())) {
    bvt bv;
    bv.resize(CHAR_WIDTH);
    map.get_literals(identifier, char_type, CHAR_WIDTH, bv);

    forall_literals(it, bv)
      if(it->var_no()>=prop.no_variables() && !it->is_constant())
	{
	  error() << identifier << eom;
	  assert(false);
	}
    return bv;
  } else return SUB::convert_symbol(expr);
}


bvt string_refinementt::convert_function_application(
       const function_application_exprt &expr)
{
  const exprt &name = expr.function();

  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    debug() << "string_refinementt::convert_function_application(" 
	    << id << ")" << eom;
    if (id == string_literal_func 
	|| id == string_concat_func 
	|| id == string_substring_func
	|| id == string_char_set_func) {
      string_exprt str = make_string(expr);
      bvt bv = convert_bv(str);
      return bv;
    } else if (id == char_literal_func) {
      return convert_char_literal(expr);
    } else if (id == string_length_func) {
      return convert_string_length(expr);
    } else if (id == string_equal_func) {
      return convert_string_equal(expr);
    } else if (id == string_char_at_func) {
      return convert_string_char_at(expr);
    } else if (id == string_is_prefix_func) {
      return convert_string_is_prefix(expr);
    } else if (id == string_is_suffix_func) {
      return convert_string_is_suffix(expr);
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
  for (size_t i = 1; i < width; ++i) {
    ret.push_back(const_literal(false));
  }
  return ret;
}

void string_refinementt::add_lemma(const exprt &lemma)
{
  debug() << "adding lemma " << lemma << eom;
  prop.l_set_to_true(convert(lemma));
  cur.push_back(lemma);
}

void string_refinementt::add_lemmas(axiom_vect & lemmas)
{
  axiom_vect::iterator it;
  for(it = lemmas.begin(); it != lemmas.end(); it++)
    {
      // distinguish between lemmas that are not universaly quantified
      if(!(it->is_quantified()))
	add_lemma(it->body);
      else 
	string_axioms.push_back(*it);
    }
}

void string_refinementt::make_string(const symbol_exprt & sym, const exprt & str) 
{
  string_exprt s(sym);
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
  boolean_symbols.push_back(eq);
  assert(f.type() == bool_typet()); 
  bvt bv = convert_bv(eq);

  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string equal?

  string_exprt s1 = make_string(args[0]);
  string_exprt s2 = make_string(args[1]);

  // We want to write:
  // eq <=> (s1.length = s2.length  && forall i < s1.length. s1[i] = s2[i])
  // We can't do it directly because of the universal quantification inside.
  // So we say instead the three following:
  // eq => s1.length = s2.length
  // forall i < s1.length. eq => s1[i] = s2[i]
  // !eq => s1.length != s2.length || (witness < s1.length && s1[witness] != s2[witness])

  symbol_exprt witness = fresh_symbol("index", index_type);

  add_lemma(implies_exprt(eq, equal_exprt(s1.length(), s2.length())));

  string_axioms.emplace_back(witness,
			     and_exprt(eq, s1 > witness),
			     equal_exprt(s1[witness],s2[witness]));

  implies_exprt 
    lemma2(not_exprt(eq),
	   or_exprt(notequal_exprt(s1.length(), s2.length()),
		    and_exprt(s1 > witness,
			      notequal_exprt(s1[witness],s2[witness]))));
  add_lemma(lemma2);

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




bvt string_refinementt::convert_string_is_prefix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string isprefix

  symbol_exprt isprefix = fresh_symbol("isprefix");
  boolean_symbols.push_back(isprefix);
  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);
  assert(f.type() == bool_typet());
  bvt bv = convert_bv(isprefix); 

  add_lemma(implies_exprt(isprefix, s0 >= s1));
	     
  symbol_exprt witness = fresh_symbol("index", index_type);

  // forall witness < s1.length. isprefix => s1[witness] = s2[witness]
  string_axioms.emplace_back(witness, and_exprt(isprefix, s1 > witness),
			     equal_exprt(s1[witness],s0[witness]));

  or_exprt s1_notpref_s0(not_exprt(s0 >= s1),
			 and_exprt(s1 > witness, 
				   notequal_exprt(s1[witness],s0[witness])));
		       
  add_lemma(implies_exprt (not_exprt(isprefix),s1_notpref_s0));
  return bv;
}


bvt string_refinementt::convert_string_is_suffix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string issuffix?

  symbol_exprt issuffix = fresh_symbol("issuffix");
  boolean_symbols.push_back(issuffix);

  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);

  // issufix => s0.length >= s1.length
  // && forall witness < s1.length. 
  //     issufix => s1[witness] = s0[witness + s0.length - s1.length]
  // && !issuffix => s1.length > s0.length 
  //       || (s1.length > witness && s1[witness] != s0[witness + s0.length - s1.length]
  symbol_exprt witness = fresh_symbol("index", index_type);

  add_lemma(implies_exprt(issuffix, s0 >= s1));

  exprt shifted = plus_exprt(witness, 
			     minus_exprt(s0.length(), s1.length()));

  string_axioms.emplace_back(witness, and_exprt(issuffix, s1 > witness),
			     equal_exprt(s1[witness],s0[shifted]));

  implies_exprt lemma2(not_exprt(issuffix),
		       or_exprt(s1 > s0,
				and_exprt(s1 > witness, 
					  notequal_exprt(s1[witness],s0[shifted]))));

  add_lemma(lemma2);

  assert(f.type() == bool_typet());
  bvt bv = convert_bv(issuffix);

  return bv;
}



bvt string_refinementt::convert_char_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); // there should be exactly 1 argument to char literal

  const exprt &arg = args[0];
  // argument to char literal should be one string constant of size one
  assert(arg.operands().size() == 1 &&
	 arg.op0().operands().size() == 1 &&
	 arg.op0().op0().operands().size() == 2 &&
	 arg.op0().op0().op0().id() == ID_string_constant); 

  const string_constantt s = to_string_constant(arg.op0().op0().op0());
  irep_idt sval = s.get_value();
  assert(sval.size() == 1); 

  std::string binary=integer2binary(unsigned(sval[0]), CHAR_WIDTH);

  return convert_bv(constant_exprt(binary, char_type));
}


bvt string_refinementt::convert_string_char_at(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //string_char_at expects 2 arguments
  string_exprt str = make_string(args[0]);
  return convert_bv(str[args[1]]);
}



////////////////////
// PASS Algorithm //
////////////////////

void string_refinementt::add_instantiations(bool first)
{
  debug() << "string_refinementt::add_instantiations" << eom;
  if (first) {
    for (size_t i = 0; i < string_axioms.size(); ++i) {
      update_index_set(string_axioms[i]);
    }
  }
  for (size_t i = 0; i < cur.size(); ++i) {
    update_index_set(cur[i]);
  }

  cur.clear();

  for (std::map<exprt, expr_sett>::iterator i = index_set.begin(),
	 end = index_set.end(); i != end; ++i) {
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


exprt string_refinementt::get_array(const exprt &arr, const exprt &size)
{
  debug() << "string_refinementt::get_array(" << arr.get(ID_identifier) 
	  << "," << size.get(ID_value) << ")" << eom;
  exprt val = get(arr);
  
  if(val.id() == "array-list") {
    exprt ret =
      array_of_exprt(char_type.zero_expr(), array_typet(char_type, infinity_exprt(index_type)));
    // size));
    
    for (size_t i = 0; i < val.operands().size()/2; i++) {  
      exprt index = val.operands()[i*2];
      assert(index.type() == index_type);
      //typecast_exprt idx(tmp_index, index_type);
      exprt value = val.operands()[i*2+1];
      //typecast_exprt value(tmp_value, char_type);
      assert(value.type() == char_type);
      ret = with_exprt(ret, index, value);
    }
    return ret;
  
  } else {
    debug() << "unable to get array-list value of " 
	    << pretty_short(val) << eom;
    return arr;
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
      debug() << "check_axioms: " << it->first << " := " << arr << eom;
    }

  for(std::vector<exprt>::iterator it = boolean_symbols.begin();
      it != boolean_symbols.end(); it++) {
    debug() << "check_axioms: " << *it << " := " << get(*it) << eom;
    fmodel[*it] = get(*it);
  }

  std::vector< std::pair<size_t, exprt> > violated;

  for (size_t i = 0; i < string_axioms.size(); ++i) {
    debug() << "string axiom " << i << eom;
    const string_axiomt &axiom = string_axioms[i];


    exprt negaxiom = and_exprt(axiom.premise, not_exprt(axiom.body));
    replace_expr(fmodel, negaxiom);

    debug() << "string axiom = " << axiom.to_string() << eom;
    debug() << "neg axiom = " << negaxiom.pretty() << eom;

    satcheck_no_simplifiert sat_check;
    SUB solver(ns, sat_check);
    solver << negaxiom;

    switch (solver()) {
    case decision_proceduret::D_SATISFIABLE: {
      debug() << "satisfiable" << eom;
      exprt val = solver.get(axiom.qvar);
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
    replace_expr(axiom.qvar, val, premise);
    replace_expr(axiom.qvar, val, body);
    implies_exprt instance(premise, body);
    if (seen_instances.insert(instance).second) {
      add_lemma(instance);
    }
    // TODO - add backwards instantiations
  }
  
  return false;
}


namespace {

  constant_exprt index_one(integer2binary(1, INDEX_WIDTH), index_type);

  // Gets the upper bounds that are applied to [qvar], in the expression [expr]
  void get_bounds(const exprt &qvar, const exprt &expr, std::vector<exprt> & out)
  {
    std::vector<exprt> to_treat;
    to_treat.push_back(expr);
    while(!to_treat.empty()) {
      exprt e = to_treat.back();
      to_treat.pop_back();
      if (e.id() == ID_lt && e.op0() == qvar) {
	assert(e.op1().type() == index_type);
	out.push_back(minus_exprt(e.op1(), index_one));
      } else if (e.id() == ID_le && e.op0() == qvar) {
	out.push_back(e.op1());
      } else {
	forall_operands(it, e) {
	  to_treat.push_back(*it);
	}
      }
    }
  }




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
  //std::cout << "string_refinement::compute_subst" << std::endl ;
  std::vector< std::pair<exprt, bool> > to_process, elems;
  to_process.push_back(std::make_pair(f, true));

  while (!to_process.empty()) {
    exprt cur = to_process.back().first;
    bool positive = to_process.back().second;
    to_process.pop_back();
    //    std::cout << "processing " << cur.pretty() << std::endl;
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
  bool found = false;
  bool neg = false;
  
  for (size_t i = 0; (i < elems.size()) ; ++i) {
    exprt &t = elems[i].first;
    if (t == qvar) {
      assert(!found);
      found = true;
      neg = !elems[i].second;
    } else {
      if (!elems[i].second) {
        t = unary_minus_exprt(t);
      }
      ret = (ret.is_nil())?t:plus_exprt(ret, t);
    }
  }

  assert(found);
  ret = (ret.is_nil())?val:minus_exprt(val, ret);

  if (neg) return unary_minus_exprt(ret);
  else return ret;
}
  
} // namespace


class find_qvar_visitor: public const_expr_visitort {
private:
  const exprt &qvar_;

public:
  find_qvar_visitor(const exprt &qvar): qvar_(qvar) {}

  void operator()(const exprt &expr) {
    if (expr == qvar_) throw true;
  }
};

// Look for the given symbol in the index expression
bool find_qvar(const exprt index, const symbol_exprt & qvar) {
  find_qvar_visitor v2(qvar);
  try {
    index.visit(v2);
    return false;
  } catch (bool found) {return found;}
}


void string_refinementt::update_index_set(const string_axiomt &axiom)
{
  std::vector<exprt> bounds;
  get_bounds(axiom.qvar, axiom.premise, bounds);

  std::vector<exprt> to_process;
  to_process.push_back(axiom.body);

  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();

      // if cur is of the form s[i] and qvar does not appear in i...
      if(!find_qvar(i,axiom.qvar)) {
	assert(s.type() == string_type.get_content_type());
	//debug() << "map_content_to_string " << s << eom;
	//string_exprt str = string_exprt::by_content(s);
	//debug() << " --> " << str << eom;
	expr_sett &idxs = index_set[s];
	// we add the bounds to the index set 
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
      //debug() << "map_content_to_string " << s << eom;
      //string_exprt str = string_exprt::by_content(s);
      //debug() << " --> " << str << eom;
      index_set[s].insert(i);
    } else {
      forall_operands(it, cur) {
        to_process.push_back(*it);
      }
    }
  }
}


// Will be used to visit an expression and return the index used 
// with the given char array
class find_index_visitor: public const_expr_visitort {
private:
    const exprt &str_;
  
public:
  find_index_visitor(const exprt &str): str_(str){}
  
  void operator()(const exprt &expr) {
    if (expr.id() == ID_index) {
      const index_exprt &i = to_index_expr(expr);
      if (i.array() == str_)
	throw i.index();
    }
  }
};

// Find an index used in the char array  str
exprt find_index(const exprt & expr, const exprt & str) {
  find_index_visitor v1(str);
  try {
    expr.visit(v1);
    return nil_exprt();
  } 
  catch (exprt i) { return i; }
}



exprt string_refinementt::instantiate(const string_axiomt &axiom,
                                      const exprt &str, const exprt &val)
{
  //debug() << "string_refinementt::instantiate(" << axiom.to_string() << ")" << eom;
  exprt idx = find_index(axiom.body,str);
  if(idx.is_nil()) return nil_exprt();
  if(!find_qvar(idx,axiom.qvar)) return nil_exprt(); 

  exprt r = compute_subst(axiom.qvar, val, idx);
  exprt premise(axiom.premise);
  exprt body(axiom.body);
  // replace_expr(what,by,dest) replaces in dest all occurances of [what]
  // by expression [by]
  implies_exprt instance(premise, body);
  replace_expr(axiom.qvar, r, instance);
  return instance;
}

