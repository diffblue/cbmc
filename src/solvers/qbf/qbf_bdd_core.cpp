/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include <solvers/prop/literal.h>

#include <fstream>

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/std_expr.h>

#include <cuddObj.hh> // CUDD Library

/*! \cond */
// FIX FOR THE CUDD LIBRARY

inline DdNode *DD::getNode() const
{
    return node;
} // DD::getNode
/*! \endcond */


#include "qbf_bdd_core.h"

qbf_bdd_certificatet::qbf_bdd_certificatet(void) : qdimacs_coret()
{
  bdd_manager=new Cudd(0, 0);
}

qbf_bdd_certificatet::~qbf_bdd_certificatet(void)
{
  for(const BDD* model : model_bdds)
  {
    if(model)
      delete model;
  }
  model_bdds.clear();

  delete(bdd_manager);
  bdd_manager=NULL;
}

literalt qbf_bdd_certificatet::new_variable(void)
{
  literalt l=qdimacs_coret::new_variable();

  if(!is_quantified(l))
    add_quantifier(quantifiert::EXISTENTIAL, l);

  return l;
}

qbf_bdd_coret::qbf_bdd_coret() : qbf_bdd_certificatet()
{
  matrix=new BDD();
  *matrix=bdd_manager->bddOne();
}

qbf_bdd_coret::~qbf_bdd_coret()
{
  for(const BDD* variable : bdd_variable_map)
  {
    if(variable)
      delete variable;
  }
  bdd_variable_map.clear();

  if(matrix)
  {
    delete(matrix);
    matrix=NULL;
  }
}

tvt qbf_bdd_coret::l_get(literalt a) const
{
  UNREACHABLE;
}

const std::string qbf_bdd_coret::solver_text()
{
  return "QBF/BDD/CORE";
}

propt::resultt qbf_bdd_coret::prop_solve()
{
  {
    status() << solver_text() << ": "
             << std::to_string(no_variables()) << " variables, "
             << std::to_string(matrix->nodeCount()) << " nodes" << eom;
  }

  model_bdds.resize(no_variables()+1, NULL);

  // Eliminate variables
  for(auto it=quantifiers.rbegin();
      it!=quantifiers.rend();
      it++)
  {
    unsigned var=it->var_no;

    if(it->type==quantifiert::EXISTENTIAL)
    {
      #if 0
      std::cout << "BDD E: " << var << ", " <<
        matrix->nodeCount() << " nodes\n";
      #endif

      BDD *model=new BDD();
      const BDD &varbdd=*bdd_variable_map[var];
      *model=matrix->AndAbstract(
        varbdd.Xnor(bdd_manager->bddOne()),
        varbdd);
      model_bdds[var]=model;

      *matrix=matrix->ExistAbstract(*bdd_variable_map[var]);
    }
    else
    {
      INVARIANT(
        it->type == quantifiert::UNIVERSAL,
        "only handles quantified variables");
      #if 0
      std::cout << "BDD A: " << var << ", " <<
        matrix->nodeCount() << " nodes\n";
      #endif

      *matrix=matrix->UnivAbstract(*bdd_variable_map[var]);
    }
  }

  if(*matrix==bdd_manager->bddOne())
  {
    compress_certificate();
    return P_SATISFIABLE;
  }
  else if(*matrix==bdd_manager->bddZero())
  {
    model_bdds.clear();
    return P_UNSATISFIABLE;
  }
  else
    return P_ERROR;
}

bool qbf_bdd_coret::is_in_core(literalt l) const
{
  UNIMPLEMENTED;
}

qdimacs_coret::modeltypet qbf_bdd_coret::m_get(literalt a) const
{
  UNIMPLEMENTED;
}

literalt qbf_bdd_coret::new_variable()
{
  literalt res=qbf_bdd_certificatet::new_variable();

  bdd_variable_map.resize(res.var_no()+1, NULL);
  BDD &var=*(new BDD());
  var=bdd_manager->bddVar();
  bdd_variable_map[res.var_no()]=&var;

  return res;
}

void qbf_bdd_coret::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  BDD clause(bdd_manager->bddZero());

  for(const literalt &l : new_bv)
  {
    BDD v(*bdd_variable_map[l.var_no()]);

    if(l.sign())
      v=~v;

    clause|=v;
  }

  *matrix&=clause;
}

literalt qbf_bdd_coret::lor(literalt a, literalt b)
{
  literalt nl=new_variable();

  BDD abdd(*bdd_variable_map[a.var_no()]);
  BDD bbdd(*bdd_variable_map[b.var_no()]);

  if(a.sign())
    abdd=~abdd;
  if(b.sign())
    bbdd=~bbdd;

  *bdd_variable_map[nl.var_no()]|=abdd | bbdd;

  return nl;
}

literalt qbf_bdd_coret::lor(const bvt &bv)
{
  for(const literalt &literal : bv)
  {
    if(literal==const_literal(true))
      return literal;
  }

  literalt nl=new_variable();

  BDD &orbdd=*bdd_variable_map[nl.var_no()];

  for(const literalt &literal : bv)
  {
    if(literal==const_literal(false))
      continue;

    BDD v(*bdd_variable_map[literal.var_no()]);
    if(literal.sign())
      v=~v;

    orbdd|=v;
  }

  return nl;
}

void qbf_bdd_coret::compress_certificate(void)
{
  status() << "Compressing Certificate" << eom;

  for(const quantifiert &quantifier : quantifiers)
  {
    if(quantifier.type==quantifiert::EXISTENTIAL)
    {
      const BDD &var=*bdd_variable_map[quantifier.var_no];
      const BDD &model=*model_bdds[quantifier.var_no];

      if(model==bdd_manager->bddOne() ||
         model==bdd_manager->bddZero())
      {
        for(const quantifiert &quantifier2 : quantifiers)
        {
          BDD &model2=*model_bdds[quantifier2.var_no];

          if(model==bdd_manager->bddZero())
            model2=model2.AndAbstract(~var, var);
          else
            model2=model2.AndAbstract(var, var);
        }
      }
    }
  }
}

const exprt qbf_bdd_certificatet::f_get(literalt l)
{
  quantifiert q;
  PRECONDITION_WITH_DIAGNOSTICS(
    !find_quantifier(l, q), "no model for unquantified variables");

  // universal?
  if(q.type==quantifiert::UNIVERSAL)
  {
    INVARIANT(l.var_no() != 0, "input literal wasn't properly initialized");
    variable_mapt::const_iterator it=variable_map.find(l.var_no());

    INVARIANT(
      it != variable_map.end(), "variable not found in the variable map");

    const exprt &sym=it->second.first;
    unsigned index=it->second.second;

    extractbit_exprt extract_expr(sym, from_integer(index, integer_typet()));

    if(l.sign())
      extract_expr.negate();

    return extract_expr;
  }
  else
  {
    // skolem functions for existentials
    INVARIANT(
      q.type == quantifiert::EXISTENTIAL,
      "only quantified literals are supported");

    function_cachet::const_iterator it=function_cache.find(l.var_no());
    if(it!=function_cache.end())
    {
      #if 0
      std::cout << "CACHE HIT for " << l.dimacs() << '\n';
      #endif

      if(l.sign())
        return not_exprt(it->second);
      else
        return it->second;
    }

    // no cached function, so construct one

    INVARIANT(
      model_bdds[l.var_no()] != nullptr,
      "there must be a model BDD for the literal");
    BDD &model=*model_bdds[l.var_no()];

    #if 0
    std::cout << "Model " << l.var_no() << '\n';
    model.PrintMinterm();
    #endif

    int *cube;
    DdGen *generator;

    or_exprt result;

    Cudd_ForeachPrime(
      bdd_manager->getManager(),
      model.getNode(),
      model.getNode(),
      generator,
      cube)
    {
      and_exprt prime;

      #if 0
      std::cout << "CUBE: ";
      for(signed i=0; i<bdd_manager->ReadSize(); i++)
        std::cout << cube[i];
      std::cout << '\n';
      #endif

      for(signed i=0; i<bdd_manager->ReadSize(); i++)
      {
        if(quantifiers[i].var_no==l.var_no())
          break; // is this sound?

        if(cube[i]!=2)
        {
          exprt subf=f_get(literalt(quantifiers[i].var_no, (cube[i]==1)));
          prime.add_to_operands(std::move(subf));
        }
      }

      simplify_extractbits(prime);

      if(prime.operands().empty())
        result.copy_to_operands(true_exprt());
      else if(prime.operands().size()==1)
        result.add_to_operands(std::move(prime.op0()));
      else
        result.add_to_operands(std::move(prime));
    }

    cube=NULL; // cube is free'd by nextCube

    exprt final;

    if(result.operands().empty())
      final=false_exprt();
    else if(result.operands().size()==1)
      final=result.op0();
    else
      final=result;

    function_cache[l.var_no()]=final;

    if(l.sign())
      return not_exprt(final);
    else
      return final;
  }
}

tvt qbf_bdd_certificatet::l_get(literalt a) const
{
  const BDD &model=*model_bdds[a.var_no()];

  if(model==bdd_manager->bddZero())
    return tvt(a.sign()?tvt::tv_enumt::TV_TRUE:tvt::tv_enumt::TV_FALSE);
  else if(model==bdd_manager->bddOne())
    return tvt(a.sign()?tvt::tv_enumt::TV_FALSE:tvt::tv_enumt::TV_TRUE);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);
}
