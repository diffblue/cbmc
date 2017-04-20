/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/converters/solution.h>
#include <cegis/jsa/genetic/jsa_serialiser.h>

jsa_serialisert::jsa_serialisert(const jsa_programt &prog) :
    prog(prog)
{
}

#define FITNESS "fitness"
#define OP0 "op0"
#define OP1 "op1"
#define RESULT_OP "result_op"
#define OPCODE "opcode"
#define INVARIANT "invariant"
#define PREDICATES "predicates"
#define QUERY "query"

void jsa_serialisert::operator()(irept &sdu,
    const jsa_genetic_solutiont &entity) const
{
  sdu.set(FITNESS, entity.fitness);
  irept invariant;
  irept::subt &invariant_instructions=invariant.get_sub();
  for(const jsa_genetic_solutiont::invariantt::value_type &instr : entity.invariant)
  {
    irept instruction;
    instruction.set(OPCODE, instr.opcode);
    invariant_instructions.push_back(instruction);
  }
  sdu.set(INVARIANT, invariant);
  irept predicates;
  irept::subt &predicates_list=predicates.get_sub();
  for(const jsa_genetic_solutiont::predicatet &predicate : entity.predicates)
  {
    irept pred;
    irept::subt &predicate_instructions=pred.get_sub();
    for(const jsa_genetic_solutiont::predicatet::value_type &instr : predicate)
    {
      irept instruction;
      instruction.set(OPCODE, instr.opcode);
      instruction.set(OP0, instr.op0);
      instruction.set(OP1, instr.op1);
      instruction.set(RESULT_OP, instr.result_op);
      predicate_instructions.push_back(instruction);
    }
    predicates_list.push_back(pred);
  }
  sdu.set(PREDICATES, predicates);
  irept query;
  irept::subt &query_instructions=query.get_sub();
  for(const jsa_genetic_solutiont::queryt::value_type &instr : entity.query)
  {
    irept instruction;
    instruction.set(OPCODE, instr.opcode);
    instruction.set(OP0, instr.op0);
    instruction.set(OP1, instr.op1);
    query_instructions.push_back(instruction);
  }
  sdu.set(QUERY, query);
}

void jsa_serialisert::operator()(jsa_genetic_solutiont &entity,
    const irept &sdu) const
{
  entity.fitness=jsa_genetic_solutiont::fitnesst(sdu.get_long_long(FITNESS));
  const irept::named_subt &named_sub=sdu.get_named_sub();
  typedef irept::named_subt::const_iterator const_iterator;
  const const_iterator invariant=named_sub.find(INVARIANT);
  assert(named_sub.end() != invariant);
  for(const irept &instruction : invariant->second.get_sub())
  {
    jsa_genetic_solutiont::invariantt::value_type instr;
    instr.opcode=__CPROVER_jsa_opcodet(instruction.get_long_long(OPCODE));
    entity.invariant.push_back(instr);
  }
  const const_iterator predicates=named_sub.find(PREDICATES);
  assert(named_sub.end() != predicates);
  for(const irept &predicate : predicates->second.get_sub())
  {
    jsa_genetic_solutiont::predicatet pred;
    for(const irept &instruction : predicate.get_sub())
    {
      jsa_genetic_solutiont::predicatet::value_type instr;
      instr.opcode=__CPROVER_jsa_opcodet(instruction.get_long_long(OPCODE));
      instr.op0=__CPROVER_jsa_opt(instruction.get_long_long(OP0));
      instr.op1=__CPROVER_jsa_opt(instruction.get_long_long(OP1));
      instr.result_op=__CPROVER_jsa_opt(instruction.get_long_long(RESULT_OP));
      pred.push_back(instr);
    }
    entity.predicates.push_back(pred);
  }
  const const_iterator query=named_sub.find(QUERY);
  assert(named_sub.end() != query);
  for(const irept &instruction : query->second.get_sub())
  {
    jsa_genetic_solutiont::queryt::value_type instr;
    instr.opcode=__CPROVER_jsa_opcodet(instruction.get_long_long(OPCODE));
    instr.op0=__CPROVER_jsa_opt(instruction.get_long_long(OP0));
    instr.op1=__CPROVER_jsa_opt(instruction.get_long_long(OP1));
    entity.query.push_back(instr);
  }
}

void jsa_serialisert::operator()(jsa_solutiont &entity, const irept &sdu) const
{
  jsa_genetic_solutiont tmp;
  operator ()(tmp, sdu);
  entity=convert(tmp, prog);
}

jsa_serialisert::operator std::function<void(irept &, const jsa_genetic_solutiont &)>() const
{
  return [this](irept &sdu, const jsa_genetic_solutiont &entity)
  { jsa_serialisert::operator ()(sdu, entity);};
}

jsa_serialisert::operator std::function<void(jsa_genetic_solutiont &, const irept &)>() const
{
  return [this](jsa_genetic_solutiont &entity, const irept &sdu)
  { jsa_serialisert::operator ()(entity, sdu);};
}

jsa_serialisert::operator std::function<void(jsa_solutiont &, const irept &)>() const
{
  return [this](jsa_solutiont &entity, const irept &sdu)
  { jsa_serialisert::operator ()(entity, sdu);};
}
