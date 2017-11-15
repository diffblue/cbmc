/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive bitvector analysis

#include "custom_bitvector_analysis.h"

#include <util/xml_expr.h>
#include <util/simplify_expr.h>

#include <iostream>

void custom_bitvector_domaint::set_bit(
  const irep_idt &identifier,
  unsigned bit_nr,
  modet mode)
{
  switch(mode)
  {
  case modet::SET_MUST:
    set_bit(must_bits[identifier], bit_nr);
    break;

  case modet::CLEAR_MUST:
    clear_bit(must_bits[identifier], bit_nr);
    break;

  case modet::SET_MAY:
    set_bit(may_bits[identifier], bit_nr);
    break;

  case modet::CLEAR_MAY:
    clear_bit(may_bits[identifier], bit_nr);
    break;
  }
}

void custom_bitvector_domaint::set_bit(
  const exprt &lhs,
  unsigned bit_nr,
  modet mode)
{
  irep_idt id=object2id(lhs);
  if(!id.empty())
    set_bit(id, bit_nr, mode);
}

irep_idt custom_bitvector_domaint::object2id(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    return to_symbol_expr(src).get_identifier();
  }
  else if(src.id()==ID_dereference)
  {
    const exprt &op=to_dereference_expr(src).pointer();

    if(op.id()==ID_address_of)
    {
      return object2id(to_address_of_expr(op).object());
    }
    else if(op.id()==ID_typecast)
    {
      irep_idt op_id=object2id(to_typecast_expr(op).op());

      if(op_id.empty())
        return irep_idt();
      else
        return '*'+id2string(op_id);
    }
    else
    {
      irep_idt op_id=object2id(op);

      if(op_id.empty())
        return irep_idt();
      else
        return '*'+id2string(op_id);
    }
  }
  else if(src.id()==ID_member)
  {
    const auto &m=to_member_expr(src);
    const exprt &op=m.compound();

    irep_idt op_id=object2id(op);

    if(op_id.empty())
      return irep_idt();
    else
      return id2string(op_id)+'.'+
             id2string(m.get_component_name());
  }
  else if(src.id()==ID_typecast)
    return object2id(to_typecast_expr(src).op());
  else
    return irep_idt();
}

void custom_bitvector_domaint::assign_lhs(
  const exprt &lhs,
  const vectorst &vectors)
{
  irep_idt id=object2id(lhs);
  if(!id.empty())
    assign_lhs(id, vectors);
}

void custom_bitvector_domaint::assign_lhs(
  const irep_idt &identifier,
  const vectorst &vectors)
{
  // we erase blank ones to avoid noise

  if(vectors.must_bits==0)
    must_bits.erase(identifier);
  else
    must_bits[identifier]=vectors.must_bits;

  if(vectors.may_bits==0)
    may_bits.erase(identifier);
  else
    may_bits[identifier]=vectors.may_bits;
}

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const irep_idt &identifier) const
{
  vectorst vectors;

  bitst::const_iterator may_it=may_bits.find(identifier);
  if(may_it!=may_bits.end())
    vectors.may_bits=may_it->second;

  bitst::const_iterator must_it=must_bits.find(identifier);
  if(must_it!=must_bits.end())
    vectors.must_bits=must_it->second;

  return vectors;
}

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const exprt &rhs) const
{
  if(rhs.id()==ID_symbol ||
     rhs.id()==ID_dereference)
  {
    const irep_idt identifier=object2id(rhs);
    return get_rhs(identifier);
  }
  else if(rhs.id()==ID_typecast)
  {
    return get_rhs(to_typecast_expr(rhs).op());
  }
  else if(rhs.id()==ID_if)
  {
    // need to merge both
    vectorst v_true=get_rhs(to_if_expr(rhs).true_case());
    vectorst v_false=get_rhs(to_if_expr(rhs).false_case());
    return merge(v_true, v_false);
  }

  return vectorst();
}

unsigned custom_bitvector_analysist::get_bit_nr(
  const exprt &string_expr)
{
  if(string_expr.id()==ID_typecast)
    return get_bit_nr(to_typecast_expr(string_expr).op());
  else if(string_expr.id()==ID_address_of)
    return get_bit_nr(to_address_of_expr(string_expr).object());
  else if(string_expr.id()==ID_index)
    return get_bit_nr(to_index_expr(string_expr).array());
  else if(string_expr.id()==ID_string_constant)
  {
    irep_idt value=string_expr.get(ID_value);
    return bits(value);
  }
  else
    return bits("(unknown)");
}

std::set<exprt> custom_bitvector_analysist::aliases(
  const exprt &src,
  locationt loc)
{
  if(src.id()==ID_symbol)
  {
    std::set<exprt> result;
    result.insert(src);
    return result;
  }
  else if(src.id()==ID_dereference)
  {
    exprt pointer=to_dereference_expr(src).pointer();

    std::set<exprt> pointer_set=
      local_may_alias_factory(loc).get(loc, pointer);

    std::set<exprt> result;

    for(const auto &pointer : pointer_set)
      if(pointer.type().id()==ID_pointer)
        result.insert(dereference_exprt(pointer));

    result.insert(src);

    return result;
  }
  else if(src.id()==ID_typecast)
  {
    return aliases(to_typecast_expr(src).op(), loc);
  }
  else
    return std::set<exprt>();
}

void custom_bitvector_domaint::assign_struct_rec(
  locationt from,
  const exprt &lhs,
  const exprt &rhs,
  custom_bitvector_analysist &cba,
  const namespacet &ns)
{
  if(ns.follow(lhs.type()).id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(ns.follow(lhs.type()));

    // assign member-by-member
    for(const auto &c : struct_type.components())
    {
      member_exprt lhs_member(lhs, c),
                   rhs_member(rhs, c);
      assign_struct_rec(from, lhs_member, rhs_member, cba, ns);
    }
  }
  else
  {
    // may alias other stuff
    std::set<exprt> lhs_set=cba.aliases(lhs, from);

    vectorst rhs_vectors=get_rhs(rhs);

    for(const auto &lhs_alias : lhs_set)
    {
      assign_lhs(lhs_alias, rhs_vectors);
    }

    // is it a pointer?
    if(lhs.type().id()==ID_pointer)
    {
      dereference_exprt lhs_deref(lhs);
      dereference_exprt rhs_deref(rhs);
      vectorst rhs_vectors=get_rhs(rhs_deref);
      assign_lhs(lhs_deref, rhs_vectors);
    }
  }
}

void custom_bitvector_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  // upcast of ai
  custom_bitvector_analysist &cba=
    static_cast<custom_bitvector_analysist &>(ai);

  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);
      assign_struct_rec(from, code_assign.lhs(), code_assign.rhs(), cba, ns);
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      assign_lhs(code_decl.symbol(), vectorst());

      // is it a pointer?
      if(code_decl.symbol().type().id()==ID_pointer)
        assign_lhs(dereference_exprt(code_decl.symbol()), vectorst());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      assign_lhs(code_dead.symbol(), vectorst());

      // is it a pointer?
      if(code_dead.symbol().type().id()==ID_pointer)
        assign_lhs(dereference_exprt(code_dead.symbol()), vectorst());
    }
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code_function_call=
        to_code_function_call(instruction.code);
      const exprt &function=code_function_call.function();

      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=to_symbol_expr(function).get_identifier();

        if(identifier=="__CPROVER_set_must" ||
           identifier=="__CPROVER_clear_must" ||
           identifier=="__CPROVER_set_may" ||
           identifier=="__CPROVER_clear_may")
        {
          if(code_function_call.arguments().size()==2)
          {
            unsigned bit_nr=
              cba.get_bit_nr(code_function_call.arguments()[1]);

            modet mode;

            if(identifier=="__CPROVER_set_must")
              mode=modet::SET_MUST;
            else if(identifier=="__CPROVER_clear_must")
              mode=modet::CLEAR_MUST;
            else if(identifier=="__CPROVER_set_may")
              mode=modet::SET_MAY;
            else if(identifier=="__CPROVER_clear_may")
              mode=modet::CLEAR_MAY;
            else
              UNREACHABLE;

            exprt lhs=code_function_call.arguments()[0];

            if(lhs.type().id()==ID_pointer)
            {
              if(lhs.is_constant() &&
                 to_constant_expr(lhs).get_value()==ID_NULL) // NULL means all
              {
                if(mode==modet::CLEAR_MAY)
                {
                  for(auto &bit : may_bits)
                    clear_bit(bit.second, bit_nr);

                  // erase blank ones
                  erase_blank_vectors(may_bits);
                }
                else if(mode==modet::CLEAR_MUST)
                {
                  for(auto &bit : must_bits)
                    clear_bit(bit.second, bit_nr);

                  // erase blank ones
                  erase_blank_vectors(must_bits);
                }
              }
              else
              {
                dereference_exprt deref(lhs);

                // may alias other stuff
                std::set<exprt> lhs_set=cba.aliases(deref, from);

                for(const auto &lhs : lhs_set)
                {
                  set_bit(lhs, bit_nr, mode);
                }
              }
            }
          }
        }
        else if(identifier=="memcpy" ||
                identifier=="memmove")
        {
          if(code_function_call.arguments().size()==3)
          {
            // we copy all tracked bits from op1 to op0
            // we do not consider any bits attached to the size op2
            dereference_exprt lhs_deref(code_function_call.arguments()[0]);
            dereference_exprt rhs_deref(code_function_call.arguments()[1]);

            assign_struct_rec(from, lhs_deref, rhs_deref, cba, ns);
          }
        }
        else
        {
          goto_programt::const_targett next=from;
          ++next;

          // only if there is an actual call, i.e., we have a body
          if(next!=to)
          {
            const code_typet &code_type=
              to_code_type(ns.lookup(identifier).type);

            code_function_callt::argumentst::const_iterator arg_it=
              code_function_call.arguments().begin();
            for(const auto &param : code_type.parameters())
            {
              const irep_idt &p_identifier=param.get_identifier();
              if(p_identifier.empty())
                continue;

              // there may be a mismatch in the number of arguments
              if(arg_it==code_function_call.arguments().end())
                break;

              // assignments arguments -> parameters
              symbol_exprt p=ns.lookup(p_identifier).symbol_expr();
              // may alias other stuff
              std::set<exprt> lhs_set=cba.aliases(p, from);

              vectorst rhs_vectors=get_rhs(*arg_it);

              for(const auto &lhs : lhs_set)
              {
                assign_lhs(lhs, rhs_vectors);
              }

              // is it a pointer?
              if(p.type().id()==ID_pointer)
              {
                dereference_exprt lhs_deref(p);
                dereference_exprt rhs_deref(*arg_it);
                vectorst rhs_vectors=get_rhs(rhs_deref);
                assign_lhs(lhs_deref, rhs_vectors);
              }

              ++arg_it;
            }
          }
        }
      }
    }
    break;

  case OTHER:
    {
      const irep_idt &statement=instruction.code.get_statement();

      if(statement=="set_may" ||
         statement=="set_must" ||
         statement=="clear_may" ||
         statement=="clear_must")
      {
        assert(instruction.code.operands().size()==2);

        unsigned bit_nr=
          cba.get_bit_nr(instruction.code.op1());

        modet mode;

        if(statement=="set_must")
          mode=modet::SET_MUST;
        else if(statement=="clear_must")
          mode=modet::CLEAR_MUST;
        else if(statement=="set_may")
          mode=modet::SET_MAY;
        else if(statement=="clear_may")
          mode=modet::CLEAR_MAY;
        else
          UNREACHABLE;

        exprt lhs=instruction.code.op0();

        if(lhs.type().id()==ID_pointer)
        {
          if(lhs.is_constant() &&
             to_constant_expr(lhs).get_value()==ID_NULL) // NULL means all
          {
            if(mode==modet::CLEAR_MAY)
            {
              for(bitst::iterator b_it=may_bits.begin();
                  b_it!=may_bits.end();
                  b_it++)
                clear_bit(b_it->second, bit_nr);

              // erase blank ones
              erase_blank_vectors(may_bits);
            }
            else if(mode==modet::CLEAR_MUST)
            {
              for(bitst::iterator b_it=must_bits.begin();
                  b_it!=must_bits.end();
                  b_it++)
                clear_bit(b_it->second, bit_nr);

              // erase blank ones
              erase_blank_vectors(must_bits);
            }
          }
          else
          {
            dereference_exprt deref(lhs);

            // may alias other stuff
            std::set<exprt> lhs_set=cba.aliases(deref, from);

            for(const auto &lhs : lhs_set)
            {
              set_bit(lhs, bit_nr, mode);
            }
          }
        }
      }
    }
    break;

  case GOTO:
    if(has_get_must_or_may(instruction.guard))
    {
      exprt guard=instruction.guard;

      if(to!=from->get_target())
        guard.make_not();

      exprt result=eval(guard, cba);
      exprt result2=simplify_expr(result, ns);

      if(result2.is_false())
        make_bottom();
    }
    break;

  default:
    {
    }
  }
}

void custom_bitvector_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(has_values.is_known())
  {
    out << has_values.to_string() << '\n';
    return;
  }

  const custom_bitvector_analysist &cba=
    static_cast<const custom_bitvector_analysist &>(ai);

  for(const auto &bit : may_bits)
  {
    out << bit.first << " MAY:";
    bit_vectort b=bit.second;

    for(unsigned i=0; b!=0; i++, b>>=1)
      if(b&1)
      {
        assert(i<cba.bits.size());
        out << ' '
            << cba.bits[i];
      }

    out << '\n';
  }

  for(const auto &bit : must_bits)
  {
    out << bit.first << " MUST:";
    bit_vectort b=bit.second;

    for(unsigned i=0; b!=0; i++, b>>=1)
      if(b&1)
      {
        assert(i<cba.bits.size());
        out << ' '
            << cba.bits[i];
      }

    out << '\n';
  }
}

bool custom_bitvector_domaint::merge(
  const custom_bitvector_domaint &b,
  locationt from,
  locationt to)
{
  bool changed=has_values.is_false();
  has_values=tvt::unknown();

  // first do MAY
  bitst::iterator it=may_bits.begin();
  for(const auto &bit : b.may_bits)
  {
    while(it!=may_bits.end() && it->first<bit.first)
      ++it;
    if(it==may_bits.end() || bit.first<it->first)
    {
      may_bits.insert(it, bit);
      changed=true;
    }
    else if(it!=may_bits.end())
    {
      bit_vectort &a_bits=it->second;
      bit_vectort old=a_bits;
      a_bits|=bit.second;
      if(old!=a_bits)
        changed=true;

      ++it;
    }
  }

  // now do MUST
  it=must_bits.begin();
  for(auto &bit : b.must_bits)
  {
    while(it!=must_bits.end() && it->first<bit.first)
    {
      it=must_bits.erase(it);
      changed=true;
    }
    if(it==must_bits.end() || bit.first<it->first)
    {
      must_bits.insert(it, bit);
      changed=true;
    }
    else if(it!=must_bits.end())
    {
      bit_vectort &a_bits=it->second;
      bit_vectort old=a_bits;
      a_bits&=bit.second;
      if(old!=a_bits)
        changed=true;

      ++it;
    }
  }

  // erase blank ones
  erase_blank_vectors(may_bits);
  erase_blank_vectors(must_bits);

  return changed;
}

/// erase blank bitvectors
void custom_bitvector_domaint::erase_blank_vectors(bitst &bits)
{
  for(bitst::iterator a_it=bits.begin();
      a_it!=bits.end();
     ) // no a_it++
  {
    if(a_it->second==0)
      a_it=bits.erase(a_it);
    else
      a_it++;
  }
}

bool custom_bitvector_domaint::has_get_must_or_may(const exprt &src)
{
  if(src.id()=="get_must" ||
     src.id()=="get_may")
    return true;

  forall_operands(it, src)
    if(has_get_must_or_may(*it))
      return true;

  return false;
}

exprt custom_bitvector_domaint::eval(
  const exprt &src,
  custom_bitvector_analysist &custom_bitvector_analysis) const
{
  if(src.id()=="get_must" || src.id()=="get_may")
  {
    if(src.operands().size()==2)
    {
      unsigned bit_nr=
        custom_bitvector_analysis.get_bit_nr(src.op1());

      exprt pointer=src.op0();

      if(pointer.type().id()!=ID_pointer)
        return src;

      if(pointer.is_constant() &&
         to_constant_expr(pointer).get_value()==ID_NULL) // NULL means all
      {
        if(src.id()=="get_may")
        {
          for(const auto &bit : may_bits)
            if(get_bit(bit.second, bit_nr))
              return true_exprt();

          return false_exprt();
        }
        else if(src.id()=="get_must")
        {
          return false_exprt();
        }
        else
          return src;
      }
      else
      {
        custom_bitvector_domaint::vectorst v=
          get_rhs(dereference_exprt(pointer));

        bool value=false;

        if(src.id()=="get_must")
          value=get_bit(v.must_bits, bit_nr);
        else if(src.id()=="get_may")
          value=get_bit(v.may_bits, bit_nr);

        if(value)
          return true_exprt();
        else
          return false_exprt();
      }
    }
    else
      return src;
  }
  else
  {
    exprt tmp=src;
    Forall_operands(it, tmp)
      *it=eval(*it, custom_bitvector_analysis);

    return tmp;
  }
}

void custom_bitvector_analysist::instrument(goto_functionst &)
{
}

void custom_bitvector_analysist::check(
  const goto_modelt &goto_model,
  bool use_xml,
  std::ostream &out)
{
  unsigned pass=0, fail=0, unknown=0;

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body.has_assertion())
       continue;

    // TODO this is a hard-coded hack
    if(f_it->first=="__actual_thread_spawn")
      continue;

    if(!use_xml)
      out << "******** Function " << f_it->first << '\n';

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      exprt result;
      irep_idt description;

      if(i_it->is_assert())
      {
        if(!custom_bitvector_domaint::has_get_must_or_may(i_it->guard))
          continue;

        if(operator[](i_it).has_values.is_false())
          continue;

        exprt tmp=eval(i_it->guard, i_it);
        const namespacet ns(goto_model.symbol_table);
        result=simplify_expr(tmp, ns);

        description=i_it->source_location.get_comment();
      }
      else
        continue;

      if(use_xml)
      {
        out << "<result status=\"";
        if(result.is_true())
          out << "SUCCESS";
        else if(result.is_false())
          out << "FAILURE";
        else
          out << "UNKNOWN";
        out << "\">\n";
        out << xml(i_it->source_location);
        out << "<description>"
            << description
            << "</description>\n";
        out << "</result>\n\n";
      }
      else
      {
        out << i_it->source_location;
        if(!description.empty())
          out << ", " << description;
        out << ": ";
        const namespacet ns(goto_model.symbol_table);
        out << from_expr(ns, f_it->first, result);
        out << '\n';
      }

      if(result.is_true())
        pass++;
      else if(result.is_false())
        fail++;
      else
        unknown++;
    }

    if(!use_xml)
      out << '\n';
  }

  if(!use_xml)
    out << "SUMMARY: " << pass << " pass, " << fail << " fail, "
        << unknown << " unknown\n";
}
