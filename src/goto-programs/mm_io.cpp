/*******************************************************************\

Module: Perform Memory-mapped I/O instrumentation

Author: Daniel Kroening

Date:   April 2017

\*******************************************************************/

/// \file
/// Perform Memory-mapped I/O instrumentation

#include "mm_io.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include "goto_model.h"

#include <set>

/// Implements MMIO instrumentation for a single function.
/// Supports both the legacy callback model (when \p regions is empty)
/// and the per-region object model (when \p regions is non-empty).
class mm_iot
{
public:
  explicit mm_iot(
    symbol_table_baset &symbol_table,
    const std::vector<mmio_regiont> &_regions = {});

  void mm_io(goto_functionst::goto_functiont &goto_function);

  std::size_t reads_replaced = 0;
  std::size_t writes_replaced = 0;

protected:
  const irep_idt id_r = CPROVER_PREFIX "mm_io_r";
  const irep_idt id_w = CPROVER_PREFIX "mm_io_w";

  const namespacet ns;
  exprt mm_io_r;
  exprt mm_io_r_value;
  exprt mm_io_w;

  // Per-region object model
  const std::vector<mmio_regiont> regions;
  symbol_table_baset &symbol_table;

  /// Return an expression that reads the MMIO region object at \p address.
  /// If \p address simplifies to a constant that falls within a known region,
  /// returns a direct `index_exprt` into that region's array. Otherwise
  /// delegates to \ref build_conditional_access.
  exprt get_mmio_object_for_address(
    const exprt &address,
    const typet &value_type,
    const source_locationt &location);

  /// Build an if-then-else chain over all MMIO regions for a symbolic
  /// \p address. The default (no region matches) is a nondet value.
  exprt build_conditional_access(
    const exprt &address,
    const typet &value_type,
    const source_locationt &location);

  /// Build a disjunction: address is in region_0 || ... || region_N.
  exprt address_in_some_region(const exprt &address);

  /// Build the in-range condition `address >= start && address < start+size`
  /// for \p region. If the region ends exactly at 2^width (the top of the
  /// address space), the upper bound is omitted, because `from_integer` of
  /// 2^width into the (unsigned) address type wraps to 0 and would otherwise
  /// make the condition unsatisfiable.
  exprt region_contains(const mmio_regiont &region, const exprt &address);

  /// Read a value of \p value_type from \p region_symbol's backing byte array
  /// starting at byte \p offset. The access spans ceil(width/8) consecutive
  /// bytes via a `byte_extract` that honours the configured endianness, so
  /// multi-byte MMIO accesses are modelled soundly rather than truncated to a
  /// single byte.
  exprt region_element(
    const symbolt &region_symbol,
    const exprt &offset,
    const typet &value_type);

  /// Replace a write through the dereference \p d (with right-hand side
  /// \p a_rhs) at instruction \p it of \p goto_function with a conditional
  /// dispatch that, for an integer address, stores into the matching region
  /// object (via \ref region_element / byte_update) and otherwise performs the
  /// original write; a fall-through assertion flags addresses outside every
  /// declared region. The original assignment is erased. Returns the
  /// instruction at which iteration should resume.
  goto_programt::targett instrument_region_write(
    goto_functionst::goto_functiont &goto_function,
    goto_programt::targett it,
    const dereference_exprt &d,
    const exprt &a_rhs);
};

mm_iot::mm_iot(
  symbol_table_baset &_symbol_table,
  const std::vector<mmio_regiont> &_regions)
  : ns(_symbol_table),
    mm_io_r(nil_exprt{}),
    mm_io_r_value(nil_exprt{}),
    mm_io_w(nil_exprt{}),
    regions(_regions),
    symbol_table(_symbol_table)
{
  if(const auto mm_io_r_symbol = symbol_table.lookup(id_r))
  {
    mm_io_r = mm_io_r_symbol->symbol_expr();

    mm_io_r_value = get_fresh_aux_symbol(
                      to_code_type(mm_io_r.type()).return_type(),
                      id2string(id_r) + "$value",
                      id2string(id_r) + "$value",
                      mm_io_r_symbol->location,
                      mm_io_r_symbol->mode,
                      symbol_table)
                      .symbol_expr();
  }

  if(const auto mm_io_w_symbol = symbol_table.lookup(id_w))
    mm_io_w = mm_io_w_symbol->symbol_expr();
}

static std::set<dereference_exprt> collect_deref_expr(const exprt &src)
{
  std::set<dereference_exprt> collected;
  src.visit_pre(
    [&collected](const exprt &e)
    {
      if(e.id() == ID_dereference)
        collected.insert(to_dereference_expr(e));
    });
  return collected;
}

goto_programt::targett mm_iot::instrument_region_write(
  goto_functionst::goto_functiont &goto_function,
  goto_programt::targett it,
  const dereference_exprt &d,
  const exprt &a_rhs)
{
  const source_locationt source_location = it->source_location();

  // We build the following structure after the original assignment (which we
  // then erase):
  //
  //   IF !integer_address(ptr) GOTO lbl_orig
  //   IF in_region_0 GOTO lbl_r0
  //   ...
  //   GOTO lbl_end          // not in any known region
  // lbl_r0: region0 = byte_update(region0, off, rhs); GOTO lbl_end
  //   ...
  // lbl_orig: *ptr = rhs; GOTO lbl_end
  // lbl_end: SKIP

  const exprt addr_as_int =
    typecast_exprt::conditional_cast(d.pointer(), size_type());

  // First pass: build region assignments in a temporary program and collect
  // targets for the dispatch GOTOs.
  goto_programt region_code;
  struct region_infot
  {
    exprt condition;
    goto_programt::targett label;
  };
  std::vector<region_infot> region_gotos;

  for(const auto &region : regions)
  {
    const symbolt *sym = symbol_table.lookup(region.object_name);
    if(!sym)
      continue;

    exprt in_range = region_contains(region, addr_as_int);

    minus_exprt offset(
      addr_as_int, from_integer(region.start_address, addr_as_int.type()));

    // Update the bytes [offset, offset + ceil(width/8)) of the region array
    // from the value being written, honouring the configured endianness, and
    // assign the resulting array back to the region. This models multi-byte
    // stores soundly instead of truncating the value to a single byte.
    const exprt region_expr = sym->symbol_expr();
    exprt updated = make_byte_update(region_expr, offset, a_rhs);

    auto lbl_region = region_code.add(goto_programt::make_assignment(
      region_expr, std::move(updated), source_location));

    region_gotos.push_back({std::move(in_range), lbl_region});
  }

  // Original dereference write
  auto lbl_orig =
    region_code.add(goto_programt::make_assignment(d, a_rhs, source_location));

  // lbl_end
  auto lbl_end = region_code.add(goto_programt::make_skip(source_location));

  // Insert GOTO lbl_end after each region assignment and after lbl_orig.
  for(auto ri = region_code.instructions.begin(); ri != lbl_end;)
  {
    if(ri->is_assign())
    {
      auto next_ri = std::next(ri);
      region_code.instructions.insert(
        next_ri, goto_programt::make_goto(lbl_end, source_location));
      ri = next_ri;
    }
    else
      ++ri;
  }

  // Build the dispatch block.
  goto_programt result;

  // Guard: not integer address -> original dereference
  result.add(goto_programt::make_goto(
    lbl_orig, not_exprt(integer_address(d.pointer())), source_location));

  // Conditional jumps to each region
  for(const auto &rg : region_gotos)
  {
    result.add(
      goto_programt::make_goto(rg.label, rg.condition, source_location));
  }

  // Fall-through: integer address not in any declared region
  {
    source_locationt assert_loc = source_location;
    assert_loc.set_property_class("mmio-region");
    assert_loc.set_comment(
      "MMIO write address must be within a declared region");
    result.add(goto_programt::make_assertion(false_exprt(), assert_loc));
    result.add(goto_programt::make_assumption(false_exprt(), source_location));
  }

  // Append region assignments + original + end
  result.destructive_append(region_code);

  // Splice into the function body after `it`, then erase the original
  // assignment. Iteration resumes from lbl_end.
  auto next = std::next(it);
  goto_function.body.destructive_insert(next, result);
  goto_function.body.instructions.erase(it);

  return lbl_end;
}

void mm_iot::mm_io(goto_functionst::goto_functiont &goto_function)
{
  // Use per-region object model if regions are specified
  if(!regions.empty())
  {
    // Instrument with per-region object model
    for(auto it = goto_function.body.instructions.begin();
        it != goto_function.body.instructions.end();
        it++)
    {
      if(!it->is_assign())
        continue;

      auto &a_lhs = it->assign_lhs();
      auto &a_rhs = it->assign_rhs_nonconst();
      const auto deref_expr_r = collect_deref_expr(a_rhs);

      // Handle reads
      if(deref_expr_r.size() == 1)
      {
        const dereference_exprt &d = *deref_expr_r.begin();
        source_locationt source_location = it->source_location();

        exprt addr_as_int =
          typecast_exprt::conditional_cast(d.pointer(), size_type());

        exprt mmio_access =
          get_mmio_object_for_address(addr_as_int, d.type(), source_location);

        if_exprt if_expr(integer_address(d.pointer()), mmio_access, d);

        replace_expr(d, if_expr, a_rhs);

        // Assert that the integer address falls within a declared region
        source_locationt assert_loc = source_location;
        assert_loc.set_property_class("mmio-region");
        assert_loc.set_comment(
          "MMIO read address must be within a declared region");
        goto_programt assert_prog;
        assert_prog.add(goto_programt::make_assertion(
          implies_exprt(
            integer_address(d.pointer()), address_in_some_region(addr_as_int)),
          assert_loc));
        goto_function.body.destructive_insert(it, assert_prog);

        ++reads_replaced;
      }

      // Handle writes (the read instrumentation above only modifies a_rhs,
      // so a_lhs is still the original dereference when both sides deref)
      if(a_lhs.id() == ID_dereference)
      {
        it = instrument_region_write(
          goto_function, it, to_dereference_expr(a_lhs), a_rhs);
        ++writes_replaced;
      }
    }

    return;
  }

  // Original implementation for backward compatibility
  // return early when there is nothing to be done
  if(mm_io_r.is_nil() && mm_io_w.is_nil())
    return;

  for(auto it = goto_function.body.instructions.begin();
      it != goto_function.body.instructions.end();
      it++)
  {
    if(!it->is_assign())
      continue;

    auto &a_lhs = it->assign_lhs();
    auto &a_rhs = it->assign_rhs_nonconst();
    const auto deref_expr_r = collect_deref_expr(a_rhs);

    if(mm_io_r.is_not_nil())
    {
      if(deref_expr_r.size() == 1)
      {
        const dereference_exprt &d = *deref_expr_r.begin();
        source_locationt source_location = it->source_location();
        const code_typet &ct = to_code_type(mm_io_r.type());

        if_exprt if_expr(
          integer_address(d.pointer()),
          typecast_exprt::conditional_cast(mm_io_r_value, d.type()),
          d);
        replace_expr(d, if_expr, a_rhs);

        const typet &pt = ct.parameters()[0].type();
        const typet &st = ct.parameters()[1].type();
        auto size_opt = size_of_expr(d.type(), ns);
        CHECK_RETURN(size_opt.has_value());
        auto call = goto_programt::make_function_call(
          mm_io_r_value,
          mm_io_r,
          {typecast_exprt(d.pointer(), pt),
           typecast_exprt(size_opt.value(), st)},
          source_location);
        goto_function.body.insert_before_swap(it, call);
        ++reads_replaced;
        it++;
      }
    }

    if(mm_io_w.is_not_nil())
    {
      if(a_lhs.id() == ID_dereference)
      {
        const dereference_exprt &d = to_dereference_expr(a_lhs);
        source_locationt source_location = it->source_location();
        const code_typet &ct = to_code_type(mm_io_w.type());
        const typet &pt = ct.parameters()[0].type();
        const typet &st = ct.parameters()[1].type();
        const typet &vt = ct.parameters()[2].type();
        auto size_opt = size_of_expr(d.type(), ns);
        CHECK_RETURN(size_opt.has_value());
        const code_function_callt fc(
          mm_io_w,
          {typecast_exprt(d.pointer(), pt),
           typecast_exprt(size_opt.value(), st),
           typecast_exprt(a_rhs, vt)});
        goto_function.body.insert_before_swap(it);
        *it = goto_programt::make_function_call(fc, source_location);
        ++writes_replaced;
        it++;
      }
    }
  }
}

void mm_io(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  mm_iot rewrite{symbol_table};

  for(auto &f : goto_functions.function_map)
    rewrite.mm_io(f.second);

  if(rewrite.reads_replaced || rewrite.writes_replaced)
  {
    messaget log{message_handler};
    log.status() << "Replaced MMIO operations: " << rewrite.reads_replaced
                 << " read(s), " << rewrite.writes_replaced << " write(s)"
                 << messaget::eom;
  }
}

void mm_io(goto_modelt &model, message_handlert &message_handler)
{
  mm_io(model.symbol_table, model.goto_functions, message_handler);
}

/// Create byte-array symbols in \p symbol_table for each MMIO region.
/// Each symbol is a static-lifetime array of `unsigned char` with size
/// matching the region specification.
void create_mmio_region_objects(
  symbol_tablet &symbol_table,
  const std::vector<mmio_regiont> &regions,
  message_handlert &message_handler)
{
  messaget log{message_handler};

  for(const auto &region : regions)
  {
    // Create a byte array object for this MMIO region
    array_typet array_type(
      unsignedbv_typet(8), from_integer(region.size, size_type()));

    symbolt new_symbol;
    new_symbol.name = region.object_name;
    new_symbol.base_name = region.object_name;
    new_symbol.type = array_type;
    new_symbol.mode = ID_C;
    new_symbol.is_lvalue = true;
    new_symbol.is_state_var = true;
    new_symbol.is_static_lifetime = true;

    if(symbol_table.add(new_symbol))
    {
      log.warning() << "Failed to add MMIO region object: "
                    << region.object_name << messaget::eom;
    }
    else
    {
      log.status() << "Created MMIO region: " << region.object_name
                   << " at address 0x"
                   << integer2string(region.start_address, 16) << " size "
                   << region.size << " bytes" << messaget::eom;
    }
  }
}

exprt mm_iot::get_mmio_object_for_address(
  const exprt &address,
  const typet &value_type,
  const source_locationt &location)
{
  // Simplify to fold typecasts of constants into plain constants
  exprt simplified = simplify_expr(address, ns);

  if(simplified.is_constant())
  {
    mp_integer addr_value;
    if(!to_integer(to_constant_expr(simplified), addr_value))
    {
      // Find the matching MMIO region
      for(const auto &region : regions)
      {
        if(
          addr_value >= region.start_address &&
          addr_value < region.start_address + region.size)
        {
          // Calculate offset within the region
          mp_integer offset = addr_value - region.start_address;

          // Get the symbol for this region
          const symbolt *region_symbol =
            symbol_table.lookup(region.object_name);
          if(region_symbol)
          {
            return region_element(
              *region_symbol, from_integer(offset, c_index_type()), value_type);
          }
        }
      }
    }
  }

  // For symbolic addresses or addresses not in MMIO regions,
  // build conditional access
  return build_conditional_access(address, value_type, location);
}

exprt mm_iot::build_conditional_access(
  const exprt &address,
  const typet &value_type,
  const source_locationt &location)
{
  // Build a chain of if-then-else expressions for each MMIO region
  exprt result = side_effect_expr_nondett(value_type, location);

  for(auto it = regions.rbegin(); it != regions.rend(); ++it)
  {
    const auto &region = *it;

    // Get the symbol for this region
    const symbolt *region_symbol = symbol_table.lookup(region.object_name);
    if(!region_symbol)
      continue;

    // Build condition: address is within this region
    exprt in_range = region_contains(region, address);

    // Calculate offset: address - start_address
    minus_exprt offset_expr(
      address, from_integer(region.start_address, address.type()));

    // Read value_type from the region, spanning consecutive bytes
    exprt region_access =
      region_element(*region_symbol, offset_expr, value_type);

    // Build if-then-else: if (in_range) region[offset] else result
    result = if_exprt(in_range, region_access, result);
  }

  return result;
}

exprt mm_iot::address_in_some_region(const exprt &address)
{
  exprt::operandst disjuncts;
  for(const auto &region : regions)
    disjuncts.push_back(region_contains(region, address));
  return disjunction(disjuncts);
}

exprt mm_iot::region_contains(const mmio_regiont &region, const exprt &address)
{
  const typet &address_type = address.type();
  binary_predicate_exprt lower(
    address, ID_ge, from_integer(region.start_address, address_type));

  const mp_integer end = region.start_address + region.size;
  // A region whose end is exactly 2^width spans the top of the address space.
  // from_integer(2^width, address_type) wraps to 0, which would turn the upper
  // bound into the always-false `address < 0`; omit it, since every value of
  // this unsigned address type already satisfies `address < 2^width`.
  if(end == power(2, to_bitvector_type(address_type).get_width()))
    return std::move(lower);

  binary_predicate_exprt upper(address, ID_lt, from_integer(end, address_type));
  return and_exprt(lower, upper);
}

exprt mm_iot::region_element(
  const symbolt &region_symbol,
  const exprt &offset,
  const typet &value_type)
{
  // The region object is a byte array; extract value_type starting at byte
  // `offset`, spanning ceil(width/8) consecutive bytes. make_byte_extract
  // uses the endianness configured for the analysed program, so multi-byte
  // accesses are modelled with the correct byte order instead of being
  // truncated to a single element.
  return make_byte_extract(region_symbol.symbol_expr(), offset, value_type);
}

void mm_io(
  goto_modelt &model,
  const std::vector<mmio_regiont> &regions,
  message_handlert &message_handler)
{
  // Create MMIO region objects first
  if(!regions.empty())
  {
    create_mmio_region_objects(model.symbol_table, regions, message_handler);
  }

  // Now instrument with the per-region model
  mm_iot rewrite{model.symbol_table, regions};

  for(auto &f : model.goto_functions.function_map)
    rewrite.mm_io(f.second);

  if(rewrite.reads_replaced || rewrite.writes_replaced)
  {
    messaget log{message_handler};
    log.status() << "Replaced MMIO operations: " << rewrite.reads_replaced
                 << " read(s), " << rewrite.writes_replaced << " write(s)"
                 << messaget::eom;
  }
}
