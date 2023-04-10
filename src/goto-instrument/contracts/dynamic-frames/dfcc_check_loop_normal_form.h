/*******************************************************************\

Module: Dynamic frame condition checking for loop contracts

Author: Qinheping Hu, qinhh@amazon.com
Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Checks normal form properties of natural loops in a GOTO program.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CHECK_LOOP_NORMAL_FORM_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CHECK_LOOP_NORMAL_FORM_H

class goto_programt;
class messaget;

/// \brief Checks and enforces normal form properties for natural loops of the
/// given \p goto_program.
///
/// If and when the function succeeds, the following properties are established
/// for each natural loop.
///
/// The loop has either a single instruction:
///
/// ```c
/// START: IF expr GOTO START;
/// ```
///
/// OR
///
/// The loop has two or more instructions and:
/// 1. has a unique head instruction;
/// 2. has a unique, unconditional GOTO latch instruction;
/// 3. has a pre-head SKIP instruction that is not part of the loop;
/// 4. the head has two incoming edges from the pre-head and the latch;
/// 5. for all instructions but the head, incoming edges are from instructions
///    in the same loop;
/// 6. all instructions of the loop are found between the head and the latch in
///    the instruction sequence;
/// 7. The span of instructions of any two loops are either nested or disjoint.
///
/// \remark The goto program will be modified by the addition of the pre-head
/// SKIP instructions, and by the rewriting of conditional latch instructions
/// into conditional exit jump + unconditional backjump.
void dfcc_check_loop_normal_form(goto_programt &goto_program, messaget &log);

#endif
