/*******************************************************************\

Module: Group Basic Blocks in Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "basic_blocks.h"

/*******************************************************************\

Function: basic_blocks

  Inputs:

 Outputs:

 Purpose: convert basic blocks into single expressions of type "block"

\*******************************************************************/

void basic_blocks(goto_programt &goto_program,
                  unsigned max_block_size)
{
  // get the targets
  typedef std::set<goto_programt::const_targett> targetst;

  targetst targets;

  for(goto_programt::instructionst::iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
    if(i_it->is_goto())
      for(goto_programt::instructiont::targetst::iterator
          t_it=i_it->targets.begin();
          t_it!=i_it->targets.end();
          t_it++)
        targets.insert(*t_it);

  // Scan program
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      ) // intentionally no it++
  {
    // goto's and empty code are left unchanged
    if(it->is_goto() || it->is_dead() ||
       it->is_assert() || it->is_assume() ||
       it->is_atomic_begin() || it->is_atomic_end() ||
       it->is_end_thread() || it->is_start_thread() ||
       it->is_end_function() || it->is_location() ||
       it->is_skip() || it->is_function_call() ||
       it->is_decl())
      it++;
    else if(it->is_other() || it->is_assign())
    {
      if(it->code.is_nil()) 
        it++;
      else
      {
        unsigned count=0;

        // this is the start of a new block
        targetst::iterator t_it; // iterator for searching targets

        // find the end of the block
        goto_programt::instructionst::iterator end_block = it;
        do
        {
          end_block++;
          count++;
          if(end_block!=goto_program.instructions.end())
            t_it=targets.find(end_block);

          if(max_block_size!=0 && count>=max_block_size)
            break;
        }
        while(end_block!=goto_program.instructions.end() &&
              (end_block->is_other() || end_block->is_assign()) &&
              t_it==targets.end());
              
        // replace it with the code of the block

        {
          code_blockt new_block;

          for(goto_programt::instructionst::iterator stmt = it;
              stmt != end_block;
              stmt++) 
            if(!stmt->code.is_nil())
              new_block.move_to_operands(stmt->code);
          
          it->code.swap(new_block);
          it++;
          if(it!=goto_program.instructions.end())
            it=goto_program.instructions.erase(it, end_block);
        }
      }
    }
    else
      assert(false);
  }
}
