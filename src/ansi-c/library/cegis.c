/* FUNCTION: __CPROVER_synthesis_execute */

typedef unsigned char __CPROVER_synthesis_opcodet;
typedef __CPROVER_synthesis_opcodet __CPROVER_synthesis_opt;
struct __CPROVER_synthesis_instructiont
{
  __CPROVER_synthesis_opcodet opcode;
  __CPROVER_synthesis_opt op0;
  __CPROVER_synthesis_opt op1;
  __CPROVER_synthesis_opt op2;
};

#define __CPROVER_synthesis_num_instrs 4u
#define __CPROVER_synthesis_max_vars 10u // TODO: Make dependent on prog size
unsigned int __CPROVER_synthesis_num_vars;
unsigned int __CPROVER_synthesis_offset_readonly;
unsigned int __CPROVER_synthesis_offset_skolem;
unsigned int __CPROVER_synthesis_offset_ranking;
unsigned int __CPROVER_synthesis_offset_writeonly;
const void *__CPROVER_synthesis_vars[__CPROVER_synthesis_max_vars];
// { skolem1, skolem2, ..., rank1, rank2, ..., wo1, wo2, ... rw1, rw2, ..., ro1, ro2, ... }
//                       SKO          RKO             WO            RO

#define __CPROVER_assume_input_op_valid(op) __CPROVER_assume(op < __CPROVER_synthesis_num_vars && op >= __CPROVER_synthesis_offset_writeonly)
#define OP(type, id) *((type *)__CPROVER_synthesis_vars[id])
#define INT_OP(id) OP(int, id)

// TODO: Refactor to actual function arguments!
unsigned int __CPROVER_synthesis_execute_prog_size;
struct __CPROVER_synthesis_instructiont *__CPROVER_synthesis_execute_prog;
int __CPROVER_synthesis_execute_is_skolem;
int __CPROVER_synthesis_execute_is_ranking;
// TODO: Refactor to actual function arguments!

//void __CPROVER_synthesis_execute(unsigned int prog_size, struct __CPROVER_synthesis_instructiont *prog)
void __CPROVER_synthesis_execute()
{
#define prog_size __CPROVER_synthesis_execute_prog_size
#define prog __CPROVER_synthesis_execute_prog
#define is_skolem __CPROVER_synthesis_execute_is_skolem
#define is_ranking __CPROVER_synthesis_execute_is_ranking
  for (unsigned int i=0; i < prog_size; ++i)
  {
    const __CPROVER_synthesis_opcodet opcode=prog[i].opcode;
    __CPROVER_assume(opcode < __CPROVER_synthesis_num_instrs);
    const __CPROVER_synthesis_opt op0=prog[i].op0;
    __CPROVER_assume_input_op_valid(op0);
    const __CPROVER_synthesis_opt op1=prog[i].op1;
    __CPROVER_assume_input_op_valid(op1);
    const __CPROVER_synthesis_opt op2=prog[i].op2;
    __CPROVER_assume(op2 < __CPROVER_synthesis_offset_readonly);
    __CPROVER_assume(is_ranking || is_skolem || op2 >= __CPROVER_synthesis_offset_ranking);
    __CPROVER_assume(!is_ranking || (op2 >= __CPROVER_synthesis_offset_skolem && op2 < __CPROVER_synthesis_offset_ranking) || op2 >= __CPROVER_synthesis_offset_writeonly);
    __CPROVER_assume(!is_skolem || op2 < __CPROVER_synthesis_offset_skolem || op2 >= __CPROVER_synthesis_offset_writeonly);
    switch (opcode)
    {
    case 0: // INT_PLUS
      INT_OP(op2)=INT_OP(op0) + INT_OP(op1);
      break;
    case 1: // INT_MINUS
      INT_OP(op2)=INT_OP(op0) - INT_OP(op1);
      break;
    case 2: // INT_LT
      INT_OP(op2)=INT_OP(op0) < INT_OP(op1);
      break;
    case 3: // INT_LE
      INT_OP(op2)=INT_OP(op0) <= INT_OP(op1);
      break;
    case 4: // NOOP
      break;
    }
  }
}
