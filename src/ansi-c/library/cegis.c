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
unsigned int __CPROVER_synthesis_readonly_offset;
const void *__CPROVER_synthesis_vars[__CPROVER_synthesis_max_vars];

#define __CPROVER_assume_opcode_valid(opcode) __CPROVER_assume(opcode < __CPROVER_synthesis_num_instrs);
#define __CPROVER_assume_op_valid(op) __CPROVER_assume(op < __CPROVER_synthesis_num_vars)
#define OP(type, id) *((type *)__CPROVER_synthesis_vars[id])
#define INT_OP(id) OP(int, id)

unsigned int __CPROVER_synthesis_execute_prog_size;
struct __CPROVER_synthesis_instructiont *__CPROVER_synthesis_execute_prog;

//void __CPROVER_synthesis_execute(unsigned int prog_size, struct __CPROVER_synthesis_instructiont *prog)
void __CPROVER_synthesis_execute()
{
#define prog_size __CPROVER_synthesis_execute_prog_size
#define prog __CPROVER_synthesis_execute_prog
  for (unsigned int i=0; i < prog_size; ++i)
  {
    const __CPROVER_synthesis_opcodet opcode=prog[i].opcode;
    __CPROVER_assume_opcode_valid(opcode);
    const __CPROVER_synthesis_opt op0=prog[i].op0;
    __CPROVER_assume_op_valid(op0);
    const __CPROVER_synthesis_opt op1=prog[i].op1;
    __CPROVER_assume_op_valid(op1);
    const __CPROVER_synthesis_opt op2=prog[i].op2;
    __CPROVER_assume(op2 < __CPROVER_synthesis_readonly_offset);
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
    case 3: // INT_GT
      INT_OP(op2)=INT_OP(op0) > INT_OP(op1);
      break;
    case 4: // NOOP
      break;
    }
  }
}
