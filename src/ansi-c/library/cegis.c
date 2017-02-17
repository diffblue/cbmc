/* FUNCTION: __CPROVER_danger_execute */

#ifndef __CPROVER_cegis_number_of_vars
#define __CPROVER_cegis_number_of_vars 2
#endif
#ifndef __CPROVER_cegis_number_of_consts
#define __CPROVER_cegis_number_of_consts 1
#endif
#ifndef __CPROVER_cegis_number_of_ops
#define __CPROVER_cegis_number_of_ops 3
#endif
#ifndef __CPROVER_cegis_max_solution_size
#define __CPROVER_cegis_max_solution_size 1
#endif

const void *__CPROVER_cegis_OPS[__CPROVER_cegis_number_of_ops];
void *__CPROVER_cegis_RESULT_OPS[__CPROVER_cegis_max_solution_size];

typedef unsigned char opcodet;
typedef unsigned char opt;
struct __CPROVER_cegis_instructiont
{
  opcodet opcode;
  opt op0;
  opt op1;
  opt op2;
};

#define __CPROVER_cegis_max_instruction 24u

void __CPROVER_danger_execute(struct __CPROVER_cegis_instructiont *program,
                              unsigned char size)
{
  for (unsigned char i = 0; i < size; ++i)
  {
#define opcode program[i].opcode
    __CPROVER_assume(opcode <= __CPROVER_cegis_max_instruction);
    const unsigned int op0_id=program[i].op0;
    const unsigned int op1_id=program[i].op1;
    const unsigned int op2_id=program[i].op2;
    const unsigned int max_op_index=__CPROVER_cegis_number_of_vars + i;
    __CPROVER_assume(op0_id < max_op_index && op1_id < max_op_index && op2_id < max_op_index
        && (op0_id >= __CPROVER_cegis_number_of_consts || op1_id >= __CPROVER_cegis_number_of_consts  || op2_id >= __CPROVER_cegis_number_of_consts)
        && (opcode > 5u || op0_id <= op1_id) && (opcode < 21u || !op1_id)
        && (opcode == 9u || !op2_id)
        && (opcode != 9u || op0_id != op2_id || op1_id <= op2_id));
    const unsigned int * const op0_ptr=__CPROVER_cegis_OPS[op0_id];
    const unsigned int * const op1_ptr=__CPROVER_cegis_OPS[op1_id];
    const unsigned int * const op2_ptr=__CPROVER_cegis_OPS[op2_id];
    __CPROVER_assume(op0_ptr && op1_ptr && op2_ptr);  // No null pointers in op array
    const unsigned int op0=*op0_ptr;
    const unsigned int op1=*op1_ptr;
    __CPROVER_assume((opcode != 19 && opcode != 20) || op1); // Avoid div by 0.
    const unsigned int op2=*op2_ptr;
#define sop0 ((int) op0)
#define sop1 ((int) op1)
#define sop2 ((int) op2)

    unsigned int result;
    if (opcode < 15)
      if (opcode < 7)
        if (opcode < 3)
          if (opcode < 1)
    __CPROVER_cegis_opcode_0: result=op0 + op1;
          else if (opcode < 2)
    __CPROVER_cegis_opcode_1: result=op0 * op1;
          else
    __CPROVER_cegis_opcode_2: result=op0 &op1;
        else
          if (opcode < 5)
            if  (opcode < 4)
    __CPROVER_cegis_opcode_3: result=op0 | op1;
            else
    __CPROVER_cegis_opcode_4: result=op0 ^ op1;
          else if (opcode < 6)
    __CPROVER_cegis_opcode_5: result=op0 != op1;
            else
    __CPROVER_cegis_opcode_6: result=!op0 || op1;
      else
        if (opcode < 11)
          if (opcode < 9)
            if (opcode < 8)
    {
    __CPROVER_cegis_opcode_first_7: result=op0 < op1;
    if (result) result=op0;
    else __CPROVER_cegis_opcode_last_7: result=op1;
    }
            else
    {
    __CPROVER_cegis_opcode_first_8: result=op0 > op1;
    if (result) result=op0;
    else __CPROVER_cegis_opcode_last_8: result=op1;
    }
          else if (opcode < 10)
    {
    __CPROVER_cegis_opcode_first_9: if (op0) result=op1;
    else __CPROVER_cegis_opcode_last_9: result=op2;
    }
          else
    __CPROVER_cegis_opcode_10: result=op0 - op1;
        else
          if (opcode < 13)
            if (opcode < 12)
            {
    __CPROVER_cegis_opcode_first_11: result=op1;
    //result%=sizeof(op0);
    result%=32u;
    __CPROVER_cegis_opcode_last_11: result=op0 << result;
            }
            else
            {
    __CPROVER_cegis_opcode_first_12:  result=op1;
    //result%=sizeof(op0);
    result%=32u;
    __CPROVER_cegis_opcode_last_12:  result=op0 >> result;
            }
          else if (opcode < 14)
          {
    __CPROVER_cegis_opcode_first_13: result=op1;
    //result%=sizeof(op0);
    result%=32u;
    __CPROVER_cegis_opcode_last_13: result=op0 >> result;
          }
          else
          {
    __CPROVER_cegis_opcode_first_14: result=op1;
    //result%=sizeof(op0);
    result%=32u;
    __CPROVER_cegis_opcode_last_14: result=sop0 >> result;
          }
    else if (opcode < 19)
      if (opcode < 17)
        if (opcode < 16)
    __CPROVER_cegis_opcode_15: result=op0 <= op1;
        else
    __CPROVER_cegis_opcode_16: result=op0 < op1;
      else if (opcode < 18)
    __CPROVER_cegis_opcode_17: result=sop0 <= sop1;
      else
    __CPROVER_cegis_opcode_18: result=sop0 < sop1;
    else if (opcode < 23)
      if (opcode < 21)
        if (opcode < 20)
    __CPROVER_cegis_opcode_19: result=op0 / op1;
        else
    __CPROVER_cegis_opcode_20: result=op0 % op1;
      else if (opcode < 22)
    __CPROVER_cegis_opcode_21: result=-op0;
      else
    __CPROVER_cegis_opcode_22: result=~op0;
    else if (opcode < 24)
    //__CPROVER_cegis_opcode_23: result=0u;
    __CPROVER_cegis_opcode_23: result=sop0 == -1;
    else
      __CPROVER_cegis_opcode_24: result=op0;
    //__CPROVER_cegis_opcode_24: result=sop0 != -1;

    *(unsigned int *)__CPROVER_cegis_RESULT_OPS[i]=result;
  }
}
