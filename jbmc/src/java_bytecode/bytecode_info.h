/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H
#define CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H

#include <cstdint>

// http://en.wikipedia.org/wiki/Java_bytecode_instruction_listings

// The 'result_type' is one of the following:
// i  integer
// l  long
// s  short
// b  byte
// c  character
// f  float
// d  double
// z  boolean
// a  reference

// The 'format' is:
// ' ' - just one byte
// 'c' - a constant_pool index, one byte
// 'C' - a constant_pool index, two bytes
// 'b' - a byte, signed
// 'o' - two byte branch offset
// 'O' - four byte branch offset
// 'v' - local variable index, one byte
// 'V' - local variable index, one byte, plus one byte, signed
// 'I' - two byte constant_pool index, plus two bytes
// 'L' - lookupswitch
// 'T' - tableswitch
// 'm' - multianewarray
// 't' - array subtype, one byte
// 's' - a short, signed

struct bytecode_infot
{
  const char *mnemonic;
  unsigned char opcode;
  char format;
  unsigned pop, push;
  char result_type;
};

extern struct bytecode_infot const bytecode_info[];

typedef uint8_t  u1; // NOLINT(readability/identifiers)
typedef uint16_t u2; // NOLINT(readability/identifiers)
typedef uint32_t u4; // NOLINT(readability/identifiers)
typedef uint64_t u8; // NOLINT(readability/identifiers)
typedef int8_t  s1; // NOLINT(readability/identifiers)
typedef int16_t s2; // NOLINT(readability/identifiers)
typedef int32_t s4; // NOLINT(readability/identifiers)
typedef int64_t s8; // NOLINT(readability/identifiers)

// clang-format off
#define BC_nop             0x00
#define BC_aconst_null     0x01
#define BC_iconst_m1       0x02
#define BC_iconst_0        0x03
#define BC_iconst_1        0x04
#define BC_iconst_2        0x05
#define BC_iconst_3        0x06
#define BC_iconst_4        0x07
#define BC_iconst_5        0x08
#define BC_lconst_0        0x09
#define BC_lconst_1        0x0a
#define BC_fconst_0        0x0b
#define BC_fconst_1        0x0c
#define BC_fconst_2        0x0d
#define BC_dconst_0        0x0e
#define BC_dconst_1        0x0f
#define BC_bipush          0x10
#define BC_sipush          0x11
#define BC_ldc             0x12
#define BC_ldc_w           0x13
#define BC_ldc2_w          0x14
#define BC_iload           0x15
#define BC_lload           0x16
#define BC_fload           0x17
#define BC_dload           0x18
#define BC_aload           0x19
#define BC_iload_0         0x1a
#define BC_iload_1         0x1b
#define BC_iload_2         0x1c
#define BC_iload_3         0x1d
#define BC_lload_0         0x1e
#define BC_lload_1         0x1f
#define BC_lload_2         0x20
#define BC_lload_3         0x21
#define BC_fload_0         0x22
#define BC_fload_1         0x23
#define BC_fload_2         0x24
#define BC_fload_3         0x25
#define BC_dload_0         0x26
#define BC_dload_1         0x27
#define BC_dload_2         0x28
#define BC_dload_3         0x29
#define BC_aload_0         0x2a
#define BC_aload_1         0x2b
#define BC_aload_2         0x2c
#define BC_aload_3         0x2d
#define BC_iaload          0x2e
#define BC_laload          0x2f
#define BC_faload          0x30
#define BC_daload          0x31
#define BC_aaload          0x32
#define BC_baload          0x33
#define BC_caload          0x34
#define BC_saload          0x35
#define BC_istore          0x36
#define BC_lstore          0x37
#define BC_fstore          0x38
#define BC_dstore          0x39
#define BC_astore          0x3a
#define BC_istore_0        0x3b
#define BC_istore_1        0x3c
#define BC_istore_2        0x3d
#define BC_istore_3        0x3e
#define BC_lstore_0        0x3f
#define BC_lstore_1        0x40
#define BC_lstore_2        0x41
#define BC_lstore_3        0x42
#define BC_fstore_0        0x43
#define BC_fstore_1        0x44
#define BC_fstore_2        0x45
#define BC_fstore_3        0x46
#define BC_dstore_0        0x47
#define BC_dstore_1        0x48
#define BC_dstore_2        0x49
#define BC_dstore_3        0x4a
#define BC_astore_0        0x4b
#define BC_astore_1        0x4c
#define BC_astore_2        0x4d
#define BC_astore_3        0x4e
#define BC_iastore         0x4f
#define BC_lastore         0x50
#define BC_fastore         0x51
#define BC_dastore         0x52
#define BC_aastore         0x53
#define BC_bastore         0x54
#define BC_castore         0x55
#define BC_sastore         0x56
#define BC_pop             0x57
#define BC_pop2            0x58
#define BC_dup             0x59
#define BC_dup_x1          0x5a
#define BC_dup_x2          0x5b
#define BC_dup2            0x5c
#define BC_dup2_x1         0x5d
#define BC_dup2_x2         0x5e
#define BC_swap            0x5f
#define BC_iadd            0x60
#define BC_ladd            0x61
#define BC_fadd            0x62
#define BC_dadd            0x63
#define BC_isub            0x64
#define BC_lsub            0x65
#define BC_fsub            0x66
#define BC_dsub            0x67
#define BC_imul            0x68
#define BC_lmul            0x69
#define BC_fmul            0x6a
#define BC_dmul            0x6b
#define BC_idiv            0x6c
#define BC_ldiv            0x6d
#define BC_fdiv            0x6e
#define BC_ddiv            0x6f
#define BC_irem            0x70
#define BC_lrem            0x71
#define BC_frem            0x72
#define BC_drem            0x73
#define BC_ineg            0x74
#define BC_lneg            0x75
#define BC_fneg            0x76
#define BC_dneg            0x77
#define BC_ishl            0x78
#define BC_lshl            0x79
#define BC_ishr            0x7a
#define BC_lshr            0x7b
#define BC_iushr           0x7c
#define BC_lushr           0x7d
#define BC_iand            0x7e
#define BC_land            0x7f
#define BC_ior             0x80
#define BC_lor             0x81
#define BC_ixor            0x82
#define BC_lxor            0x83
#define BC_iinc            0x84
#define BC_i2l             0x85
#define BC_i2f             0x86
#define BC_i2d             0x87
#define BC_l2i             0x88
#define BC_l2f             0x89
#define BC_l2d             0x8a
#define BC_f2i             0x8b
#define BC_f2l             0x8c
#define BC_f2d             0x8d
#define BC_d2i             0x8e
#define BC_d2l             0x8f
#define BC_d2f             0x90
#define BC_i2b             0x91
#define BC_i2c             0x92
#define BC_i2s             0x93
#define BC_lcmp            0x94
#define BC_fcmpl           0x95
#define BC_fcmpg           0x96
#define BC_dcmpl           0x97
#define BC_dcmpg           0x98
#define BC_ifeq            0x99
#define BC_ifne            0x9a
#define BC_iflt            0x9b
#define BC_ifge            0x9c
#define BC_ifgt            0x9d
#define BC_ifle            0x9e
#define BC_if_icmpeq       0x9f
#define BC_if_icmpne       0xa0
#define BC_if_icmplt       0xa1
#define BC_if_icmpge       0xa2
#define BC_if_icmpgt       0xa3
#define BC_if_icmple       0xa4
#define BC_if_acmpeq       0xa5
#define BC_if_acmpne       0xa6
#define BC_goto            0xa7
#define BC_jsr             0xa8
#define BC_ret             0xa9
#define BC_tableswitch     0xaa
#define BC_lookupswitch    0xab
#define BC_ireturn         0xac
#define BC_lreturn         0xad
#define BC_freturn         0xae
#define BC_dreturn         0xaf
#define BC_areturn         0xb0
#define BC_return          0xb1
#define BC_getstatic       0xb2
#define BC_putstatic       0xb3
#define BC_getfield        0xb4
#define BC_putfield        0xb5
#define BC_invokevirtual   0xb6
#define BC_invokespecial   0xb7
#define BC_invokestatic    0xb8
#define BC_invokeinterface 0xb9
#define BC_invokedynamic   0xba
#define BC_new             0xbb
#define BC_newarray        0xbc
#define BC_anewarray       0xbd
#define BC_arraylength     0xbe
#define BC_athrow          0xbf
#define BC_checkcast       0xc0
#define BC_instanceof      0xc1
#define BC_monitorenter    0xc2
#define BC_monitorexit     0xc3
#define BC_wide            0xc4
#define BC_multianewarray  0xc5
#define BC_ifnull          0xc6
#define BC_ifnonnull       0xc7
#define BC_goto_w          0xc8
#define BC_jsr_w           0xc9
#define BC_breakpoint      0xca
#define BC_impdep1         0xfe
#define BC_impdep2         0xff
// clang-format on

#endif // CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H
