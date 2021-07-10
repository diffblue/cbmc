
#ifndef SAFE_MATH_H
#define SAFE_MATH_H









STATIC int8_t
FUNC_NAME(unary_minus_func_int8_t_s)(int8_t si LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT8_MAX>=INT_MAX)
    (si==INT8_MIN) ?
    (UNDEFINED(si)) :
#endif
#endif
    -si;
}

STATIC int8_t
FUNC_NAME(add_func_int8_t_s_s)(int8_t si1, int8_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT8_MAX>=INT_MAX)
    (((si1>0) && (si2>0) && (si1 > (INT8_MAX-si2))) || ((si1<0) && (si2<0) && (si1 < (INT8_MIN-si2)))) ?
    (UNDEFINED(si1)) :
#endif
#endif
    (si1 + si2);
}

STATIC int8_t
FUNC_NAME(sub_func_int8_t_s_s)(int8_t si1, int8_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT8_MAX>=INT_MAX)
    (((si1^si2) & (((si1 ^ ((si1^si2) & (~INT8_MAX)))-si2)^si2)) < 0) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    (si1 - si2);
}

STATIC int8_t
FUNC_NAME(mul_func_int8_t_s_s)(int8_t si1, int8_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT8_MAX>=INT_MAX)
    (((si1 > 0) && (si2 > 0) && (si1 > (INT8_MAX / si2))) || ((si1 > 0) && (si2 <= 0) && (si2 < (INT8_MIN / si1))) || ((si1 <= 0) && (si2 > 0) && (si1 < (INT8_MIN / si2))) || ((si1 <= 0) && (si2 <= 0) && (si1 != 0) && (si2 < (INT8_MAX / si1)))) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    si1 * si2;
}

STATIC int8_t
FUNC_NAME(mod_func_int8_t_s_s)(int8_t si1, int8_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT8_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 % si2);
}

STATIC int8_t
FUNC_NAME(div_func_int8_t_s_s)(int8_t si1, int8_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT8_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 / si2);
}

STATIC int8_t
FUNC_NAME(lshift_func_int8_t_s_s)(int8_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > (INT8_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC int8_t
FUNC_NAME(lshift_func_int8_t_s_u)(int8_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32) || (left > (INT8_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC int8_t
FUNC_NAME(rshift_func_int8_t_s_s)(int8_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC int8_t
FUNC_NAME(rshift_func_int8_t_s_u)(int8_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}



STATIC int16_t
FUNC_NAME(unary_minus_func_int16_t_s)(int16_t si LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT16_MAX>=INT_MAX)
    (si==INT16_MIN) ?
    (UNDEFINED(si)) :
#endif
#endif
    -si;
}

STATIC int16_t
FUNC_NAME(add_func_int16_t_s_s)(int16_t si1, int16_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT16_MAX>=INT_MAX)
    (((si1>0) && (si2>0) && (si1 > (INT16_MAX-si2))) || ((si1<0) && (si2<0) && (si1 < (INT16_MIN-si2)))) ?
    (UNDEFINED(si1)) :
#endif
#endif
    (si1 + si2);
}

STATIC int16_t
FUNC_NAME(sub_func_int16_t_s_s)(int16_t si1, int16_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT16_MAX>=INT_MAX)
    (((si1^si2) & (((si1 ^ ((si1^si2) & (~INT16_MAX)))-si2)^si2)) < 0) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    (si1 - si2);
}

STATIC int16_t
FUNC_NAME(mul_func_int16_t_s_s)(int16_t si1, int16_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT16_MAX>=INT_MAX)
    (((si1 > 0) && (si2 > 0) && (si1 > (INT16_MAX / si2))) || ((si1 > 0) && (si2 <= 0) && (si2 < (INT16_MIN / si1))) || ((si1 <= 0) && (si2 > 0) && (si1 < (INT16_MIN / si2))) || ((si1 <= 0) && (si2 <= 0) && (si1 != 0) && (si2 < (INT16_MAX / si1)))) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    si1 * si2;
}

STATIC int16_t
FUNC_NAME(mod_func_int16_t_s_s)(int16_t si1, int16_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT16_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 % si2);
}

STATIC int16_t
FUNC_NAME(div_func_int16_t_s_s)(int16_t si1, int16_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT16_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 / si2);
}

STATIC int16_t
FUNC_NAME(lshift_func_int16_t_s_s)(int16_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > (INT16_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC int16_t
FUNC_NAME(lshift_func_int16_t_s_u)(int16_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32) || (left > (INT16_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC int16_t
FUNC_NAME(rshift_func_int16_t_s_s)(int16_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC int16_t
FUNC_NAME(rshift_func_int16_t_s_u)(int16_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}



STATIC int32_t
FUNC_NAME(unary_minus_func_int32_t_s)(int32_t si LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT32_MAX>=INT_MAX)
    (si==INT32_MIN) ?
    (UNDEFINED(si)) :
#endif
#endif
    -si;
}

STATIC int32_t
FUNC_NAME(add_func_int32_t_s_s)(int32_t si1, int32_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT32_MAX>=INT_MAX)
    (((si1>0) && (si2>0) && (si1 > (INT32_MAX-si2))) || ((si1<0) && (si2<0) && (si1 < (INT32_MIN-si2)))) ?
    (UNDEFINED(si1)) :
#endif
#endif
    (si1 + si2);
}

STATIC int32_t
FUNC_NAME(sub_func_int32_t_s_s)(int32_t si1, int32_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT32_MAX>=INT_MAX)
    (((si1^si2) & (((si1 ^ ((si1^si2) & (~INT32_MAX)))-si2)^si2)) < 0) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    (si1 - si2);
}

STATIC int32_t
FUNC_NAME(mul_func_int32_t_s_s)(int32_t si1, int32_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT32_MAX>=INT_MAX)
    (((si1 > 0) && (si2 > 0) && (si1 > (INT32_MAX / si2))) || ((si1 > 0) && (si2 <= 0) && (si2 < (INT32_MIN / si1))) || ((si1 <= 0) && (si2 > 0) && (si1 < (INT32_MIN / si2))) || ((si1 <= 0) && (si2 <= 0) && (si1 != 0) && (si2 < (INT32_MAX / si1)))) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    si1 * si2;
}

STATIC int32_t
FUNC_NAME(mod_func_int32_t_s_s)(int32_t si1, int32_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT32_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 % si2);
}

STATIC int32_t
FUNC_NAME(div_func_int32_t_s_s)(int32_t si1, int32_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT32_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 / si2);
}

STATIC int32_t
FUNC_NAME(lshift_func_int32_t_s_s)(int32_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > (INT32_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC int32_t
FUNC_NAME(lshift_func_int32_t_s_u)(int32_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32) || (left > (INT32_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC int32_t
FUNC_NAME(rshift_func_int32_t_s_s)(int32_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC int32_t
FUNC_NAME(rshift_func_int32_t_s_u)(int32_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}

#ifndef NO_LONGLONG


STATIC int64_t
FUNC_NAME(unary_minus_func_int64_t_s)(int64_t si LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT64_MAX>=INT_MAX)
    (si==INT64_MIN) ?
    (UNDEFINED(si)) :
#endif
#endif
    -si;
}

STATIC int64_t
FUNC_NAME(add_func_int64_t_s_s)(int64_t si1, int64_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT64_MAX>=INT_MAX)
    (((si1>0) && (si2>0) && (si1 > (INT64_MAX-si2))) || ((si1<0) && (si2<0) && (si1 < (INT64_MIN-si2)))) ?
    (UNDEFINED(si1)) :
#endif
#endif
    (si1 + si2);
}

STATIC int64_t
FUNC_NAME(sub_func_int64_t_s_s)(int64_t si1, int64_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT64_MAX>=INT_MAX)
    (((si1^si2) & (((si1 ^ ((si1^si2) & (~INT64_MAX)))-si2)^si2)) < 0) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    (si1 - si2);
}

STATIC int64_t
FUNC_NAME(mul_func_int64_t_s_s)(int64_t si1, int64_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
#if (INT64_MAX>=INT_MAX)
    (((si1 > 0) && (si2 > 0) && (si1 > (INT64_MAX / si2))) || ((si1 > 0) && (si2 <= 0) && (si2 < (INT64_MIN / si1))) || ((si1 <= 0) && (si2 > 0) && (si1 < (INT64_MIN / si2))) || ((si1 <= 0) && (si2 <= 0) && (si1 != 0) && (si2 < (INT64_MAX / si1)))) ? 
    (UNDEFINED(si1)) : 
#endif
#endif
    si1 * si2;
}

STATIC int64_t
FUNC_NAME(mod_func_int64_t_s_s)(int64_t si1, int64_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT64_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 % si2);
}

STATIC int64_t
FUNC_NAME(div_func_int64_t_s_s)(int64_t si1, int64_t si2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((si2 == 0) || ((si1 == INT64_MIN) && (si2 == (-1)))) ? 
    (UNDEFINED(si1)) : 
#endif
    (si1 / si2);
}

STATIC int64_t
FUNC_NAME(lshift_func_int64_t_s_s)(int64_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > (INT64_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC int64_t
FUNC_NAME(lshift_func_int64_t_s_u)(int64_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32) || (left > (INT64_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC int64_t
FUNC_NAME(rshift_func_int64_t_s_s)(int64_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC int64_t
FUNC_NAME(rshift_func_int64_t_s_u)(int64_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((left < 0) || (((unsigned int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}

#endif





STATIC uint8_t
FUNC_NAME(unary_minus_func_uint8_t_u)(uint8_t ui LOG_INDEX)
{
  LOG_EXEC
  return -ui;
}

STATIC uint8_t
FUNC_NAME(add_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 + ui2;
}

STATIC uint8_t
FUNC_NAME(sub_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 - ui2;
}

STATIC uint8_t
FUNC_NAME(mul_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ((unsigned int)ui1) * ((unsigned int)ui2);
}

STATIC uint8_t
FUNC_NAME(mod_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 % ui2);
}

STATIC uint8_t
FUNC_NAME(div_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 / ui2);
}

STATIC uint8_t
FUNC_NAME(lshift_func_uint8_t_u_s)(uint8_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32) || (left > (UINT8_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC uint8_t
FUNC_NAME(lshift_func_uint8_t_u_u)(uint8_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((unsigned int)right) >= 32) || (left > (UINT8_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC uint8_t
FUNC_NAME(rshift_func_uint8_t_u_s)(uint8_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC uint8_t
FUNC_NAME(rshift_func_uint8_t_u_u)(uint8_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (((unsigned int)right) >= 32) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}



STATIC uint16_t
FUNC_NAME(unary_minus_func_uint16_t_u)(uint16_t ui LOG_INDEX)
{
  LOG_EXEC
  return -ui;
}

STATIC uint16_t
FUNC_NAME(add_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 + ui2;
}

STATIC uint16_t
FUNC_NAME(sub_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 - ui2;
}

STATIC uint16_t
FUNC_NAME(mul_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ((unsigned int)ui1) * ((unsigned int)ui2);
}

STATIC uint16_t
FUNC_NAME(mod_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 % ui2);
}

STATIC uint16_t
FUNC_NAME(div_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 / ui2);
}

STATIC uint16_t
FUNC_NAME(lshift_func_uint16_t_u_s)(uint16_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32) || (left > (UINT16_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC uint16_t
FUNC_NAME(lshift_func_uint16_t_u_u)(uint16_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((unsigned int)right) >= 32) || (left > (UINT16_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC uint16_t
FUNC_NAME(rshift_func_uint16_t_u_s)(uint16_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC uint16_t
FUNC_NAME(rshift_func_uint16_t_u_u)(uint16_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (((unsigned int)right) >= 32) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}



STATIC uint32_t
FUNC_NAME(unary_minus_func_uint32_t_u)(uint32_t ui LOG_INDEX)
{
  LOG_EXEC
  return -ui;
}

STATIC uint32_t
FUNC_NAME(add_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 + ui2;
}

STATIC uint32_t
FUNC_NAME(sub_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 - ui2;
}

STATIC uint32_t
FUNC_NAME(mul_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ((unsigned int)ui1) * ((unsigned int)ui2);
}

STATIC uint32_t
FUNC_NAME(mod_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 % ui2);
}

STATIC uint32_t
FUNC_NAME(div_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 / ui2);
}

STATIC uint32_t
FUNC_NAME(lshift_func_uint32_t_u_s)(uint32_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32) || (left > (UINT32_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC uint32_t
FUNC_NAME(lshift_func_uint32_t_u_u)(uint32_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((unsigned int)right) >= 32) || (left > (UINT32_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC uint32_t
FUNC_NAME(rshift_func_uint32_t_u_s)(uint32_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC uint32_t
FUNC_NAME(rshift_func_uint32_t_u_u)(uint32_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (((unsigned int)right) >= 32) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}

#ifndef NO_LONGLONG


STATIC uint64_t
FUNC_NAME(unary_minus_func_uint64_t_u)(uint64_t ui LOG_INDEX)
{
  LOG_EXEC
  return -ui;
}

STATIC uint64_t
FUNC_NAME(add_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 + ui2;
}

STATIC uint64_t
FUNC_NAME(sub_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ui1 - ui2;
}

STATIC uint64_t
FUNC_NAME(mul_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return ((unsigned long long)ui1) * ((unsigned long long)ui2);
}

STATIC uint64_t
FUNC_NAME(mod_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 % ui2);
}

STATIC uint64_t
FUNC_NAME(div_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (ui2 == 0) ? 
    (UNDEFINED(ui1)) : 
#endif
    (ui1 / ui2);
}

STATIC uint64_t
FUNC_NAME(lshift_func_uint64_t_u_s)(uint64_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32) || (left > (UINT64_MAX >> ((int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((int)right));
}

STATIC uint64_t
FUNC_NAME(lshift_func_uint64_t_u_u)(uint64_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((unsigned int)right) >= 32) || (left > (UINT64_MAX >> ((unsigned int)right)))) ? 
    (UNDEFINED(left)) : 
#endif
    (left << ((unsigned int)right));
}

STATIC uint64_t
FUNC_NAME(rshift_func_uint64_t_u_s)(uint64_t left, int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    ((((int)right) < 0) || (((int)right) >= 32)) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((int)right));
}

STATIC uint64_t
FUNC_NAME(rshift_func_uint64_t_u_u)(uint64_t left, unsigned int right LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE
    (((unsigned int)right) >= 32) ? 
    (UNDEFINED(left)) : 
#endif
    (left >> ((unsigned int)right));
}

#endif




#ifdef __STDC__


STATIC float
FUNC_NAME(add_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabsf((0.5f * sf1) + (0.5f * sf2)) > (0.5f * FLT_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 + sf2);
}

STATIC float
FUNC_NAME(sub_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabsf((0.5f * sf1) - (0.5f * sf2)) > (0.5f * FLT_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 - sf2);
}

STATIC float
FUNC_NAME(mul_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    (fabsf((0x1.0p-100f * sf1) * (0x1.0p-28f * sf2)) > (0x1.0p-100f * (0x1.0p-28f * FLT_MAX))) ?
#else
    (fabsf((ldexpf(1.0, -100) * sf1) * (0x1.0p-28f * sf2)) > (ldexpf(1.0, -100) * (0x1.0p-28f * FLT_MAX))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 * sf2);
}

STATIC float
FUNC_NAME(div_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    ((fabsf(sf2) < 1.0f) && (((sf2 == 0.0f) || (fabsf((0x1.0p-49f * sf1) / (0x1.0p100f * sf2))) > (0x1.0p-100f * (0x1.0p-49f * FLT_MAX))))) ?
#else
    ((fabsf(sf2) < 1.0f) && (((sf2 == 0.0f) || (fabsf((0x1.0p-49f * sf1) / (ldexpf(1.0, 100) * sf2))) > (ldexpf(1.0, -100) * (0x1.0p-49f * FLT_MAX))))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 / sf2);
}




STATIC double
FUNC_NAME(add_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabs((0.5 * sf1) + (0.5 * sf2)) > (0.5 * DBL_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 + sf2);
}

STATIC double
FUNC_NAME(sub_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabs((0.5 * sf1) - (0.5 * sf2)) > (0.5 * DBL_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 - sf2);
}

STATIC double
FUNC_NAME(mul_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    (fabs((0x1.0p-100 * sf1) * (0x1.0p-924 * sf2)) > (0x1.0p-100 * (0x1.0p-924 * DBL_MAX))) ?
#else
    (fabs((ldexp(1.0, -100) * sf1) * (0x1.0p-924 * sf2)) > (ldexp(1.0, -100) * (0x1.0p-924 * DBL_MAX))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 * sf2);
}

STATIC double
FUNC_NAME(div_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    ((fabs(sf2) < 1.0) && (((sf2 == 0.0) || (fabs((0x1.0p-974 * sf1) / (0x1.0p100 * sf2))) > (0x1.0p-100 * (0x1.0p-974 * DBL_MAX))))) ?
#else
    ((fabs(sf2) < 1.0) && (((sf2 == 0.0) || (fabs((0x1.0p-974 * sf1) / (ldexp(1.0, 100) * sf2))) > (ldexp(1.0, -100) * (0x1.0p-974 * DBL_MAX))))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 / sf2);
}


#else


STATIC float
FUNC_NAME(add_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabsf((0.5f * sf1) + (0.5f * sf2)) > (0.5f * FLT_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 + sf2);
}

STATIC float
FUNC_NAME(sub_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabsf((0.5f * sf1) - (0.5f * sf2)) > (0.5f * FLT_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 - sf2);
}

STATIC float
FUNC_NAME(mul_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    (fabsf((0x1.0p-100f * sf1) * (ldexpf(1.0, -28) * sf2)) > (0x1.0p-100f * (ldexpf(1.0, -28) * FLT_MAX))) ?
#else
    (fabsf((ldexpf(1.0, -100) * sf1) * (ldexpf(1.0, -28) * sf2)) > (ldexpf(1.0, -100) * (ldexpf(1.0, -28) * FLT_MAX))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 * sf2);
}

STATIC float
FUNC_NAME(div_func_float_f_f)(float sf1, float sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    ((fabsf(sf2) < 1.0f) && (((sf2 == 0.0f) || (fabsf((ldexpf(1.0, -49) * sf1) / (0x1.0p100f * sf2))) > (0x1.0p-100f * (ldexpf(1.0, -49) * FLT_MAX))))) ?
#else
    ((fabsf(sf2) < 1.0f) && (((sf2 == 0.0f) || (fabsf((ldexpf(1.0, -49) * sf1) / (ldexpf(1.0, 100) * sf2))) > (ldexpf(1.0, -100) * (ldexpf(1.0, -49) * FLT_MAX))))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 / sf2);
}




STATIC double
FUNC_NAME(add_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabs((0.5 * sf1) + (0.5 * sf2)) > (0.5 * DBL_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 + sf2);
}

STATIC double
FUNC_NAME(sub_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    (fabs((0.5 * sf1) - (0.5 * sf2)) > (0.5 * DBL_MAX)) ? 
    UNDEFINED(sf1) :
#endif
    (sf1 - sf2);
}

STATIC double
FUNC_NAME(mul_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    (fabs((0x1.0p-100 * sf1) * (ldexp(1.0, -924) * sf2)) > (0x1.0p-100 * (ldexp(1.0, -924) * DBL_MAX))) ?
#else
    (fabs((ldexp(1.0, -100) * sf1) * (ldexp(1.0, -924) * sf2)) > (ldexp(1.0, -100) * (ldexp(1.0, -924) * DBL_MAX))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 * sf2);
}

STATIC double
FUNC_NAME(div_func_double_f_f)(double sf1, double sf2 LOG_INDEX)
{
  LOG_EXEC
  return
#ifndef UNSAFE_FLOAT
#ifdef __STDC__
    ((fabs(sf2) < 1.0) && (((sf2 == 0.0) || (fabs((ldexp(1.0, -974) * sf1) / (0x1.0p100 * sf2))) > (0x1.0p-100 * (ldexp(1.0, -974) * DBL_MAX))))) ?
#else
    ((fabs(sf2) < 1.0) && (((sf2 == 0.0) || (fabs((ldexp(1.0, -974) * sf1) / (ldexp(1.0, 100) * sf2))) > (ldexp(1.0, -100) * (ldexp(1.0, -974) * DBL_MAX))))) ?
#endif
    UNDEFINED(sf1) :
#endif
    (sf1 / sf2);
}


#endif




STATIC int32_t
FUNC_NAME(convert_func_float_to_int32_t)(float sf1 LOG_INDEX)
{
  LOG_EXEC
  return 
#ifndef UNSAFE_FLOAT
    ((sf1 <= INT32_MIN) || (sf1 >= INT32_MAX)) ?
    UNDEFINED(INT32_MAX) :
#endif
    ((int32_t)(sf1));
}



#endif
