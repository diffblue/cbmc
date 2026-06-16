/* FUNCTION: __builtin_neon_vabd_v */

// Arm instruction(s): SABD, UABD (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vabd_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
    {
      int d = (int)x[i] - (int)y[i];
      r[i] = d < 0 ? -d : d;
    }
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
    {
      int d = (int)x[i] - (int)y[i];
      r[i] = d < 0 ? -d : d;
    }
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
    {
      long long d = (long long)x[i] - (long long)y[i];
      r[i] = d < 0 ? -d : d;
    }
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vabdq_v */

// Arm instruction(s): SABD, UABD (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vabdq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
    {
      int d = (int)x[i] - (int)y[i];
      r[i] = d < 0 ? -d : d;
    }
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
    {
      int d = (int)x[i] - (int)y[i];
      r[i] = d < 0 ? -d : d;
    }
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
    {
      long long d = (long long)x[i] - (long long)y[i];
      r[i] = d < 0 ? -d : d;
    }
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : y[i] - x[i];
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vbsl_v */

// Arm instruction(s): BSL (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));

__gcc_v8qi
__builtin_neon_vbsl_v(__gcc_v8qi mask, __gcc_v8qi a, __gcc_v8qi b, int type)
{
  (void)type;
  return (mask & a) | (~mask & b);
}

/* FUNCTION: __builtin_neon_vbslq_v */

// Arm instruction(s): BSL (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));

__gcc_v16qi
__builtin_neon_vbslq_v(__gcc_v16qi mask, __gcc_v16qi a, __gcc_v16qi b, int type)
{
  (void)type;
  return (mask & a) | (~mask & b);
}

/* FUNCTION: __builtin_neon_vhadd_v */

// Arm instruction(s): SHADD, UHADD (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vhadd_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = ((long long)x[i] + (long long)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = ((long long)x[i] + (long long)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vhaddq_v */

// Arm instruction(s): SHADD, UHADD (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vhaddq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((long long)x[i] + (long long)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((long long)x[i] + (long long)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vhsub_v */

// Arm instruction(s): SHSUB, UHSUB (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vhsub_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = ((long long)x[i] - (long long)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = ((long long)x[i] - (long long)y[i]) >> 1;
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vhsubq_v */

// Arm instruction(s): SHSUB, UHSUB (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vhsubq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((long long)x[i] - (long long)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] - (int)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((long long)x[i] - (long long)y[i]) >> 1;
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vmax_v */

// Arm instruction(s): SMAX, UMAX (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vmax_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vmaxq_v */

// Arm instruction(s): SMAX, UMAX (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vmaxq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vmin_v */

// Arm instruction(s): SMIN, UMIN (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vmin_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vminq_v */

// Arm instruction(s): SMIN, UMIN (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vminq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] < y[i] ? x[i] : y[i];
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vpadd_v */

// Arm instruction(s): ADDP (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vpadd_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned char)x[2 * i] + (unsigned char)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned char)y[2 * i] + (unsigned char)y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned short)x[2 * i] + (unsigned short)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned short)y[2 * i] + (unsigned short)y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned int)x[2 * i] + (unsigned int)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned int)y[2 * i] + (unsigned int)y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned char)x[2 * i] + (unsigned char)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned char)y[2 * i] + (unsigned char)y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned short)x[2 * i] + (unsigned short)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned short)y[2 * i] + (unsigned short)y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned int)x[2 * i] + (unsigned int)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned int)y[2 * i] + (unsigned int)y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vpaddq_v */

// Arm instruction(s): ADDP (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef long long __gcc_v2di_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));
typedef unsigned long long __gcc_v2di_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vpaddq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    int h = 16 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned char)x[2 * i] + (unsigned char)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned char)y[2 * i] + (unsigned char)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned short)x[2 * i] + (unsigned short)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned short)y[2 * i] + (unsigned short)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned int)x[2 * i] + (unsigned int)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned int)y[2 * i] + (unsigned int)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 35:
  {
    __gcc_v2di_s x = (__gcc_v2di_s)a, y = (__gcc_v2di_s)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned long long)x[2 * i] + (unsigned long long)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] =
        (unsigned long long)y[2 * i] + (unsigned long long)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    int h = 16 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned char)x[2 * i] + (unsigned char)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned char)y[2 * i] + (unsigned char)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned short)x[2 * i] + (unsigned short)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned short)y[2 * i] + (unsigned short)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned int)x[2 * i] + (unsigned int)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = (unsigned int)y[2 * i] + (unsigned int)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 51:
  {
    __gcc_v2di_u x = (__gcc_v2di_u)a, y = (__gcc_v2di_u)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = (unsigned long long)x[2 * i] + (unsigned long long)x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] =
        (unsigned long long)y[2 * i] + (unsigned long long)y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vpmax_v */

// Arm instruction(s): SMAXP, UMAXP (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vpmax_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vpmaxq_v */

// Arm instruction(s): SMAXP, UMAXP (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vpmaxq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    int h = 16 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    int h = 16 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] > x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] > y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vpmin_v */

// Arm instruction(s): SMINP, UMINP (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vpmin_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    int h = 2 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vpminq_v */

// Arm instruction(s): SMINP, UMINP (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vpminq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    int h = 16 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    int h = 16 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    int h = 8 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    int h = 4 / 2;
    for(int i = 0; i < h; i++)
      r[i] = x[2 * i] < x[2 * i + 1] ? x[2 * i] : x[2 * i + 1];
    for(int i = 0; i < h; i++)
      r[h + i] = y[2 * i] < y[2 * i + 1] ? y[2 * i] : y[2 * i + 1];
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vqadd_v */

// Arm instruction(s): SQADD, UQADD (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef long long __gcc_v1di_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));
typedef unsigned long long __gcc_v1di_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vqadd_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s < -128 ? -128 : (s > 127 ? 127 : s);
    }
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s < -32768 ? -32768 : (s > 32767 ? 32767 : s);
    }
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
    {
      long long s = (long long)x[i] + (long long)y[i];
      r[i] = s < -2147483648 ? -2147483648 : (s > 2147483647 ? 2147483647 : s);
    }
    return (__gcc_v8qi)r;
  }
  case 3:
  {
    __gcc_v1di_s x = (__gcc_v1di_s)a, y = (__gcc_v1di_s)b, r;
    for(int i = 0; i < 1; i++)
    {
      long long s =
        (long long)((unsigned long long)x[i] + (unsigned long long)y[i]);
      r[i] =
        ((x[i] ^ s) & (y[i] ^ s)) < 0
          ? (x[i] < 0 ? (-9223372036854775807LL - 1) : 9223372036854775807LL)
          : s;
    }
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s > 255 ? 255 : s;
    }
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s > 65535 ? 65535 : s;
    }
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
    {
      long long s = (long long)x[i] + (long long)y[i];
      r[i] = s > 4294967295 ? 4294967295 : s;
    }
    return (__gcc_v8qi)r;
  }
  case 19:
  {
    __gcc_v1di_u x = (__gcc_v1di_u)a, y = (__gcc_v1di_u)b, r;
    for(int i = 0; i < 1; i++)
    {
      unsigned long long s = x[i] + y[i];
      r[i] = s < x[i] ? 18446744073709551615ULL : s;
    }
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vqaddq_v */

// Arm instruction(s): SQADD, UQADD (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef long long __gcc_v2di_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));
typedef unsigned long long __gcc_v2di_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vqaddq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s < -128 ? -128 : (s > 127 ? 127 : s);
    }
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s < -32768 ? -32768 : (s > 32767 ? 32767 : s);
    }
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
    {
      long long s = (long long)x[i] + (long long)y[i];
      r[i] = s < -2147483648 ? -2147483648 : (s > 2147483647 ? 2147483647 : s);
    }
    return (__gcc_v16qi)r;
  }
  case 35:
  {
    __gcc_v2di_s x = (__gcc_v2di_s)a, y = (__gcc_v2di_s)b, r;
    for(int i = 0; i < 2; i++)
    {
      long long s =
        (long long)((unsigned long long)x[i] + (unsigned long long)y[i]);
      r[i] =
        ((x[i] ^ s) & (y[i] ^ s)) < 0
          ? (x[i] < 0 ? (-9223372036854775807LL - 1) : 9223372036854775807LL)
          : s;
    }
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s > 255 ? 255 : s;
    }
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
    {
      int s = (int)x[i] + (int)y[i];
      r[i] = s > 65535 ? 65535 : s;
    }
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
    {
      long long s = (long long)x[i] + (long long)y[i];
      r[i] = s > 4294967295 ? 4294967295 : s;
    }
    return (__gcc_v16qi)r;
  }
  case 51:
  {
    __gcc_v2di_u x = (__gcc_v2di_u)a, y = (__gcc_v2di_u)b, r;
    for(int i = 0; i < 2; i++)
    {
      unsigned long long s = x[i] + y[i];
      r[i] = s < x[i] ? 18446744073709551615ULL : s;
    }
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vqsub_v */

// Arm instruction(s): SQSUB, UQSUB (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef long long __gcc_v1di_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));
typedef unsigned long long __gcc_v1di_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vqsub_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
    {
      int s = (int)x[i] - (int)y[i];
      r[i] = s < -128 ? -128 : (s > 127 ? 127 : s);
    }
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
    {
      int s = (int)x[i] - (int)y[i];
      r[i] = s < -32768 ? -32768 : (s > 32767 ? 32767 : s);
    }
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
    {
      long long s = (long long)x[i] - (long long)y[i];
      r[i] = s < -2147483648 ? -2147483648 : (s > 2147483647 ? 2147483647 : s);
    }
    return (__gcc_v8qi)r;
  }
  case 3:
  {
    __gcc_v1di_s x = (__gcc_v1di_s)a, y = (__gcc_v1di_s)b, r;
    for(int i = 0; i < 1; i++)
    {
      long long d =
        (long long)((unsigned long long)x[i] - (unsigned long long)y[i]);
      r[i] =
        ((x[i] ^ y[i]) & (x[i] ^ d)) < 0
          ? (x[i] < 0 ? (-9223372036854775807LL - 1) : 9223372036854775807LL)
          : d;
    }
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v8qi)r;
  }
  case 19:
  {
    __gcc_v1di_u x = (__gcc_v1di_u)a, y = (__gcc_v1di_u)b, r;
    for(int i = 0; i < 1; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vqsubq_v */

// Arm instruction(s): SQSUB, UQSUB (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef long long __gcc_v2di_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));
typedef unsigned long long __gcc_v2di_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vqsubq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
    {
      int s = (int)x[i] - (int)y[i];
      r[i] = s < -128 ? -128 : (s > 127 ? 127 : s);
    }
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
    {
      int s = (int)x[i] - (int)y[i];
      r[i] = s < -32768 ? -32768 : (s > 32767 ? 32767 : s);
    }
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
    {
      long long s = (long long)x[i] - (long long)y[i];
      r[i] = s < -2147483648 ? -2147483648 : (s > 2147483647 ? 2147483647 : s);
    }
    return (__gcc_v16qi)r;
  }
  case 35:
  {
    __gcc_v2di_s x = (__gcc_v2di_s)a, y = (__gcc_v2di_s)b, r;
    for(int i = 0; i < 2; i++)
    {
      long long d =
        (long long)((unsigned long long)x[i] - (unsigned long long)y[i]);
      r[i] =
        ((x[i] ^ y[i]) & (x[i] ^ d)) < 0
          ? (x[i] < 0 ? (-9223372036854775807LL - 1) : 9223372036854775807LL)
          : d;
    }
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v16qi)r;
  }
  case 51:
  {
    __gcc_v2di_u x = (__gcc_v2di_u)a, y = (__gcc_v2di_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = x[i] > y[i] ? x[i] - y[i] : 0;
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vrhadd_v */

// Arm instruction(s): SRHADD, URHADD (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vrhadd_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = ((long long)x[i] + (long long)y[i] + 1) >> 1;
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = ((long long)x[i] + (long long)y[i] + 1) >> 1;
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vrhaddq_v */

// Arm instruction(s): SRHADD, URHADD (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vrhaddq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((long long)x[i] + (long long)y[i] + 1) >> 1;
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = ((int)x[i] + (int)y[i] + 1) >> 1;
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = ((long long)x[i] + (long long)y[i] + 1) >> 1;
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vtst_v */

// Arm instruction(s): CMTST (per ACLE advsimd.md)

typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef signed char __gcc_v8qi_s __attribute__((__vector_size__(8)));
typedef short __gcc_v4hi_s __attribute__((__vector_size__(8)));
typedef int __gcc_v2si_s __attribute__((__vector_size__(8)));
typedef long long __gcc_v1di_s __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
typedef unsigned int __gcc_v2si_u __attribute__((__vector_size__(8)));
typedef unsigned long long __gcc_v1di_u __attribute__((__vector_size__(8)));

__gcc_v8qi __builtin_neon_vtst_v(__gcc_v8qi a, __gcc_v8qi b, int type)
{
  switch(type)
  {
  case 0:
  {
    __gcc_v8qi_s x = (__gcc_v8qi_s)a, y = (__gcc_v8qi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 1:
  {
    __gcc_v4hi_s x = (__gcc_v4hi_s)a, y = (__gcc_v4hi_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 2:
  {
    __gcc_v2si_s x = (__gcc_v2si_s)a, y = (__gcc_v2si_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 3:
  {
    __gcc_v1di_s x = (__gcc_v1di_s)a, y = (__gcc_v1di_s)b, r;
    for(int i = 0; i < 1; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 16:
  {
    __gcc_v8qi_u x = (__gcc_v8qi_u)a, y = (__gcc_v8qi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 17:
  {
    __gcc_v4hi_u x = (__gcc_v4hi_u)a, y = (__gcc_v4hi_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 18:
  {
    __gcc_v2si_u x = (__gcc_v2si_u)a, y = (__gcc_v2si_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  case 19:
  {
    __gcc_v1di_u x = (__gcc_v1di_u)a, y = (__gcc_v1di_u)b, r;
    for(int i = 0; i < 1; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v8qi)r;
  }
  }

  __gcc_v8qi r = {0};
  return r;
}

/* FUNCTION: __builtin_neon_vtstq_v */

// Arm instruction(s): CMTST (per ACLE advsimd.md)

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef signed char __gcc_v16qi_s __attribute__((__vector_size__(16)));
typedef short __gcc_v8hi_s __attribute__((__vector_size__(16)));
typedef int __gcc_v4si_s __attribute__((__vector_size__(16)));
typedef long long __gcc_v2di_s __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
typedef unsigned int __gcc_v4si_u __attribute__((__vector_size__(16)));
typedef unsigned long long __gcc_v2di_u __attribute__((__vector_size__(16)));

__gcc_v16qi __builtin_neon_vtstq_v(__gcc_v16qi a, __gcc_v16qi b, int type)
{
  switch(type)
  {
  case 32:
  {
    __gcc_v16qi_s x = (__gcc_v16qi_s)a, y = (__gcc_v16qi_s)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 33:
  {
    __gcc_v8hi_s x = (__gcc_v8hi_s)a, y = (__gcc_v8hi_s)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 34:
  {
    __gcc_v4si_s x = (__gcc_v4si_s)a, y = (__gcc_v4si_s)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 35:
  {
    __gcc_v2di_s x = (__gcc_v2di_s)a, y = (__gcc_v2di_s)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 48:
  {
    __gcc_v16qi_u x = (__gcc_v16qi_u)a, y = (__gcc_v16qi_u)b, r;
    for(int i = 0; i < 16; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 49:
  {
    __gcc_v8hi_u x = (__gcc_v8hi_u)a, y = (__gcc_v8hi_u)b, r;
    for(int i = 0; i < 8; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 50:
  {
    __gcc_v4si_u x = (__gcc_v4si_u)a, y = (__gcc_v4si_u)b, r;
    for(int i = 0; i < 4; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  case 51:
  {
    __gcc_v2di_u x = (__gcc_v2di_u)a, y = (__gcc_v2di_u)b, r;
    for(int i = 0; i < 2; i++)
      r[i] = (x[i] & y[i]) != 0 ? -1 : 0;
    return (__gcc_v16qi)r;
  }
  }

  __gcc_v16qi r = {0};
  return r;
}
