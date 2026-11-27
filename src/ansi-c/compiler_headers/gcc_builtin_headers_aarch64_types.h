// clang-format off
// The built-in types that GCC (aarch64-simd-builtin-types.def and
// aarch64-builtins.cc) provides for AArch64: the vector types that
// <arm_neon.h> gives user-visible names to, and the scalar types that
// <arm_neon.h> converts pointers to. CBMC models __fp16 and __bf16 as
// _Float16, and __mfp8 (an 8-bit floating-point type of unspecified format)
// as an unsigned 8-bit integer. The vector_size attributes precede the
// element types, which the C++ front-end requires. gcc_builtin_headers_types.h
// declares __Float32x4_t and __Float64x2_t.
typedef unsigned char __mfp8;
typedef unsigned char __Poly8_t;
typedef unsigned short __Poly16_t;
typedef unsigned long __Poly64_t;
typedef unsigned __int128 __Poly128_t;

typedef __attribute__((__vector_size__(8))) signed char __Int8x8_t;
typedef __attribute__((__vector_size__(8))) short __Int16x4_t;
typedef __attribute__((__vector_size__(8))) int __Int32x2_t;
typedef __attribute__((__vector_size__(8))) long __Int64x1_t;
typedef __attribute__((__vector_size__(8))) unsigned char __Uint8x8_t;
typedef __attribute__((__vector_size__(8))) unsigned short __Uint16x4_t;
typedef __attribute__((__vector_size__(8))) unsigned int __Uint32x2_t;
typedef __attribute__((__vector_size__(8))) unsigned long __Uint64x1_t;
typedef __attribute__((__vector_size__(8))) __Poly8_t __Poly8x8_t;
typedef __attribute__((__vector_size__(8))) __Poly16_t __Poly16x4_t;
typedef __attribute__((__vector_size__(8))) __Poly64_t __Poly64x1_t;
typedef __attribute__((__vector_size__(8))) __CPROVER_Float16 __Float16x4_t;
typedef __attribute__((__vector_size__(8))) float __Float32x2_t;
typedef __attribute__((__vector_size__(8))) double __Float64x1_t;
typedef __attribute__((__vector_size__(8))) __CPROVER_Float16 __Bfloat16x4_t;
typedef __attribute__((__vector_size__(8))) __mfp8 __Mfloat8x8_t;

typedef __attribute__((__vector_size__(16))) signed char __Int8x16_t;
typedef __attribute__((__vector_size__(16))) short __Int16x8_t;
typedef __attribute__((__vector_size__(16))) int __Int32x4_t;
typedef __attribute__((__vector_size__(16))) long __Int64x2_t;
typedef __attribute__((__vector_size__(16))) unsigned char __Uint8x16_t;
typedef __attribute__((__vector_size__(16))) unsigned short __Uint16x8_t;
typedef __attribute__((__vector_size__(16))) unsigned int __Uint32x4_t;
typedef __attribute__((__vector_size__(16))) unsigned long __Uint64x2_t;
typedef __attribute__((__vector_size__(16))) __Poly8_t __Poly8x16_t;
typedef __attribute__((__vector_size__(16))) __Poly16_t __Poly16x8_t;
typedef __attribute__((__vector_size__(16))) __Poly64_t __Poly64x2_t;
typedef __attribute__((__vector_size__(16))) __CPROVER_Float16 __Float16x8_t;
typedef __attribute__((__vector_size__(16))) __CPROVER_Float16 __Bfloat16x8_t;
typedef __attribute__((__vector_size__(16))) __mfp8 __Mfloat8x16_t;

typedef signed char __builtin_aarch64_simd_qi;
typedef short __builtin_aarch64_simd_hi;
typedef int __builtin_aarch64_simd_si;
typedef long __builtin_aarch64_simd_di;
typedef __CPROVER_Float16 __builtin_aarch64_simd_hf;
typedef float __builtin_aarch64_simd_sf;
typedef double __builtin_aarch64_simd_df;
typedef __CPROVER_Float16 __builtin_aarch64_simd_bf;
typedef __Poly8_t __builtin_aarch64_simd_poly8;
typedef __Poly16_t __builtin_aarch64_simd_poly16;
typedef __Poly64_t __builtin_aarch64_simd_poly64;
typedef __Poly128_t __builtin_aarch64_simd_poly128;
typedef __int128 __builtin_aarch64_simd_ti;
typedef unsigned char __builtin_aarch64_simd_uqi;
typedef unsigned short __builtin_aarch64_simd_uhi;
typedef unsigned int __builtin_aarch64_simd_usi;
typedef unsigned long __builtin_aarch64_simd_udi;
// GCC 11 and earlier pass tuples of two to four 128-bit registers to the
// structure load and store builtins as opaque values of the size of the tuple
// (integers in GCC).
typedef __attribute__((__vector_size__(32))) long __builtin_aarch64_simd_oi;
typedef __attribute__((__vector_size__(48))) long __builtin_aarch64_simd_ci;
typedef __attribute__((__vector_size__(64))) long __builtin_aarch64_simd_xi;
// clang-format on
