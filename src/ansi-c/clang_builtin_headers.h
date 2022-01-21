// clang-format off
__gcc_v2di __builtin_ia32_undef128(void);
__gcc_v4di __builtin_ia32_undef256(void);
__gcc_v8di __builtin_ia32_undef512(void);

__gcc_v8hi __builtin_ia32_cvtne2ps2bf16_128(__gcc_v4sf, __gcc_v4sf);
__gcc_v16hi __builtin_ia32_cvtne2ps2bf16_256(__gcc_v8sf, __gcc_v8sf);
__gcc_v32hi __builtin_ia32_cvtne2ps2bf16_512(__gcc_v16sf, __gcc_v16sf);
__gcc_v8hi __builtin_ia32_cvtneps2bf16_128_mask(__gcc_v4sf, __gcc_v8hi, unsigned char);
__gcc_v8hi __builtin_ia32_cvtneps2bf16_256_mask(__gcc_v8sf, __gcc_v8hi, unsigned char);
__gcc_v16si __builtin_ia32_cvtneps2bf16_512_mask(__gcc_v16sf, __gcc_v16hi, unsigned short);
__gcc_v4sf __builtin_ia32_dpbf16ps_128(__gcc_v4sf, __gcc_v4si, __gcc_v4si);
__gcc_v8sf __builtin_ia32_dpbf16ps_256(__gcc_v8sf, __gcc_v8si, __gcc_v8si);
__gcc_v16sf __builtin_ia32_dpbf16ps_512(__gcc_v16sf, __gcc_v16si, __gcc_v16si);
float __builtin_ia32_cvtsbf162ss_32(unsigned short);

void __builtin_ia32_vp2intersect_d_512(__gcc_v16si, __gcc_v16si, unsigned short *, unsigned short *);
void __builtin_ia32_vp2intersect_d_256(__gcc_v8si, __gcc_v8si, unsigned char *, unsigned char *);
void __builtin_ia32_vp2intersect_d_128(__gcc_v4si, __gcc_v4si, unsigned char *, unsigned char *);

__gcc_v16qi __builtin_ia32_selectb_128(unsigned short, __gcc_v16qi, __gcc_v16qi);
__gcc_v32qi __builtin_ia32_selectb_256(unsigned int, __gcc_v32qi, __gcc_v32qi);
__gcc_v64qi __builtin_ia32_selectb_512(unsigned long, __gcc_v64qi, __gcc_v64qi);
__gcc_v8hi __builtin_ia32_selectw_128(unsigned char, __gcc_v8hi, __gcc_v8hi);
__gcc_v16hi __builtin_ia32_selectw_256(unsigned short, __gcc_v16hi, __gcc_v16hi);
__gcc_v32hi __builtin_ia32_selectw_512(unsigned int, __gcc_v32hi, __gcc_v32hi);
__gcc_v4si __builtin_ia32_selectd_128(unsigned char, __gcc_v4si, __gcc_v4si);
__gcc_v8si __builtin_ia32_selectd_256(unsigned char, __gcc_v8si, __gcc_v8si);
__gcc_v16si __builtin_ia32_selectd_512(unsigned short, __gcc_v16si, __gcc_v16si);
__gcc_v4sf __builtin_ia32_selectps_128(unsigned char, __gcc_v4sf, __gcc_v4sf);
__gcc_v8sf __builtin_ia32_selectps_256(unsigned char, __gcc_v8sf, __gcc_v8sf);
__gcc_v16sf __builtin_ia32_selectps_512(unsigned short, __gcc_v16sf, __gcc_v16sf);
__gcc_v2df __builtin_ia32_selectpd_128(unsigned char, __gcc_v2df, __gcc_v2df);
__gcc_v4df __builtin_ia32_selectpd_256(unsigned char, __gcc_v4df, __gcc_v4df);
__gcc_v8df __builtin_ia32_selectpd_512(unsigned char, __gcc_v8df, __gcc_v8df);
__gcc_v4sf __builtin_ia32_selectss_128(unsigned char, __gcc_v4sf, __gcc_v4sf);
__gcc_v2df __builtin_ia32_selectsd_128(unsigned char, __gcc_v2df, __gcc_v2df);

__gcc_v4sf __builtin_ia32_vfmaddss3_mask(__gcc_v4sf, __gcc_v4sf, __gcc_v4sf, unsigned char, int);
__gcc_v4sf __builtin_ia32_vfmaddss3_maskz(__gcc_v4sf, __gcc_v4sf, __gcc_v4sf, unsigned char, int);
__gcc_v4sf __builtin_ia32_vfmaddss3_mask3(__gcc_v4sf, __gcc_v4sf, __gcc_v4sf, unsigned char, int);
__gcc_v2df __builtin_ia32_vfmaddsd3_mask(__gcc_v2df, __gcc_v2df, __gcc_v2df, unsigned char, int);
__gcc_v2df __builtin_ia32_vfmaddsd3_maskz(__gcc_v2df, __gcc_v2df, __gcc_v2df, unsigned char, int);
__gcc_v2df __builtin_ia32_vfmaddsd3_mask3(__gcc_v2df, __gcc_v2df, __gcc_v2df, unsigned char, int);
__gcc_v2df __builtin_ia32_vfmsubsd3_mask3(__gcc_v2df, __gcc_v2df, __gcc_v2df, unsigned char, int);
__gcc_v4sf __builtin_ia32_vfmsubss3_mask3(__gcc_v4sf, __gcc_v4sf, __gcc_v4sf, unsigned char, int);

__gcc_v4sf __builtin_ia32_cvtsd2ss_round_mask(__gcc_v4sf, __gcc_v2df, __gcc_v4sf, unsigned char, int);
__gcc_v2df __builtin_ia32_cvtss2sd_round_mask(__gcc_v2df, __gcc_v4sf, __gcc_v2df, unsigned char, int);
// clang-format on

void __builtin_nontemporal_store();
void __builtin_nontemporal_load();

int __builtin_flt_rounds(void);

unsigned char __builtin_bitreverse8(unsigned char);
unsigned short __builtin_bitreverse16(unsigned short);
unsigned int __builtin_bitreverse32(unsigned int);
unsigned long long __builtin_bitreverse64(unsigned long long);

unsigned char __builtin_rotateleft8(unsigned char, unsigned char);
unsigned short __builtin_rotateleft16(unsigned short, unsigned short);
unsigned int __builtin_rotateleft32(unsigned int, unsigned int);
unsigned long long __builtin_rotateleft64(unsigned long long, unsigned long long);

unsigned char __builtin_rotateright8(unsigned char, unsigned char);
unsigned short __builtin_rotateright16(unsigned short, unsigned short);
unsigned int __builtin_rotateright32(unsigned int, unsigned int);
unsigned long long __builtin_rotateright64(unsigned long long, unsigned long long);
// clang-format on
