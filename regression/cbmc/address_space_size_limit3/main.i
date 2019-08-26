// copy of Pointer_Arithmetic12

typedef unsigned int uint32_t;

uint32_t __stack[32];

uint32_t eax;
uint32_t ebp;
uint32_t ebx;
uint32_t ecx;
uint32_t edi;
uint32_t edx;
uint32_t esi;
uint32_t esp=(uint32_t)&(__stack[31]);
uint32_t var0;
uint32_t var1;
uint32_t var10;
uint32_t var11;
uint32_t var12;
uint32_t var13;
uint32_t var14;
uint32_t var15;
uint32_t var16;
uint32_t var2;
uint32_t var3;
uint32_t var4;
uint32_t var5;
uint32_t var6;
uint32_t var7;
uint32_t var8;
uint32_t var9;

void g__L_0x3b4_0()
{
  L_0x3b4_0: esp-=0x4;
  L_0x3b4_1: *(uint32_t*)(esp)=ebp;
  L_0x3b5_0: ebp=esp;
  L_0x3b7_0: var4=ebp;
  L_0x3b7_1: var4+=0xc;
  L_0x3b7_2: eax=*(uint32_t*)(var4);
  L_0x3ba_0: edx=eax;
  L_0x3bc_0: edx&=0x3;
  L_0x3bf_0: var5=ebp;
  L_0x3bf_1: var5+=0x8;
  L_0x3bf_2: eax=*(uint32_t*)(var5);
  L_0x3c2_0: *(uint32_t*)(eax)=edx;
  L_0x3c4_0: ebp=*(uint32_t*)(esp);
  L_0x3c4_1: esp+=0x4;
  L_0x3c5_0: return;
}

void f__L_0x3c6_0()
{
  L_0x3c6_0: esp-=0x4;
  L_0x3c6_1: *(uint32_t*)(esp)=ebp;
  L_0x3c7_0: ebp=esp;
  L_0x3c9_0: esp-=0x18;
  L_0x3cc_0: var6=ebp;
  L_0x3cc_1: var6-=0x4;
  L_0x3cc_2: *(uint32_t*)(var6)=0x0;
  L_0x3d3_0: var7=ebp;
  L_0x3d3_1: var7-=0x8;
  L_0x3d3_2: *(uint32_t*)(var7)=0x0;
  L_0x3da_0: var8=ebp;
  L_0x3da_1: var8+=0x8;
  L_0x3da_2: eax=*(uint32_t*)(var8);
  L_0x3dd_0: var9=ebp;
  L_0x3dd_1: var9-=0x4;
  L_0x3dd_2: *(uint32_t*)(var9)=eax;
  L_0x3e0_0: var10=ebp;
  L_0x3e0_1: var10-=0x4;
  L_0x3e0_2: eax=*(uint32_t*)(var10);
  L_0x3e3_0: var11=esp;
  L_0x3e3_1: var11+=0x4;
  L_0x3e3_2: *(uint32_t*)(var11)=eax;
  L_0x3e7_0: var12=ebp;
  L_0x3e7_1: var12-=0x8;
  L_0x3e7_2: eax=(uint32_t)&*(uint32_t*)(var12);
  L_0x3ea_0: *(uint32_t*)(esp)=eax;
  L_0x3ed_0: esp-=4; g__L_0x3b4_0(); esp+=4;
  L_0x3f2_0: var13=ebp;
  L_0x3f2_1: var13-=0x4;
  L_0x3f2_2: *(uint32_t*)(var13)=0x5;
  L_0x3f9_0: var14=ebp;
  L_0x3f9_1: var14-=0x8;
  L_0x3f9_2: eax=*(uint32_t*)(var14);
  L_0x3fc_0: esp=ebp;
  L_0x3fc_1: ebp=*(uint32_t*)(esp);
  L_0x3fc_2: esp+=0x4;
  L_0x3fd_0: return;
}

int main()
{
  int unknown;
  // Avoid constant propagation solving for pointer-offsets of esp,
  // which prevent demonstrating the object-size limitation this test
  // intends to exhibit:
  esp -= (unknown & 1);
  L_0x3fe_0: esp-=0x4;
  L_0x3fe_1: *(uint32_t*)(esp)=ebp;
  L_0x3ff_0: ebp=esp;
  L_0x401_0: esp-=0x14;
  L_0x404_0: var15=ebp;
  L_0x404_1: var15-=0x4;
  L_0x404_2: *(uint32_t*)(var15)=0xffffffff;
  L_0x40b_0: var16=ebp;
  L_0x40b_1: var16-=0x4;
  L_0x40b_2: eax=*(uint32_t*)(var16);
  L_0x40e_0: *(uint32_t*)(esp)=eax;
  L_0x411_0: esp-=4; f__L_0x3c6_0(); esp+=4;
             uint32_t eax1=eax;
  C_0x3ff_0: ebp=esp;
  C_0x401_0: esp-=0x14;
  C_0x404_0: var15=ebp;
  C_0x404_1: var15-=0x4;
  C_0x404_2: *(uint32_t*)(var15)=0xffffffff;
  C_0x40b_0: var16=ebp;
  C_0x40b_1: var16-=0x4;
  C_0x40b_2: eax=*(uint32_t*)(var16);
  C_0x40e_0: *(uint32_t*)(esp)=eax;
  C_0x411_0: esp-=4; f__L_0x3c6_0(); esp+=4;
             uint32_t eax2=eax;
             __CPROVER_assert(eax2 == eax1, "");
  L_0x416_0: esp=ebp;
  L_0x416_1: ebp=*(uint32_t*)(esp);
  L_0x416_2: esp+=0x4;
  L_0x417_0: return 0;
}
