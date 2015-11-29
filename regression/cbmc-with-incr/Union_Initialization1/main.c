#include <assert.h>

// based on Linux's
// arch/x86/include/asm/io_apic.h

union
{
  int something;

  struct
  {
    unsigned vector          :  8,
             delivery_mode   :  3,
             dest_mode       :  1,
             delivery_status :  1,
             polarity        :  1,
             irr             :  1,
             trigger         :  1,
             mask            :  1,
             __reserved_2    : 15;
             
    unsigned __reserved_3    : 24,
             dest            :  8;      
  } entry;

} u1 = { .entry.delivery_mode = 2, .entry.mask = 1 };

union
{
  int a, b;

  struct
  {
    int d, e;
  } c;
  
} u2 = { 1 }, u3 = { .c.e = 2 } ;

int main()
{
  assert(u1.entry.vector==0);
  assert(u1.entry.delivery_mode==2);
  assert(u1.entry.mask==1);
  
  assert(u2.a==1);
  assert(u3.a==0);
  assert(u3.c.e==2);
}
