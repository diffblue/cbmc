#include <stdbool.h>

int global;
const int num_irqs=2;
const char* __CPROVER_isr_array[]={"isrA", "isrB"};
int irq_enabled[]={0, 0};
int count=2;

int nondet_int();
bool nondet_bool();

void __CPROVER_enable_isr(int i)
{
  irq_enabled[i]=1;
}

void __CPROVER_disable_isr(int i)
{
  irq_enabled[i]=0;
}

void f()
{
  int j=count;
  int irq;

  for(int i=0; i<j; i++)
  {
    // non-deterministically generate candidate irq
    irq = nondet_int();
    __CPROVER_assume(irq>=0 && irq<num_irqs);

    // if irq is enabled, contingently generate the interrupt
    if(count!=0 && irq_enabled[irq] && nondet_bool())
    {
      count--;

      // invoke the ISR, preempting the calling program
      switch(irq)
      {
        case 0: isrA(); break;
        case 1: isrB(); break;
        default: ;
      }
    }
  }
}

void isrA()
{
  __CPROVER_disable_isr(0);
  __CPROVER_enable_isr(1);

  global=0;

  __CPROVER_enable_isr(0);
}

void isrB()
{
  __CPROVER_disable_isr(1);

  global=1;
  assert(global==1); // safe

  __CPROVER_enable_isr(1);
}

int main()
{
  __CPROVER_enable_isr(0);
  f();
}
