struct timer {
  int (* func)(int);
  int a;
};

struct irq_handler {
  void (* handler)(int);
};


struct irq_handler ihandler;
struct timer timer;

int func2(int a)
{
  // this should fail
  assert(0);

  return a + 10;
}

void func1(int a)
{
  timer.func = func2;
}

void run_irq_handler()
{
  (* ihandler.handler)(10);  
}

void run_timer()
{
  (* timer.func)(20);
}

int main()
{
  ihandler.handler = func1;
  
  run_irq_handler();
  run_timer();
}
