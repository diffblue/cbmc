volatile int data;
volatile int cmd;

int data_seen;

void observe_data(int value)
{
  data_seen = value;
}

void observe_cmd(int value)
{
  if(value == 1)
    __CPROVER_assert(data_seen == 0x1234, "data committed before GO");
}

// A helper that writes the data register and returns without a barrier.
void write_data(void)
{
  data = 0x1234;
}

int main()
{
  write_data();
  cmd = 1;
  return 0;
}
