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

int main()
{
  data = 0x1234;
  cmd = 1;
  return 0;
}
