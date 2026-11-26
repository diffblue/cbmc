volatile int data;
volatile int cmd;

// The device's view of the data register, updated when the device observes a
// write to it.
int data_seen;

void observe_data(int value)
{
  data_seen = value;
}

void observe_cmd(int value)
{
  // When the device observes the GO command it requires that the write to the
  // data register has already been observed.
  if(value == 1)
    __CPROVER_assert(data_seen == 0x1234, "data committed before GO");
}

int main()
{
  data = 0x1234;
  cmd = 1;
  return 0;
}
