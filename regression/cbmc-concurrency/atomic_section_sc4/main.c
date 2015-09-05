
int open = 0;
int power_on = 0;

void i2c_hid_open() {
  __CPROVER_atomic_begin();

  if(open == 0)
  {
  if (open == 0) {
    power_on = 1;
  }

  __CPROVER_assert(power_on != 0, "");
  }
  __CPROVER_assert(power_on != 0, "");

  __CPROVER_atomic_end();
}

void main() {
__CPROVER_ASYNC_1: i2c_hid_open();
}


