union datat
{
  char c;
  int i;
};

int main(void)
{
  union datat data;
  data.c = '\0';

  __CPROVER_assert(data.i == 0, "");
}
