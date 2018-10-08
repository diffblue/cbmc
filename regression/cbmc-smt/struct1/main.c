struct datat
{
  char c;
  int i;
};

int main(void)
{
  struct datat data;
  data.c = '\0';

  __CPROVER_assert(data.i == 0, "");
}
