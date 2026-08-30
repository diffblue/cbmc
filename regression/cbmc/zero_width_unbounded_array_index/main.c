struct empty
{
};

int main()
{
  struct empty arr[10];
  struct empty *p = arr;
  struct empty e = p[1];
  return 0;
}
