int main(void)
{
  void *v, *x, *x_before;
  x_before = x;
  __atomic_store_n(&x, 42, 0);
  __atomic_exchange_n(&x, 42, 0);
}
