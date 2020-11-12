int main(void)
{
  void *v, *x, *x_before;
  x_before = x;
#ifdef __GNUC__
  __atomic_store_n(&x, 42, 0);
  __atomic_exchange_n(&x, 42, 0);
#endif
}
