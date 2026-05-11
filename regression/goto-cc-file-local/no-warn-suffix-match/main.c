extern int recv(int);
int kernel_entry(void);
int main(void)
{
  return recv(0) + kernel_entry();
}
