
int main()
{
  int *p = malloc(10);

  if(non_det())
    p = malloc(20);
}
