int main()
{
  int A[(sizeof((int[]){1, 2, 3})==3*sizeof(int))?1:-1];

  return 0;
}
