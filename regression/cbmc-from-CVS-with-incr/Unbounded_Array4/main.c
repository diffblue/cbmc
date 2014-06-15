int main()
{
  int xxx;
  xxx=1;
  int array[xxx];
  xxx++;
  assert(sizeof(array)==sizeof(int));
}
