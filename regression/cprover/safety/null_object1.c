int main()
{
  int *p = 0;
  p++;        // still 'null object'
  int x = *p; // unsafe
}
