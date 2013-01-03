char *p;

int main()
{
  p="";

  // this is bad, as read-only
  *p=1;
}
