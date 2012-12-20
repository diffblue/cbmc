extern char my_string[];

void elsewhere()
{
  char ch;
  // should fail, this is out of bounds
  ch=my_string[10];
}

