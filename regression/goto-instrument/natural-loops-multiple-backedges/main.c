int main(int argc, char **argv)
{
loop_header:
  --argc;
  if(argc == 1)
    goto loop_header;
  else if(argc == 2)
    goto loop_header;
  return argc;
}
