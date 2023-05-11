void main()
{
  int i = 0;

HEAD:
  if(i > 5)
    goto EXIT;
  goto BODY;

LATCH:
  goto HEAD;

BODY:
  i++;
  goto LATCH;

EXIT:;
}
