void main()
{
  int i = 0;
  int j = 0;

HEAD1:
  if(i > 5)
    goto EXIT1;
  goto BODY1;

EXIT1:;
HEAD2:
  if(j > 5)
    goto EXIT2;
  goto BODY2;

BODY1:
  i++;
  goto HEAD1;

BODY2:
  j++;
  goto HEAD2;
EXIT2:;
}
