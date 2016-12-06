int main()
{
  int altitude;

  __CPROVER_input("altitude", altitude);

  if (altitude > 2500)
  {
    /* instructions */
  }

  return 1;
}
