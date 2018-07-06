void fails(void)
{
  asm volatile ( ".if (0 == 0); .error \"asm error\";.endif" );
}
