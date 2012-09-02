int main()
{
  float temp;
  
  temp = 1.8e307f + 1.5e50f;	// should produce overflow -> +infinity (according to standard)
  assert(__CPROVER_isinf(temp));
  
  float x;
  
  x=temp-temp;
  
  // should be +inf
  assert(__CPROVER_isinf(temp));
}
