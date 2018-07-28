int main()
{
  int arrayOfIntegers[] = {1, 2, 3};
  int *pointer2FirstElem = arrayOfIntegers;
  int *pointer2ThirdElem = arrayOfIntegers + 2;
  int iFirst=(int)pointer2FirstElem;
  int iThird=(int)pointer2ThirdElem;
  int addrDiff = iThird-iFirst;
  __CPROVER_assert(addrDiff == 2* sizeof(int), "");
  return 0;
}
