#include <assert.h>

// C semantics are that these will be zero
int uninitializedGlobalArray1[2];
int uninitializedGlobalArray2[2];

int main(void)
{
  // Variable access
  long directUseReadLocation; // Non-det

  long x = directUseReadLocation;
  if(0 <= directUseReadLocation && directUseReadLocation < 2)
    assert(uninitializedGlobalArray1[directUseReadLocation] == 0);

  /*** Variable non-redundant update ***/
  // No obvious simplifications to writes

  long nonRedundantWriteLocation;

  if(
    0 <= nonRedundantWriteLocation && nonRedundantWriteLocation < 2 &&
    nonRedundantWriteLocation != 1)
  {
    uninitializedGlobalArray2[nonRedundantWriteLocation] = 1;
  }

  // Constant access
  // Again, constant index into a fully known but non-constant array
  assert(uninitializedGlobalArray2[1] == 0);

  return 0;
}
