#include <assert.h>

int main(int argc, char *argv[])
{
  // A uniform constant array
  int a[3][3]={{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  // A non-uniform constant array
  int b[3][3]={{0, 1, 2}, {3, 4, 5}, {6, 7, 8}};

  // Test if we can represent uniform constant arrays
  assert(a[1][2]==0);
  assert(a[1][2]==1);

  // Test if we can represent constant arrays which aren't uniform
  assert(b[1][2]==5);
  assert(b[1][2]==0);

  // Test alternative syntax for accessing an array value
  assert(*(b[1]+2)==5);
  assert(*(b[1]+2)==0);
  assert((*(b+1))[2]==5);
  assert((*(b+1))[2]==0);
  assert(*(*(b+1)+2)==5);
  assert(*(*(b+1)+2)==0);
  assert(1[b][2]==5);
  assert(1[b][2]==0);
  assert(*(1[b]+2)==5);
  assert(*(1[b]+2)==0);
  assert((*(1+b))[2]==5);
  assert((*(1+b))[2]==0);
  assert(*(*(1+b)+2)==5);
  assert(*(*(1+b)+2)==0);
  assert(2[1[b]]==5);
  assert(2[1[b]]==0);
  assert(*(2+1[b])==5);
  assert(*(2+1[b])==0);
  assert(*(2+*(1+b))==5);
  assert(*(2+*(1+b))==0);

  // Test how well we can deal with merging for an array value when there is one
  // possible value
  if(argc>2)
  {
    a[0][1]=0;
  }
  assert(a[0][1]==0);
  assert(a[0][1]==1);
  assert(a[0][2]==0);

  // Test how well we can deal with merging for an array value when there are
  // two possible values
  if(argc>2)
  {
    b[0][1]=2;
  }
  assert(b[0][1]==2);
  assert(b[0][1]==3);
  assert(b[0][2]==2);

  // Reset this change to ensure tests later work as expected
  b[0][1]=1;

  // The variables i, j and k will be used as indexes into arrays of size 3.
  // They all require merging paths in the CFG. For i there is only one value on
  // both paths, which is a valid index. The rest can each take two different
  // values. For j both of these values are valid indexes. For k one is and one
  // isn't.
  int i=0;
  int j=0;
  int k=0;
  if(argc>3)
  {
    i=0;
    j=1;
    k=100;
  }

  // Test how well we can deal with merging for an index on a uniform array when
  // the index has one possible value
  assert(a[i][1]==0);
  assert(a[i][1]==1);
  assert(a[1][i]==0);
  assert(a[1][i]==1);
  assert(a[i][i]==0);
  assert(a[i][i]==1);

  // Test how well we can deal with merging for an index on a uniform array when
  // the index has two possible values
  assert(a[j][1]==0);
  assert(a[j][1]==1);
  assert(a[1][j]==0);
  assert(a[1][j]==1);
  assert(a[j][j]==0);
  assert(a[j][j]==1);

  // Test how well we can deal with merging for an index on a non-uniform array

  assert(b[i][1]==1);
  assert(b[i][1]==11);
  assert(b[1][i]==3);
  assert(b[1][i]==11);
  assert(b[i][i]==0);
  assert(b[i][i]==11);

  // Test how well we can deal with merging for an index on a non-uniform array
  assert(b[j][1]==1);
  assert(b[j][1]==11);
  assert(b[1][j]==3);
  assert(b[1][j]==11);
  assert(b[j][j]==0);
  assert(b[j][j]==11);

  // Test how we deal with reading off the end of an array
  assert(a[100][0]==0);
  assert(a[0][100]==0);

  // Test how we deal with writing off the end of an array
  int c=0;
  a[100][0]=1;
  assert(c==0);
  c=0;
  a[0][100]=1;
  assert(c==0);

  // Test how we deal with merging for an index with one possible value when
  // writing to an array
  int ei[3][3]={{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  ei[i][1]=1;
  assert(ei[0][1]==1);
  assert(ei[0][1]==0);
  assert(ei[2][1]==0);
  assert(ei[2][1]==1);

  // Test how we deal with merging for an index with two possible values when
  // writing to an array
  int ej[3][3]={{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  ej[j][1]=1;
  assert(ej[0][1]==0);
  assert(ej[2][1]==0);

  // Test how we deal with merging for an index with two possible values when
  // it means writing to an array element that may be out of bounds
  int ek[3][3]={{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  c=0;
  ek[k][1]=1;
  assert(ek[0][1]==0);
  assert(c==0);

  return 0;
}
