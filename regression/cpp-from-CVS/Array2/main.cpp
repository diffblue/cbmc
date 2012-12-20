int y[2][3][4][5];

int main()
{
  for(int i=0; i<5; i++)
    for(int j=0; j<4; j++)
      for(int k=0; k<3; k++)
        for(int l=0; l<2; l++)
          y[i][j][k][l]=2; // out-of-bounds
}

