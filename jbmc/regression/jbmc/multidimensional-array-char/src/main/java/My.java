public class My {
  public int check2DCharArray(char[][] board, boolean assertionCheck) {
    int diff = 0;
    for (int row = 0; row < 2; row++) {
      for (int col = 0; col < 2; col++) {
        if (board[row][col] == 'O') {
          diff++;
          assert !assertionCheck;
          assert diff < 10;
        } else if (board[row][col] == 'X') {
          diff--;
          assert !assertionCheck;
          assert diff < 10 ;
        }
      }
    }
    return diff;
  }
}
