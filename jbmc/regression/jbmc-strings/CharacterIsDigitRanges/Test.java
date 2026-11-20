public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // digits other than the latin, Arabic-Indic, extended Arabic-Indic,
    // Devanagari and full-width ones
    case 0:
      assert Character.isDigit('\u09e6');
      break;
    case 1:
      assert Character.isDigit(0x1d7ce);
      break;
    }
  }
}
