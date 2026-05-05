public class Test
{
  public static void floatToInt(int c, float a, float b)
  {
    switch(c)
    {
    case 0: 
      if (a == 1.5f) {
        int result = (int) a;
        assert result == 1;
      }
      break;
    case 1: 
      if (a == -1.5f) {
        int result = (int) a;
        assert result == -1;
      }
      break;
    case 2: 
      if (a == 1.0f) {
        // Note: dividing by -0.0f has the same behavior as case 3.
        int result = (int)(a / 0.0f);
        // a/b = +inf
        assert result == 2147483647;
      }
      break;
    case 3: 
      if (a == -1.0f) {
        // Note: dividing by -0.0f has the same behavior as case 2.
        int result = (int)(a / 0.0f);
        // a/b = -inf
        assert result == -2147483648;
      }
      break;
    case 4: 
      if (a == 2147483648.0f) {
        // a is not representable as int
        int result = (int) a;
        assert result == 2147483647;
      }
      break;
    case 5: 
      if (a == -4294967296.0f) {
        // a is not representable as int
        int result = (int) a;
        assert result == -2147483648;
      }
      break;
    default: 
      if (a == 0.0f && b == 0.0f) {
        int result = (int)(a / b);
        // a/b = nan
        assert result == 0; 
      }
      break;
    }
  }

  public static void floatToLong(int c, float a, float b)
  {
    switch(c)
    {
    case 0: 
      if (a == 1.5f) {
        long result = (long) a;
        assert result == 1L;
      }
      break;
    case 1: 
      if (a == -1.5f) {
        long result = (long) a;
        assert result == -1L;
      }
      break;
    case 2: 
      if (a == 1.0f) {
        long result = (long)(a / 0.0f);
        // a/b = +inf
        assert result == 9223372036854775807L;
      }
      break;
    case 3: 
      if (a == -1.0f) {
        long result = (long)(a / 0.0f);
        // a/b = -inf
        assert result == -9223372036854775808L;
      }
      break;
    case 4: 
      if (a == 9223372036854775808.0f) {
        // a is not representable as long
        long result = (long) a;
        assert result == 9223372036854775807L;
      }
      break;
    case 5: 
      if (a == -18446744073709551616.0f) {
        // a is not representable as long
        long result = (long) a;
        assert result == -9223372036854775808L;
      }
      break;
    default: 
      if (a == 0.0f && b == 0.0f) {
        long result = (long)(a / b);
        // a/b = nan
        assert result == 0L;
      }
      break;
    }
  }

  public static void doubleToInt(int c, double a, double b)
  {
    switch(c)
    {
    case 0: 
      if (a == 1.5) {
        int result = (int) a;
        assert result == 1;
      }
      break;
    case 1: 
      if (a == -1.5) {
        int result = (int) a;
        assert result == -1;
      }
      break;
    case 2: 
      if (a == 1.0) {
        int result = (int)(a / 0.0);
        // a/b = +inf
        assert result == 2147483647;
      }
      break;
    case 3: 
      if (a == -1.0) {
        int result = (int)(a / 0.0);
        // a/b = -inf
        assert result == -2147483648;
      }
      break;
    case 4: 
      if (a == 2147483648.0) {
        // a is not representable in int
        int result = (int) a;
        assert result == 2147483647;
      }
      break;
    case 5: 
      if (a == -4294967296.0) {
        // a is not representable in int
        int result = (int) a;
        assert result == -2147483648;
      }
      break;
    default: 
      if (a == 0.0 && b == 0.0) {
        int result = (int)(a / b);
        // a/b = nan
        assert result == 0;
      }
      break;
    }
  }
  
  public static void doubleToLong(int c, double a, double b)
  {
    switch(c)
    {
    case 0: 
      if (a == 1.5) {
        long result = (long) a;
        assert result == 1L;
      }
      break;
    case 1: 
      if (a == -1.5) {
        long result = (long) a;
        assert result == -1L;
      }
      break;
    case 2: 
      if (a == 1.0) {
        long result = (long)(a / 0.0);
        // a/b = +inf
        assert result == 9223372036854775807L;
      }
      break;
    case 3: 
      if (a == -1.0) {
        long result = (long)(a / 0.0);
        // a/b = -inf
        assert result == -9223372036854775808L;
      }
      break;
    case 4: 
      if (a == 9223372036854775808.0) {
        // a is not representable in long
        long result = (long) a;
        assert result == 9223372036854775807L;
      }
      break;
    case 5: 
      if (a == -18446744073709551616.0) {
        long result = (long) a;
        // a is not representable in long
        assert result == -9223372036854775808L;
      }
      break;
    default: 
      if (a == 0.0 && b == 0.0) {
        long result = (long)(a / b);
        // a/b = nan
        assert result == 0L;
      }
      break;
    }
  }

}
