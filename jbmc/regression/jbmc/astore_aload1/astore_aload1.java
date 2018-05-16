class astore_aload1
{
  public static void main(String[] args)
  {
    int size = 10;
    boolean[] boolean_array = new boolean[size];
    byte[] byte_array = new byte[size];
    char[] char_array = new char[size];
    short[] short_array = new short[size];
    int[] int_array = new int[size];
    long[] long_array = new long[size];
    double[] double_array = new double[size];
    float[] float_array = new float[size];

    for (int i = 0; i < size; i++) {
      boolean tmp = false;
      if(i % 2 == 0) {
        tmp = true;
      }
      boolean_array[i] = tmp;
      byte_array[i] = (byte) i;
      char_array[i] = (char) i;
      short_array[i] = (short) i;
      int_array[i] = i;
      long_array[i] = (long) i;
      double_array[i] = (double) i;
      float_array[i] = (float) i;
    }

    assert 10 == boolean_array.length;
    assert boolean_array[0];
    assert !boolean_array[1];
    assert boolean_array[2];
    assert !boolean_array[3];
    assert boolean_array[4];
    assert !boolean_array[5];
    assert boolean_array[6];
    assert !boolean_array[7];
    assert boolean_array[8];
    assert !boolean_array[9];
    assert 10 == byte_array.length;
    assert byte_array[0] == (byte) 0;
    assert byte_array[1] == (byte) 1;
    assert byte_array[2] == (byte) 2;
    assert byte_array[3] == (byte) 3;
    assert byte_array[4] == (byte) 4;
    assert byte_array[5] == (byte) 5;
    assert byte_array[6] == (byte) 6;
    assert byte_array[7] == (byte) 7;
    assert byte_array[8] == (byte) 8;
    assert byte_array[9] == (byte) 9;
    assert 10 == short_array.length;
    assert short_array[0] == (short) 0;
    assert short_array[1] == (short) 1;
    assert short_array[2] == (short) 2;
    assert short_array[3] == (short) 3;
    assert short_array[4] == (short) 4;
    assert short_array[5] == (short) 5;
    assert short_array[6] == (short) 6;
    assert short_array[7] == (short) 7;
    assert short_array[8] == (short) 8;
    assert short_array[9] == (short) 9;
    assert 10 == int_array.length;
    assert int_array[0] == 0;
    assert int_array[1] == 1;
    assert int_array[2] == 2;
    assert int_array[3] == 3;
    assert int_array[4] == 4;
    assert int_array[5] == 5;
    assert int_array[6] == 6;
    assert int_array[7] == 7;
    assert int_array[8] == 8;
    assert int_array[9] == 9;
    assert 10 == long_array.length;
    assert long_array[0] == 0L;
    assert long_array[1] == 1L;
    assert long_array[2] == 2L;
    assert long_array[3] == 3L;
    assert long_array[4] == 4L;
    assert long_array[5] == 5L;
    assert long_array[6] == 6L;
    assert long_array[7] == 7L;
    assert long_array[8] == 8L;
    assert long_array[9] == 9L;
    assert 10 == char_array.length;
    assert char_array[0] == (char) 0;
    assert char_array[1] == (char) 1;
    assert char_array[2] == (char) 2;
    assert char_array[3] == (char) 3;
    assert char_array[4] == (char) 4;
    assert char_array[5] == (char) 5;
    assert char_array[6] == (char) 6;
    assert char_array[7] == (char) 7;
    assert char_array[8] == (char) 8;
    assert char_array[9] == (char) 9;
    assert 10 == double_array.length;
    assert (int) double_array[0] == 0;
    assert (int) double_array[1] == 1;
    assert (int) double_array[2] == 2;
    assert (int) double_array[3] == 3;
    assert (int) double_array[4] == 4;
    assert (int) double_array[5] == 5;
    assert (int) double_array[6] == 6;
    assert (int) double_array[7] == 7;
    assert (int) double_array[8] == 8;
    assert (int) double_array[9] == 9;
  }
}
