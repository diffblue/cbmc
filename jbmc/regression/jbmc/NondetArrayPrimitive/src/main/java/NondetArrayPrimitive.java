class NondetArrayPrimitive
{
  void intArray(int[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 42) {
      assert false;
    }
  }

  void floatArray(float[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 42.0) {
      assert false;
    }
  }

  void charArray(char[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 'f') {
      assert false;
    }
  }

  void doubleArray(double[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 42.0) {
      assert false;
    }
  }

  void longArray(long[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 42) {
      assert false;
    }
  }

  void shortArray(short[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 42) {
      assert false;
    }
  }

  void byteArray(byte[] array)
  {
    if (array != null && array.length > 1500 && array[1500] == 42) {
      assert false;
    }
  }

  void intArrayMulti(int[][] array)
  {
    if (array != null &&
        array.length > 2 &&
        array[2].length > 50 &&
        array[2][50] == 42) {
      assert false;
    }
  }

}
