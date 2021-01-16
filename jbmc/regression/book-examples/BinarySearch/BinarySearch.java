public class BinarySearch {
  public static int binarySearch(int[] array, int value) {
    int lowerBound = 0;
    int upperBound = array.length;
    int i = array.length / 2;
    while(array[i] != value && upperBound > lowerBound + 1) {
      if(array[i] > value) upperBound = i; else lowerBound = i;
      i = (upperBound + lowerBound) / 2;
    }
    return i;
  }
}
