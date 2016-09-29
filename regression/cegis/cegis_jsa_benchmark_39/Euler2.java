import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

class Euler2 {

	private static BigInteger sumIfEven(List<Integer> values) {
		BigInteger result = BigInteger.ZERO;
		for (Integer n : values) {
			if (n % 2 == 0) {
				result = result.add(new BigInteger(n.toString()));
			}
		}
		return result;
	}

	private static List<Integer> fibUpTo(int max) {
		List<Integer> nums = new ArrayList<Integer>();

		int next = 1;
		for (int i = 0, j = 0, prev; true; ++i) {
			prev = next;
			next = j + next;
			j = prev; 

			if (next > max)
				break;

			nums.add(next);
		}

		return nums;
	}

	public static void main(String[] args) {
		List<Integer> nums = fibUpTo(4000000);
		System.out.println("The answer is " + sumIfEven(nums));
	}	

}

