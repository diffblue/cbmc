package questions100;

import java.util.*;

public class CombinationSum {
	public ArrayList<ArrayList<Integer>> combinationSum(int[] candidates,
			int target) {
		// Start typing your Java solution below
		// DO NOT write main() function

		Map<Integer, ArrayList<ArrayList<Integer>>> hashMem = new HashMap<Integer, ArrayList<ArrayList<Integer>>>();
		ArrayList<ArrayList<Integer>> result = new ArrayList<ArrayList<Integer>>();
		
		Arrays.sort(candidates);
		Set<Integer> can = new HashSet<Integer>();
		
		if(candidates == null)
		{
			return result;
		}
		
		for (int i = 0; i < candidates.length; i++) {
			can.add(candidates[i]);
		}

		for (int i = 1; i <= target; i++) {
			ArrayList<ArrayList<Integer>> sol = new ArrayList<ArrayList<Integer>>();

			for (int j = 0; j < candidates.length; j++) {
				int diff = i - candidates[j];
				if (diff < 0)
					break;
				else if (diff == 0) {
					ArrayList<Integer> aL = new ArrayList<Integer>();
					aL.add(candidates[j]);
					if(!sol.contains(aL))
						sol.add(aL);
					break;
				}
				else
				{
					if(hashMem.containsKey(diff))
					{
						ArrayList<ArrayList<Integer>> subSol = hashMem.get(diff);
						for(ArrayList<Integer> intList: subSol)
						{
							if(candidates[j] >= intList.get(intList.size() -1))
							{
								ArrayList<Integer> newList = new  ArrayList<Integer>();
								newList.addAll(intList);
								newList.add(candidates[j]);
								if(!sol.contains(newList))
									sol.add(newList);
							}
						}
						continue;
					}			
					if(can.contains(diff))
					{
						if(candidates[j] <= diff)
						{
							ArrayList<Integer> aL = new ArrayList<Integer>();
							aL.add(candidates[j]);
							aL.add(diff);
							if(!sol.contains(aL))
								sol.add(aL);
						}
					}
				}
			}
			if(!sol.isEmpty())
			{
				hashMem.put(i, sol);
			}
		}
		if(hashMem.containsKey(target))
			result = hashMem.get(target);
		return result;
	}
}