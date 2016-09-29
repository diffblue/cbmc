package arrays;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;



public class ArrayUtils {

	public Integer[] merge(Integer[] array1, Integer[] array2){
		
		List<Integer> returnedList = new ArrayList<Integer>();
		List<Integer> concatList = array1 != null ? new ArrayList<Integer>(Arrays.asList(array1)) : 
								  (array2 != null ? new ArrayList<Integer>(Arrays.asList(array2)) : new ArrayList<Integer>()) ;
		if(array2 != null && array2 != null)
			concatList.addAll(Arrays.asList(array2));

		for(Integer element2: concatList){
			
			if(returnedList.indexOf(element2) == -1){
				returnedList.add(element2);
			}
			
		}
		return (Integer[]) returnedList.toArray(new Integer[returnedList.size()]);
	}
	
	public Integer[] innerJoin(Integer[] array1, Integer[] array2){
		
		List<Integer> returnedList = new ArrayList<Integer>();
		
		for(Integer element1: array1){
			
			for(Integer element2: array2){
				if(element2 == element1){
					returnedList.add(element1);
					break;
				}
			}
		}
		
		return (Integer[]) returnedList.toArray(new Integer[returnedList.size()]);
	}
	
	public Integer[]  leftJoin(Integer[] array1, Integer[] array2){
		
		List<Integer> returnedList = array1 != null  ? new ArrayList<Integer>(Arrays.asList(array1)) :
									(array2 != null ? new ArrayList<Integer>(Arrays.asList(array2)) :
									new ArrayList<Integer>());
		if(array1 != null){
			for(Integer element2: array2){
				
				if(returnedList.indexOf(element2) > -1){
					returnedList.add(element2);
				}
			}
		}

		return (Integer[]) returnedList.toArray(new Integer[returnedList.size()]); 
	}
	
    public Integer[]  outerJoin(Integer[] array1, Integer[] array2){
		
		List<Integer> returnedList = new ArrayList<Integer>();
		List<Integer> concatList = array1 != null ? new ArrayList<Integer>(Arrays.asList(array1)) : 
			  (array2 != null ? new ArrayList<Integer>(Arrays.asList(array2)) : new ArrayList<Integer>()) ;
		if(array1 != null && array2 != null)
			concatList.addAll(Arrays.asList(array2));
		
		for(Integer element1: concatList){
			if(concatList.indexOf(element1) == concatList.lastIndexOf(element1)){
				returnedList.add(element1);
			}
		}

		return (Integer[]) returnedList.toArray(new Integer[returnedList.size()]);
	}
  
}
