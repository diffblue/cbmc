import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;


public class CollectionTest {

	public static void Test()
	{
		Collection<Integer> collection = new ArrayList<Integer>() ;
		
		for(int i = 1 ;i < 10 ;++i)
		{
			collection.add(i) ;
		}
		
		for(int value:collection)
		{
			System.out.println(value);
		}
	}
	
	public static void Test2()
	{
		int []iArr = new int[]{ 1,2,3,4} ;
		List<Integer> intList = new ArrayList( Arrays.asList(iArr )) ;
		
	}

	public static void Test3()
	{
		Collection<Integer> collection  = new ArrayList<Integer>(Arrays.asList(1,2,3,4,5)) ;
		Integer []moreInts = {6,7,8,9,10} ;
		collection.addAll(Arrays.asList(moreInts)) ;
		
		Collections.addAll(collection, 11,12,13,14,15) ;
		Collections.addAll(collection, moreInts) ;
		for(int i: collection)
		{
			System.out.print(i + "\t");
		}
	}
	
	public static void IteratorTest()
	{
		List<Integer> intList = new ArrayList<Integer>() ;
		Collections.addAll(intList, 1,2,3,4,5) ;
		
		
//		Iterator<Integer> iterator = intList.iterator() ;
//		iterator.next() ;
//		iterator.remove();
//		while(iterator.hasNext())
//		{
//			System.out.println(iterator.next());
//		}
		
		/////////////////////////////////////////////
		
		ListIterator<Integer> listIterator = intList.listIterator() ;
		while(listIterator.hasNext())
		{
			System.out.println(listIterator.next() + ", " + listIterator.nextIndex() + ", " + listIterator.previousIndex());
		}
		System.out.println("----------------------------------");
		
		while(listIterator.hasPrevious())
		{
			System.out.print(listIterator.previous() + "\t");
		}
		
		while(listIterator.hasNext())
		{
			int value = listIterator.next() ;
			listIterator.set(value*10); 
		}
		while(listIterator.hasPrevious())
		{
			System.out.print(listIterator.previous() + "\t");
		}	
		
	}
	public static void main(String[] args) {
		// TODO Auto-generated method stub

		IteratorTest() ;
		
		
	}

}
