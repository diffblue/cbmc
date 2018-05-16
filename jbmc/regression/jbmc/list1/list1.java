class LinkedListEntry
{
  public LinkedListEntry Next;
  public int Value; 
}

class LinkedList
{
  public LinkedListEntry Head;
  
  public int size()
  {
    int count = 0;
    for (LinkedListEntry entry = Head; entry != null; entry = entry.Next)
      ++count;
    return count;
  }
  
  public void add(int index, int e)
  {
    LinkedListEntry newEntry = new LinkedListEntry();
    newEntry.Value = e;
    if (index == 0)
    {
      Head = newEntry;
      return;
    }
    LinkedListEntry entry = Head;
    for (int i = 1; i < index; ++i)
      entry = entry.Next;
    entry.Next = newEntry;
  }
  
  public void add(int e)
  {
    add(size(), e);
  }
  
  public void remove(int index)
  {
    LinkedListEntry entry = Head;
    for (int i = 1; i < index; ++i)
      entry = entry.Next;
    entry.Next = entry.Next.Next;
  }
  
  public int get(int index)
  {
    LinkedListEntry entry = Head;
    for (int i = 0; i < index; ++i)
      entry = entry.Next;
    return entry.Value;
  }
}

class __CPROVER_nondet
{
  public static int nondet_int()
  {
    return 0;
  }
}

class __CPROVER_synthesis
{
  public static int accumulator(int aggregated, int e)
  {
    return 0;
  }

  public static boolean predicate(int lhs)
  {
    return true;
  }
}

class list1
{
  private static int stream(LinkedList list)
  {
    // java.util.stream.Stream.filter(...)
    int index = 0;
    for (LinkedListEntry entry = list.Head; entry != null; entry = entry.Next)
      if (__CPROVER_synthesis.predicate(entry.Value))
        ++index;
      else
        list.remove(index);

    // java.util.stream.Stream.reduce(...)
    int aggregated = 0;
    for (LinkedListEntry it = list.Head; it != null; it = it.Next)
      aggregated = __CPROVER_synthesis.accumulator(aggregated, it.Value);

    return aggregated;
  }
  
  public static void main(String[] args)
  {
    LinkedList lhs = new LinkedList();
    LinkedList rhs = new LinkedList();
    int size = 10;
    for (int i = 0; i < size; ++i)
    {
      int value = __CPROVER_nondet.nondet_int();
      lhs.add(i, value);
      rhs.add(i, value);
    }

    int lhs_result = 0;
    for (LinkedListEntry it = lhs.Head; it != null; it = it.Next)
    {
      if (it.Value % 2 == 0)
        if (lhs_result < it.Value)
          lhs_result = it.Value;
    }
    
    int rhs_result = stream(rhs);

    assert(lhs_result == rhs_result);
  }
}
