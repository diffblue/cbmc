public class generic_two_fields {

  // For this to work we need to compile with -g, otherwise the symbols we are looking for 
  // are entering the symbol table as anonlocal::1 and anonlocal::2 and nothing works.  
  class bound_element<NUM extends java.lang.Number> {
    NUM first;
    NUM second;
  }

  bound_element<Integer> belem;
}
