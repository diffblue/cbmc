public class test_isempty_nondet
{
   /// Exercises string_constraint_generatort::add_axioms_for_is_empty in
   /// the string-refinement loop. Because the input string is nondet, the
   /// simplifier cannot constant-fold the isEmpty() call and the dispatch
   /// in add_axioms_for_function_application is reached.
   static void checkIsEmpty(String s)
   {
      if (s == null)
         return;
      // Boolean-equivalent encoding: the helper must return
      // length(s) == 0, so this assertion holds for every valid string.
      assert s.isEmpty() == (s.length() == 0);
   }
}
