Issues

  int x[4] = {1, 2, 3, 4};
->
  main::1::x () -> {[0] = 00000000000000000000000000000001 @ []
  [1] = 00000000000000000000000000000010 @ []
  [2] = 00000000000000000000000000000011 @ []
  [3] = 00000000000000000000000000000100 @ []
  } @ [1]
  
Problem is that on generation of each element there needs to be a copy
of the instruction location, but this would be a substantial change to the codebase.

Could be handled as a special case.

--

m.age = 10;

main::1::m () -> {.age=00000000000000000000000000001010 @ [2]} @ []

Should be?

main::1::m () -> {.age=00000000000000000000000000001010 @ [2]} @ [2]

tl;dr: Copying objects with subelements.