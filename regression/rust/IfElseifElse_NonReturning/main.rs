fn main() {
  let a : u32;

  if a % 3 == 0 {
    assert!(a != 4);
  }
  
  if a % 3 == 0 {
    assert!(a != 5);
  }
  else if a % 3 == 1 {
    assert!(a > 0);
  }
  else {
    assert!(a > 1);
  }
}
