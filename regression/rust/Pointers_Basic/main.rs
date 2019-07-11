fn main() {
  let x = 3;
  let y = &x;
  let mut z = *y;

  assert!(z == 3);
}
