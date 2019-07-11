fn main() {
  let a : u32;
  let b = a / 2;
  let c = a / 2;
  {
    let c = c + 1;
    assert!(c > b);
  }
  assert!(c == b);
}
