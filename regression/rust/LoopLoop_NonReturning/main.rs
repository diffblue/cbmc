fn main() {
  let mut a : u32;
  
  loop {
     a = a / 2;
     
     if a == 0 {
        break;
     }
  }
  
  assert!(a == 0);
}
