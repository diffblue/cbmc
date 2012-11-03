int nums[2]; 
int *p; 

int main() { 
  nums[1] = 1; 
  p = &nums[0]; 
  p++; 

  assert(*p == 1); 
} 
