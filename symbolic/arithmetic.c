uint64_t main() {
  uint64_t  a;
  uint64_t  b;
  uint64_t  i;
  uint64_t* x;

  a = 43;
  b = 2;
  x = malloc(8);

  read(0, x, 8);

  a = a * *x;

  b = b + a; 

  return b;
}