uint64_t main() {
  uint64_t  a;
  uint64_t  b;
  uint64_t  c;
  uint64_t  i;
  uint64_t* x;

  a = 43;
  b = 2;
  c = 432;
  x = malloc(8);

  *x = 0;

  read(0, x, 1);

  a = a * *x;

  b = b + a;

  b = b / 2;

  c = b - c;

  c = c % 223405432;

  return c;
}
