uint64_t main() {
  uint64_t* x;

  x = malloc(8);

  read(0, x, 1);

  *x = *x * 0;

  return *x;
}