//this file does pretty much the same as simple-if-else-1-35.c
//but has symbolic exit codes since we only support symbolic exits for now

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 40;
  x = malloc(8);

  read(0, x, 1);

  *x = *x - 47;

  if (*x == 2)
    a = a + *x;
  else
    a = a + (*x * 0);

  if (a == 42)
    return a;
  else
    return *x;
}