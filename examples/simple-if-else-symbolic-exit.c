/*
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code, or
performs division by zero or invalid/unsafe memory accesses.

This code is exactly the same as simple-if-else-1-35.c but with symbolic exit codes.
This is necessary since we only support symbolic exit codes so far.

Input == #b00110001 (== 49 == '1')
*/

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 40;
  x = malloc(8);

  *x = 0;

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
