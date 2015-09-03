int fib[100000];
int n = 100000;

fib[0] = 1;
fib[1] = 1;

for(int j = 0; j < 100000; j = j + 1) {
  for(int i = 2; i < n; i = i + 1) {
    fib[i] = fib[i-2] + fib[i-1];
  }
}
