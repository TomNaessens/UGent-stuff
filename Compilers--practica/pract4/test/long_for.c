int n = 9999;
int sum = 0;
int foo[10000];

for (int j = 0; j < 100000; j = j + 1) {
  for (int i = 0; i < n; i = i+1) {
    sum = sum + i;
    foo[n] = sum;
  }
}
