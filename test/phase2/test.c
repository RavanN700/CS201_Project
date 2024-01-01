void test() {
  int y = 3;
  int x = 10;
  y = 11;
  if (x > y) {
    x = x + 1;
    y = x + 2;
  } else {
    int z = x;
    x = 4;
  }
  x = y+3;
  y = x-2;
}
