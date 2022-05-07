#ifndef NOHEADER
//%HEADER%
#endif

#define dabs(a,b) (( (a-b)<0 ? b-a : a-b ))

const int MIN = 'A';
const int MAX = 'Z';

int OUT, sum;

int main() {
  int A0;
  int A1;
  int A2;
  int A3;
  int A4;
  int A5;
  int A6;
  int A7;

  int B0;
  int B1;
  int B2;
  int B3;
  int B4;
  int B5;
  int B6;
  int B7;

  //%INPUT%

  OUT = 0;
  sum = 0;

  if (A0 >= MIN && A1 >= MIN && A2 >= MIN && A3 >= MIN && A4 >= MIN &&
      A5 >= MIN && A6 >= MIN && A7 >= MIN && B0 >= MIN && B1 >= MIN &&
      B2 >= MIN && B3 >= MIN && B4 >= MIN && B5 >= MIN && B6 >= MIN &&
      B7 >= MIN && A0 <= MAX && A1 <= MAX && A2 <= MAX && A3 <= MAX &&
      A4 <= MAX && A5 <= MAX && A6 <= MAX && A7 <= MAX && B0 <= MAX &&
      B1 <= MAX && B2 <= MAX && B3 <= MAX && B4 <= MAX && B5 <= MAX &&
      B6 <= MAX && B7 <= MAX) {
    sum = sum + dabs(A0, B0);
    sum = sum + dabs(A1, B1);
    sum = sum + dabs(A2, B2);
    sum = sum + dabs(A3, B3);
    sum = sum + dabs(A4, B4);
    sum = sum + dabs(A5, B5);
    sum = sum + dabs(A6, B6);
    sum = sum + dabs(A7, B7);
    OUT = (dabs(8 * (MAX - MIN), sum) * 100) / (8 * (MAX - MIN));
  }
  //%OUTPUT%
}
