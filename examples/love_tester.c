#ifndef NOHEADER
//%HEADER%
#endif

const int MIN = 'A';
const int MAX = 'Z';

int OUT, sum, sum0, sum1, sum2,sum3,sum4,sum5,sum6,sum7;

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
    sum0 = (((A0 - B0) < 0 ? B0 - A0 : A0 - B0));
    sum1 = (((A1 - B1) < 0 ? B1 - A1 : A1 - B1));
    sum2 = (((A2 - B2) < 0 ? B2 - A2 : A2 - B2));
    sum3 = (((A3 - B3) < 0 ? B3 - A3 : A3 - B3));
    sum4 = (((A4 - B4) < 0 ? B4 - A4 : A4 - B4));
    sum5 = (((A5 - B5) < 0 ? B5 - A5 : A5 - B5));
    sum6 = (((A6 - B6) < 0 ? B6 - A6 : A6 - B6));
    sum7 = (((A7 - B7) < 0 ? B7 - A7 : A7 - B7));
    sum = sum0 + sum1 + sum2 + sum3 + sum4 + sum5 + sum6 + sum7;
    OUT = ((((8 * (MAX - MIN) - sum) < 0 ? sum - 8 * (MAX - MIN)
                                         : 8 * (MAX - MIN) - sum))
           * 100) / (8 * (MAX - MIN));
  }
  //%OUTPUT%
}
