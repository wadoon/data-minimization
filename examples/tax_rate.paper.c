#ifndef NOHEADER
//%HEADER%
#endif


int tax_rate(int age, int income) {
  if (age < 18)
    return 0;
  if (age < 25 && !(income > 1000))
    return 10;
  if (income <= 1000)
    return 20;
  return 30;
}

int main() {
    int age;
    int income;
    //%INPUT%
    int TAX_RATE = tax_rate(age, income);
    //%OUTPUT%
}