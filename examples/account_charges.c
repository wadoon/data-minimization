#ifndef NOHEADER
//%HEADER%
#endif

int charge(int alter, int einkommen, int treuepunkte) {
    if (alter < 18) return 0;
    if (alter < 27){
        if(einkommen <= 1500) {
            return 0;
        }
        else {
            return 5 - 2 * treuepunkte;
        }
    }

    int g = 10 - 2 * treuepunkte;
    while(einkommen >= 500 && g > 0) {
        g--;  einkommen -= 500;
    }

    return g<0?0:g;
}


int age, income, reward;
int charges;

int main() {
    //%INPUT%
    charges = charge(age, income, reward);
    //%OUTPUT%
}
