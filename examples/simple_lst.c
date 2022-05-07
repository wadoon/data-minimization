#ifndef NOHEADER
//%HEADER%
#endif

int einkommen;
int lohnsteuer;
int psatz;

int main() {
    //%INPUT%
    if(einkommen < 10347) {
        lohnsteuer = 0;
    } else {
        if(einkommen < 14926) {
            int Y = (einkommen-10347)/10000;
            lohnsteuer = (1088 * Y + 1.4) * Y;
        } else {
            if(einkommen < 58596) {
                int Z =(einkommen-14926)/10000;
                lohnsteuer =(206 * Z + 2397) * Z + 869;
            } else {
                if(einkommen < 277825) {
                    lohnsteuer= (42 * einkommen)/100 - 9336;
                } else {
                    lohnsteuer = (45 * einkommen)/100 - 17671;
                }
            }
        }
    }

    psatz = lohnsteuer * 100 / einkommen;
    // 0 <= psatz < 100

    // Diskretisierung auf nächste Zehnerstelle.
    if( psatz % 10 >= 5 ) {
        psatz = ((psatz/10)+1)*10;
    } else {
        psatz = (psatz/10)*10; // or psatz - (psatz%10)
    }


    /* int a = psatz/10; // psatz=12, a = 1 */
    /* int l = a*10;     // 10 */
    /* int u = (a+1)*10; // 20 */
    /* int d1 = psatz - l; // 2 */
    /* int d2 = u - psatz; // 8 */
    /* if(d1 < d2) { */
    /*     psatz = d1; */
    /* } */
    /* else { */
    /*     psatz = d2; */
    /* } */
    //%OUTPUT%
}
