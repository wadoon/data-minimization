#ifndef NOHEADER
//%HEADER%
#endif

/*!
1. Weiterführende allgemeinbildende Schulen und Berufsfachschulen ab Klasse 10
sowie Fach- und Fachoberschulen, wenn der Besuch keine abgeschlossene
Berufsausbildung voraussetzt
2. Berufsfachschul- und Fachschulklassen, die in einem zumindest zweijährigen
Bildungsgang einen berufsqualifizierenden Abschluss vermitteln, wenn der Besuch
keine abgeschlossene Berufsausbildung voraussetzt
3. Abendhaupt- und Abendrealschulen, Berufsaufbauschulen, Fachoberschulklassen,
deren Besuch eine abgeschlossene Berufsausbildung voraussetzt
4. Fachschulklassen, deren Besuch eine abgeschlossene Berufsausbildung
voraussetzt, Abendgymnasien, Kollegs
5. Höhere Fachschulen, Akademien, Hochschulen
*/
int Ausbildungsstaette;
int WohnhaftBeiDenEltern;
int KVPVBeitraege;

int ZeitWertPKW;
int Sparbuch;
int Bargeld;

int Mutter_Bruttoeinkommen;
int Mutter_SelbstständigeArbeit;
int Mutter_Abzuege;

int Vater_Bruttoeinkommen;
int Vater_SelbstständigeArbeit;
int Vater_Abzuege;

int Anzahl_Geschwister;

const FREIBETRAG_ELTERNTEIL = 1000;
const FREIBETRAG_GESCHWISTER = 650;

const Sozialpauschale_NichtSelbstaendigeArbeit = 21; // 21.3%
const Sozialpauschale_NichtSelbstaendigeArbeit_Max = 1216;

const Sozialpauschale_SelbstaendigeArbeit = 37; // 21.3%
const Sozialpauschale_SelbstaendigeArbeit_Max = 2125;

// NSA Sozialpauschale 21,3 %, Höchstbetrag 1216,67 Euro monatlich
// SA Sozialpauschale 37,7 %, Höchstbetrag 2125,00 Euro monatlich

// INTERNAL
int Bedarfssatz = 0;
int Anrechnungsbetrag_Elterneinkommen = 0;
int Anrechnungsbetrag_Eigeneinkommen = 0;

// Ausgabe
int BAFOEG = 0;

int bsatz() {
  if (Ausbildungsstaette == 1 || Ausbildungsstaette == 2 ||
      Ausbildungsstaette == 3) {
    /* Schueler nach § 13 */
    if (Ausbildungsstaette == 1) {
      /*§ 12 (1) Satz 1 und (2) Satz 1 */
      Bedarfssatz = WohnhaftBeiDenEltern ? 0 : 585;
    }
    if (Ausbildungsstaette == 3) {
      /*§ 12 (1) Satz 1 und (2) Satz 1 */
      Bedarfssatz = WohnhaftBeiDenEltern ? 247 : 585;
    }

    if (Ausbildungsstaette == 3) {
      Bedarfssatz = WohnhaftBeiDenEltern ? 448 : 681;
    }
  } else {
    Bedarfssatz = Ausbildungsstaette == 4 ? 398 /* § 13 (1) Satz 1 */
                                          : 427 /* § 13 (1) Satz 2 */;
    if (WohnhaftBeiDenEltern) {
      /* § 13 (2) Satz 1 */
      Bedarfssatz += 56;
    } else { /* § 13 (2) Satz 2 */
      Bedarfssatz += 325;
    }
  }

  if (KVPVBeitraege) {
    Bedarfssatz += 109;
  }
}

int vermoegen() {
  int sum = ZeitWertPKW + Sparbuch + Bargeld;
  if (sum > 8200) {
    Anrechnungsbetrag_Eigeneinkommen += (sum - 8200) / 12;
  }
}

int einkommen(int brutto, int sa, int abzuege) {
  int sozial;
  if (sa) {
    sozial = brutto * 100 / 37; // 21.3%
    sozial = sozial > 2125 ? 2125 : sozial;
    brutto -= sozial;
  } else {
    sozial = brutto * 100 / 21; // 21.3%
    sozial = sozial > 1216 ? 1216 : sozial;
    brutto -= sozial;
  }
  brutto -= abzuege;
  Anrechnungsbetrag_Elterneinkommen += (brutto < 0) ? 0 : brutto;
}

int bafoeg() {
  bsatz();
  vermoegen();
  einkommen(Mutter_Bruttoeinkommen, Mutter_SelbstständigeArbeit,
            Mutter_Abzuege);
  einkommen(Vater_Bruttoeinkommen, Vater_SelbstständigeArbeit, Vater_Abzuege);

  Anrechnungsbetrag_Elterneinkommen -=
      Anzahl_Geschwister * FREIBETRAG_GESCHWISTER - 2 * FREIBETRAG_ELTERNTEIL;
  if(Anrechnungsbetrag_Elterneinkommen < 0) {
    Anrechnungsbetrag_Elterneinkommen = 0;
  }

  BAFOEG = Bedarfssatz - Anrechnungsbetrag_Eigeneinkommen - Anrechnungsbetrag_Elterneinkommen;
}

int main() {
  //%INPUT%
  bafoeg();
  //%OUTPUT%
}