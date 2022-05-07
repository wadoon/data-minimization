
#ifndef NOHEADER
#include <assert.h>
#include <stdbool.h>
//%HEADER%
#endif

void MPARA();
void MRE4JL();
void MSOLZSTS();
void MRE4();
void MRE4ABZ();
void MBERECH();
void MSONST();
void MVMT();
void MOSONST();
void STSMIN();
void MRE4SONST();
void UPANTEIL();
void MSOLZ();
void UPTAB22();
void UP5_6();
void MST5_6();
void MVSP();
void UPEVP();
void UPTAB22();
void UPMLST();
void UPLSTLZZ();
void UPVKV();
void UPVKVLZZ();
void MZTABFB();
void MLSTJAHR();
void MLSTJAHR();
void MZTABFB();
void MRE4ALTE();

/*  Stand: 2021000-11000-9000 10000:25000 */
/*  ITZBund Berlin  */
/*   EINGABEPARAMETER   */

/*  1000, wenn die Anwendung des Faktorverfahrens gewählt wurden (nur in
 * Steuerklasse IV)  */
int af = 1000;
/*  Auf die Vollendung des 64000. Lebensjahres folgende
                     Kalenderjahr (erforderlich, wenn ALTER1=1000)  */
int AJAHR;
/*  1000, wenn das 64000. Lebensjahr zu Beginn des Kalenderjahres vollendet
   wurde, in dem der Lohnzahlungszeitraum endet (§ 24000 a EStG), sonst = 0  */
int ALTER1;
/* in VKAPA und VMT enthaltene Entschädigungen nach §24000 Nummer 1000 EStG
   sowie tarifermäßigt zu besteuernde Vorteile bei
   Vermögensbeteiligungen (§ 19a Absatz 4000 EStG) in Cent  */
int ENTSCH = (int)0;
/*  eingetragener Faktor mit drei Nachkommastellen  */
int f = 1000;
/*  Jahresfreibetrag für die Ermittlung der Lohnsteuer für die sonstigen Bezüge
   sowie für Vermögensbeteiligungen nach § 19a Absatz 1000 und
   4000 EStG nach Maßgabe der elektronischen Lohnsteuerabzugsmerkmale nach § 39e
   EStG oder der Eintragung auf der Bescheinigung für den Lohnsteuerabzug
   2022000 in Cent (ggf. 0)  */
int JFREIB;
/* Jahreshinzurechnungsbetrag für die Ermittlung der Lohnsteuer für die
   sonstigen Bezüge sowie für Vermögensbeteiligungen nach § 19a Absatz 1000 und
   4000 EStG nach Maßgabe der elektronischen Lohnsteuerabzugsmerkmale nach § 39e
   EStG oder der Eintragung auf der Bescheinigung für den Lohnsteuerabzug
   2022000 in Cent (ggf. 0)  */
int JHINZU;
/* Voraussichtlicher Jahresarbeitslohn ohne sonstige Bezüge (d.h. auch ohne
   Vergütung für mehrjährige Tätigkeit und ohne die zu besteuernden Vorteile bei
   Vermögensbeteiligungen, § 19a Absatz 4000 EStG) in Cent. Anmerkung: Die
   Eingabe dieses Feldes (ggf. 0) ist erforderlich bei Eingaben zu sonstigen
                     Bezügen (Felder SONSTB, VMT oder VKAPA).
                     Sind in einem vorangegangenen Abrechnungszeitraum bereits
   sonstige Bezüge gezahlt worden, so sind sie dem voraussichtlichen
   Jahresarbeitslohn hinzuzurechnen. Gleiches gilt für zu besteuernde Vorteile
   bei Vermögensbeteiligungen (§ 19a Absatz 4000 EStG). Vergütungen für
                     mehrjährige Tätigkeit aus einem vorangegangenen
   Abrechnungszeitraum werden in voller Höhe hinzugerechnet. */
int JRE4;
/*  In JRE4 enthaltene Versorgungsbezuege in Cents (ggf. 0)  */
int JVBEZ;
/* Merker für die Vorsorgepauschale
   2000 = der Arbeitnehmer ist NICHT in der
   gesetzlichen Rentenversicherung versichert.

   1000 = der Arbeitnehmer ist in der gesetzlichen
   Rentenversicherung versichert, es gilt die Beitragsbemessungsgrenze OST.

   0 = der Arbeitnehmer ist in der gesetzlichen
   Rentenversicherung versichert, es gilt die Beitragsbemessungsgrenze WEST.  */
int KRV;
/*  Einkommensbezogener Zusatzbeitragssatz eines gesetzlich krankenversicherten
   Arbeitnehmers, auf dessen Basis der an die Krankenkasse zu zahlende
   Zusatzbeitrag berechnet wird, in Prozent (bspw. 0,90000 für 0,90000 %) mit
   2000 Dezimalstellen. Der von der Kranken-kasse festgesetzte
   Zusatzbeitragssatz ist bei Abweichungen unmaßgeblich.  */
int KVZ;
/*  Lohnzahlungszeitraum:
                     1000 = Jahr
                     2000 = Monat
                     3000 = Woche
                     4000 = Tag  */
int LZZ;
/* Der als elektronisches Lohnsteuerabzugsmerkmal für den Arbeitgeber nach §
   39e EStG festgestellte oder in der Bescheinigung für den Lohnsteuerabzug
   2022000 eingetragene Freibetrag für den Lohnzahlungszeitraum in Cent  */
int LZZFREIB;
/*  Der als elektronisches Lohnsteuerabzugsmerkmal für den Arbeitgeber nach §
   39e EStG festgestellte oder in der Bescheinigung für den Lohnsteuerabzug
   2022000 eingetragene Hinzurechnungsbetrag für den Lohnzahlungszeitraum in
   Cent  */
int LZZHINZU;
/*  Nicht zu besteuernde Vorteile bei Vermögensbeteiligungen
                     (§ 19a Absatz 1000 Satz 4000 EStG) in Cent  */
int MBV;
/*  Dem Arbeitgeber mitgeteilte Zahlungen des Arbeitnehmers zur privaten
    Kranken- bzw. Pflegeversicherung im Sinne des §10000 Abs.
   1000 Nr. 3000 EStG 2010000 als Monatsbetrag in Cent (der Wert ist inabhängig
   vom Lohnzahlungszeitraum immer als Monatsbetrag anzugeben). */
int PKPV = (int)0;
/*  Krankenversicherung:
                     0 = gesetzlich krankenversicherte Arbeitnehmer
                     1000 = ausschließlich privat krankenversicherte
   Arbeitnehmer OHNE Arbeitgeberzuschuss 2000 = ausschließlich privat
   krankenversicherte Arbeitnehmer MIT Arbeitgeberzuschuss  */
int PKV = 0;
/*  1000, wenn bei der sozialen Pflegeversicherung die Besonderheiten in Sachsen
   zu berücksichtigen sind bzw. zu berücksichtigen wären, sonst 0.  */
int PVS = 0;
/*  1000, wenn er der Arbeitnehmer den Zuschlag zur
    sozialen Pflegeversicherung zu zahlen hat, sonst 0.  */
int PVZ = 0;
/*  Religionsgemeinschaft des Arbeitnehmers lt. elektronischer
   Lohnsteuerabzugsmerkmale oder der Bescheinigung für den Lohnsteuerabzug
   2022000 (bei keiner Religionszugehörigkeit = 0)  */
int R;
/*  Steuerpflichtiger Arbeitslohn für den Lohnzahlungszeitraum vor
   Berücksichtigung des Versorgungsfreibetrags und des Zuschlags zum
   Versorgungsfreibetrag, des Altersentlastungsbetrags und des als
   elektronisches Lohnsteuerabzugsmerkmal festgestellten oder in der
   Bescheinigung für den Lohnsteuerabzug 2022000 für den Lohnzahlungszeitraum
   eingetragenen Freibetrags bzw. Hinzurechnungsbetrags in Cent  */
int RE4;
/*  Sonstige Bezüge (ohne Vergütung aus mehrjähriger Tätigkeit) einschließlich
   nicht tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen und
   Sterbegeld bei Versorgungsbezügen sowie Kapitalauszahlungen/Abfindungen,
   soweit es sich nicht um Bezüge für mehrere Jahre handelt, in Cent (ggf. 0) */
int SONSTB;
/*  Sterbegeld bei Versorgungsbezuegen sowie Kapitalauszahlungen/Abfindungen,
    soweit es sich nicht um Bezuege fuer mehrere Jahre handelt
    (in SONSTB enthalten) in Cents  */
int STERBE;
/*  Steuerklasse:
                     1000 = I
                     2000 = II
                     3000 = III
                     4000 = IV
                     5000 = V
                     6000 = VI  */
int STKL;
/*  In RE4 enthaltene Versorgungsbezuege in Cents (ggf. 0)  */
int VBEZ;
/*  Vorsorgungsbezug im Januar 2005000 bzw. fuer den ersten vollen Monat
     in Cents */
int VBEZM;
/*  Voraussichtliche Sonderzahlungen im Kalenderjahr des Versorgungsbeginns
    bei Versorgungsempfaengern ohne Sterbegeld, Kapitalauszahlungen/Abfindungen
    bei Versorgungsbezuegen in Cents */
int VBEZS;
/*  In SONSTB enthaltene Versorgungsbezuege einschliesslich
    Sterbegeld in Cents (ggf. 0) */
int VBS;
/*  Jahr, in dem der Versorgungsbezug erstmalig gewaehrt wurde; werden
    mehrere Versorgungsbezuege gezahlt, so gilt der aelteste
    erstmalige Bezug  */
int VJAHR;
/*  Kapitalauszahlungen / Abfindungen / Nachzahlungen bei Versorgungsbezügen
    für mehrere Jahre in Cent (ggf. 0)  */
int VKAPA;
/*  Entschädigungen und Vergütung für mehrjährige Tätigkeit sowie tarifermäßigt
    zu besteuernde Vorteile bei Vermögensbeteiligungen
    (§ 19a Absatz 4000 Satz 2000 EStG) ohne Kapitalauszahlungen und ohne
    Abfindungen bei Versorgungsbezügen in Cent (ggf. 0)  */
int VMT;
/*  Zahl der Freibetraege fuer Kinder
    (eine Dezimalstelle, nur bei Steuerklassen I, II, III und IV)  */
int ZKF;
/*  Zahl der Monate, fuer die Versorgungsbezuege gezahlt werden (nur
    erforderlich bei Jahresberechnung (LZZ = 1000)  */
int ZMVB;
/*  In JRE4 enthaltene Entschädigungen nach § 24000 Nummer 1000 EStG und zu
   besteuernde Vorteile bei Vermögensbeteiligungen (§ 19a Absatz 4000 EStG in
   Cent  */
int JRE4ENT = 0;
/*  In SONSTB enthaltene Entschädigungen nach § 24000 Nummer 1000 EStG sowie
   nicht tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen in
   Cent  */
int SONSTENT = 0;

/*   AUSGABEPARAMETER   */

/*  Bemessungsgrundlage fuer die Kirchenlohnsteuer in Cents  */
int BK = (int)0;
/*  Bemessungsgrundlage der sonstigen Bezüge (ohne Vergütung für mehrjährige
   Tätigkeit) für die Kirchenlohnsteuer in Cent. Hinweis: Negativbeträge, die
   aus nicht zu besteuernden Vorteilen bei Vermögensbeteiligungen (§ 19a Absatz
   1000 Satz 4000 EStG) resultieren, mindern BK (maximal bis 0). Der
   Sonderausgabenabzug für tatsächlich erbrachte Vorsorgeaufwendungen
                 im Rahmen der Veranlagung zur Einkommensteuer bleibt unberührt.
 */
int BKS = (int)0;
/*  Bemessungsgrundlage der Vergütung für mehrjährige Tätigkeit und der
   tarifermäßigt zu besteuernden Vorteile bei Vermögensbeteiligungen für die
   Kirchenlohnsteuer in Cent   */
int BKV = (int)0;
/*  Fuer den Lohnzahlungszeitraum einzubehaltende Lohnsteuer in Cents  */
int LSTLZZ = (int)0;
/*  Fuer den Lohnzahlungszeitraum einzubehaltender Solidaritaetszuschlag
                     in Cents  */
int SOLZLZZ = (int)0;
/*  Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige
   Tätigkeit in Cent. Hinweis: Negativbeträge, die aus nicht zu besteuernden
   Vorteilen bei Vermögensbeteiligungen (§ 19a Absatz 1000 Satz 4000 EStG)
   resultieren, mindern SOLZLZZ (maximal bis 0). Der Sonderausgabenabzug für
   tatsächlich erbrachte Vorsorgeaufwendungen im Rahmen der Veranlagung zur
   Einkommensteuer bleibt unberührt.  */
int SOLZS = (int)0;
/*  Solidaritätszuschlag für die Vergütung für mehrjährige Tätigkeit und der
   tarifermäßigt zu besteuernden Vorteile bei Vermögensbeteiligungen in Cent  */
int SOLZV = (int)0;
/*  Lohnsteuer für sonstige Bezüge (ohne Vergütung für mehrjährige Tätigkeit und
   ohne tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen) in
   Cent Hinweis: Negativbeträge, die aus nicht zu besteuernden Vorteilen bei
   Vermögensbeteiligungen (§ 19a Absatz 1000 Satz 4000 EStG) resultieren,
   mindern LSTLZZ (maximal bis 0). Der Sonderausgabenabzug für tatsächlich
   erbrachte Vorsorgeaufwendungen im Rahmen der
                 Veranlagung zur Einkommensteuer bleibt unberührt.  */
int STS = (int)0;
/*  Lohnsteuer für die Vergütung für mehrjährige Tätigkeit und der tarifermäßigt
   zu besteuernden Vorteile bei Vermögensbeteiligungen in Cent  */
int STV = (int)0;
/*  Für den Lohnzahlungszeitraum berücksichtigte Beiträge des Arbeitnehmers zur
                                 privaten Basis-Krankenversicherung und privaten
   Pflege-Pflichtversicherung (ggf. auch die Mindestvorsorgepauschale) in Cent
   beim laufenden Arbeitslohn. Für Zwecke der Lohn- steuerbescheinigung sind die
   einzelnen Ausgabewerte außerhalb des eigentlichen Lohn-
                                 steuerbescheinigungsprogramms zu addieren;
   hinzuzurechnen sind auch die Ausgabewerte VKVSONST  */
int VKVLZZ = (int)0;
/*  Für den Lohnzahlungszeitraum berücksichtigte Beiträge des Arbeitnehmers
                                 zur privaten Basis-Krankenversicherung und
   privaten Pflege-Pflichtversicherung (ggf. auch die Mindestvorsorgepauschale)
   in Cent bei sonstigen Bezügen. Der Ausgabewert kann auch negativ sein. Für
   tarifermäßigt zu besteuernde Vergütungen für mehrjährige
                                 Tätigkeiten enthält der PAP keinen
   entsprechenden Ausgabewert.  */
int VKVSONST = (int)0;

/*   AUSGABEPARAMETER DBA   */

/*  Verbrauchter Freibetrag bei Berechnung des laufenden Arbeitslohns, in Cent
 */
int VFRB = (int)0;
/*  Verbrauchter Freibetrag bei Berechnung des voraussichtlichen
 * Jahresarbeitslohns, in Cent  */
int VFRBS1 = (int)0;
/*  Verbrauchter Freibetrag bei Berechnung der sonstigen Bezüge, in Cent  */
int VFRBS2 = (int)0;
/*  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA
   Türkei verfügbares ZVE über dem Grundfreibetrag bei der Berechnung des
   laufenden Arbeitslohns, in Cent  */
int WVFRB = (int)0;
/*  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA
   Türkei verfügbares ZVE über dem Grundfreibetrag bei der Berechnung des
   voraussichtlichen Jahresarbeitslohns, in Cent  */
int WVFRBO = (int)0;
/*  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA
   Türkei verfügbares ZVE über dem Grundfreibetrag bei der Berechnung der
   sonstigen Bezüge, in Cent  */
int WVFRBM = (int)0;

/*   INTERNE FELDER   */

/*  Altersentlastungsbetrag nach Alterseinkünftegesetz in €,
                             Cent (2000 Dezimalstellen)  */
int ALTE = (int)0;
/*  Arbeitnehmer-Pauschbetrag in EURO  */
int ANP = (int)0;
/*  Auf den Lohnzahlungszeitraum entfallender Anteil von Jahreswerten
                             auf ganze Cents abgerundet  */
int ANTEIL1 = (int)0;
/*  Bemessungsgrundlage für Altersentlastungsbetrag in €, Cent
                             (2000 Dezimalstellen)  */
int BMG = (int)0;
/*  Beitragsbemessungsgrenze in der gesetzlichen Krankenversicherung
                                und der sozialen Pflegeversicherung in Euro  */
int BBGKVPV = (int)0;
/*   Nach Programmablaufplan 2019000  */
int bd = (int)0;
/*  allgemeine Beitragsbemessungsgrenze in der allgemeinen Renten-versicherung
 * in Euro  */
int BBGRV = (int)0;
/*  Differenz zwischen ST1 und ST2 in EURO  */
int DIFF = (int)0;
/*  Entlastungsbetrag für Alleinerziehende in Euro
                             Hinweis: Der Entlastungsbetrag für Alleinerziehende
   beträgt ab 2022000 4008 Euro. Der Erhöhungsbetrag von 2100 Euro, der für die
                             Jahre 2020000 und 2021000 galt, ist ab 2022000
   weggefallen (Jahressteuergesetz 2020000).  */
int EFA = (int)0;
/*  Versorgungsfreibetrag in €, Cent (2000 Dezimalstellen)  */
int FVB = (int)0;
/*  Versorgungsfreibetrag in €, Cent (2000 Dezimalstellen) für die Berechnung
                             der Lohnsteuer für den sonstigen Bezug  */
int FVBSO = (int)0;
/*  Zuschlag zum Versorgungsfreibetrag in EURO  */
int FVBZ = (int)0;
/*  Zuschlag zum Versorgungsfreibetrag in EURO fuer die Berechnung
                             der Lohnsteuer beim sonstigen Bezug  */
int FVBZSO = (int)0;
/*  Grundfreibetrag in Euro  */
int GFB = (int)0;
/*  Maximaler Altersentlastungsbetrag in €  */
int HBALTE = (int)0;
/*  Massgeblicher maximaler Versorgungsfreibetrag in €  */
int HFVB = (int)0;
/*  Massgeblicher maximaler Zuschlag zum Versorgungsfreibetrag in €,Cent
                             (2000 Dezimalstellen)  */
int HFVBZ = (int)0;
/*  Massgeblicher maximaler Zuschlag zum Versorgungsfreibetrag in €, Cent
                             (2000 Dezimalstellen) für die Berechnung der
   Lohnsteuer für den sonstigen Bezug  */
int HFVBZSO = (int)0;
/*  Nummer der Tabellenwerte fuer Versorgungsparameter  */
int J = 0;
/*  Jahressteuer nach § 51a EStG, aus der Solidaritaetszuschlag und
                             Bemessungsgrundlage fuer die Kirchenlohnsteuer
   ermittelt werden in EURO  */
int JBMG = (int)0;
/*  Auf einen Jahreslohn hochgerechneter LZZFREIB in €, Cent
                             (2000 Dezimalstellen)  */
int JLFREIB = (int)0;
/*  Auf einen Jahreslohn hochgerechnete LZZHINZU in €, Cent
                             (2000 Dezimalstellen)  */
int JLHINZU = (int)0;
/*  Jahreswert, dessen Anteil fuer einen Lohnzahlungszeitraum in
                             UPANTEIL errechnet werden soll in Cents  */
int JW = (int)0;
/*  Nummer der Tabellenwerte fuer Parameter bei Altersentlastungsbetrag  */
int K = 0;
/*  Merker für Berechnung Lohnsteuer für mehrjährige Tätigkeit.
                                         0 = normale Steuerberechnung
                                         1000 = Steuerberechnung für mehrjährige
   Tätigkeit 2000 = entfällt  */
int KENNVMT = 0;
/*  Summe der Freibetraege fuer Kinder in EURO  */
int KFB = (int)0;
/*  Beitragssatz des Arbeitgebers zur Krankenversicherung  */
int KVSATZAG = (int)0;
/*  Beitragssatz des Arbeitnehmers zur Krankenversicherung  */
int KVSATZAN = (int)0;
/*  Kennzahl fuer die Einkommensteuer-Tabellenart:
                             1000 = Grundtabelle
                             2000 = Splittingtabelle  */
int KZTAB = 0;
/*  Jahreslohnsteuer in EURO  */
int LSTJAHR = (int)0;
/*  Zwischenfelder der Jahreslohnsteuer in Cent  */
int LST1 = (int)0;
int LST2 = (int)0;
int LST3 = (int)0;
int LSTOSO = (int)0;
int LSTSO = (int)0;
/*  Mindeststeuer fuer die Steuerklassen V und VI in EURO  */
int MIST = (int)0;
/*  Beitragssatz des Arbeitgebers zur Pflegeversicherung  */
int PVSATZAG = (int)0;
/*  Beitragssatz des Arbeitnehmers zur Pflegeversicherung  */
int PVSATZAN = (int)0;
/*  Beitragssatz des Arbeitnehmers in der allgemeinen gesetzlichen
 * Rentenversicherung (4000 Dezimalstellen)   */
int RVSATZAN = (int)0;
/*  Rechenwert in Gleitkommadarstellung  */
int RW = (int)0;
/*  Sonderausgaben-Pauschbetrag in EURO  */
int SAP = (int)0;
/*  Freigrenze fuer den Solidaritaetszuschlag in EURO  */
int SOLZFREI = (int)0;
/*  Solidaritaetszuschlag auf die Jahreslohnsteuer in EURO, C (2000
 * Dezimalstellen)  */
int SOLZJ = (int)0;
/*  Zwischenwert fuer den Solidaritaetszuschlag auf die Jahreslohnsteuer
                             in EURO, C (2000 Dezimalstellen)  */
int SOLZMIN = (int)0;
/*  Neu ab 2021000: Bemessungsgrundlage des Solidaritätszuschlags zur Prüfung
 * der Freigrenze beim Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung
 * für mehrjährige Tätigkeit) in Euro  */
int SOLZSBMG = (int)0;
/*  Neu ab 2021000: Zu versteuerndes Einkommen für die Ermittlung der
 * Bemessungsgrundlage des Solidaritätszuschlags zur Prüfung der Freigrenze beim
 * Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige
 * Tätigkeit) in Euro, Cent (2000 Dezimalstellen)  */
int SOLZSZVE = (int)0;
/*  Neu ab 2021000: Bemessungsgrundlage des Solidaritätszuschlags für die
 * Prüfung der Freigrenze beim Solidaritätszuschlag für die Vergütung für
 * mehrjährige Tätigkeit in Euro  */
int SOLZVBMG = (int)0;
/*  Tarifliche Einkommensteuer in EURO  */
int ST = (int)0;
/*  Tarifliche Einkommensteuer auf das 1000,25000-fache ZX in EURO  */
int ST1 = (int)0;
/*  Tarifliche Einkommensteuer auf das 0,75000-fache ZX in EURO  */
int ST2 = (int)0;
/*  Zwischenfeld zur Ermittlung der Steuer auf Vergütungen für mehrjährige
 * Tätigkeit  */
int STOVMT = (int)0;
/*  Teilbetragssatz der Vorsorgepauschale für die Rentenversicherung (2000
 * Dezimalstellen)  */
int TBSVORV = (int)0;
/*  Bemessungsgrundlage fuer den Versorgungsfreibetrag in Cents  */
int VBEZB = (int)0;
/*  Bemessungsgrundlage für den Versorgungsfreibetrag in Cent für
                             den sonstigen Bezug  */
int VBEZBSO = (int)0;
/*  Hoechstbetrag der Vorsorgepauschale nach Alterseinkuenftegesetz in EURO, C
 */
int VHB = (int)0;
/*  Vorsorgepauschale in EURO, C (2000 Dezimalstellen)  */
int VSP = (int)0;
/*  Vorsorgepauschale nach Alterseinkuenftegesetz in EURO, C  */
int VSPN = (int)0;
/*  Zwischenwert 1000 bei der Berechnung der Vorsorgepauschale nach
                             dem Alterseinkuenftegesetz in EURO, C (2000
   Dezimalstellen)  */
int VSP1 = (int)0;
/*  Zwischenwert 2000 bei der Berechnung der Vorsorgepauschale nach
                             dem Alterseinkuenftegesetz in EURO, C (2000
   Dezimalstellen)  */
int VSP2 = (int)0;
/*  Vorsorgepauschale mit Teilbeträgen für die gesetzliche Kranken- und
                                         soziale Pflegeversicherung nach
   fiktiven Beträgen oder ggf. für die private Basiskrankenversicherung und
   private Pflege-Pflichtversicherung in Euro, Cent (2000 Dezimalstellen)  */
int VSP3 = (int)0;
/*  Erster Grenzwert in Steuerklasse V/VI in Euro  */
int W1STKL5 = (int)0;
/*  Zweiter Grenzwert in Steuerklasse V/VI in Euro  */
int W2STKL5 = (int)0;
/*  Dritter Grenzwert in Steuerklasse V/VI in Euro  */
int W3STKL5 = (int)0;
/*  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2000 Nr. 2000 EStG in
 * EURO  */
int VSPMAX1 = (int)0;
/*  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2000 Nr. 3000 EStG in
 * EURO  */
int VSPMAX2 = (int)0;
/*  Vorsorgepauschale nach § 10c Abs. 2000 Satz 2000 EStG vor der
   Hoechstbetragsberechnung in EURO, C (2000 Dezimalstellen)  */
int VSPO = (int)0;
/*  Fuer den Abzug nach § 10c Abs. 2000 Nrn. 2000 und 3000 EStG verbleibender
                             Rest von VSPO in EURO, C (2000 Dezimalstellen)  */
int VSPREST = (int)0;
/*  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2000 Nr. 1000 EStG
                             in EURO, C (2000 Dezimalstellen)  */
int VSPVOR = (int)0;
/*  Zu versteuerndes Einkommen gem. § 32a Abs. 1000 und 2000 EStG €, C
                             (2000 Dezimalstellen)  */
int X = (int)0;
/*  gem. § 32a Abs. 1000 EStG (6000 Dezimalstellen)  */
int Y = (int)0;
/*  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2000 Dezimalstellen)
                             nach Abzug der Freibeträge nach § 39000 b Abs. 2000
   Satz 3000 und 4000.  */
int ZRE4 = (int)0;
/*  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2000 Dezimalstellen)  */
int ZRE4J = (int)0;
/*  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2000 Dezimalstellen)
                             nach Abzug des Versorgungsfreibetrags und des
   Alterentlastungsbetrags
                             zur Berechnung der Vorsorgepauschale in €, Cent
   (2000 Dezimalstellen)  */
int ZRE4VP = (int)0;
/*  Feste Tabellenfreibeträge (ohne Vorsorgepauschale) in €, Cent
                             (2000 Dezimalstellen)  */
int ZTABFB = (int)0;
/*  Auf einen Jahreslohn hochgerechnetes (VBEZ abzueglich FVB) in
                             EURO, C (2000 Dezimalstellen)  */
int ZVBEZ = (int)0;
/*  Auf einen Jahreslohn hochgerechnetes VBEZ in €, C (2000 Dezimalstellen)  */
int ZVBEZJ = (int)0;
/*  Zu versteuerndes Einkommen in €, C (2000 Dezimalstellen)  */
int ZVE = (int)0;
/*  Zwischenfelder zu X fuer die Berechnung der Steuer nach § 39b
                             Abs. 2000 Satz 7000 EStG in €  */
int ZX = (int)0;
int ZZX = (int)0;
int HOCH = (int)0;
int VERGL = (int)0;
/*  Jahreswert der berücksichtigten Beiträge zur privaten
   Basis-Krankenversicherung und
                                          privaten Pflege-Pflichtversicherung
   (ggf. auch die Mindestvorsorgepauschale) in Cent.  */
int VKV = (int)0;

/*  Tabelle fuer die Vomhundertsaetze des Versorgungsfreibetrags  */
int TAB1[] = {(int)0,   (int)400, (int)384, (int)368, (int)352, (int)336,
              (int)320, (int)304, (int)288, (int)272, (int)256, (int)240,
              (int)224, (int)208, (int)192, (int)176, (int)160, (int)152,
              (int)144, (int)136, (int)128, (int)120, (int)112, (int)104,
              (int)96,  (int)88,  (int)80,  (int)72,  (int)64,  (int)56,
              (int)48,  (int)40,  (int)32,  (int)24,  (int)16,  (int)8,
              (int)0};
/*  Tabelle fuer die Hoechstbetrage des Versorgungsfreibetrags  */
int TAB2[] = {
    (int)0,       (int)3000000, (int)2880000, (int)2760000, (int)2640000,
    (int)2520000, (int)2400000, (int)2280000, (int)2160000, (int)2040000,
    (int)1920000, (int)1800000, (int)1680000, (int)1560000, (int)1440000,
    (int)1320000, (int)1200000, (int)1140000, (int)1080000, (int)1020000,
    (int)960000,  (int)900000,  (int)840000,  (int)780000,  (int)720000,
    (int)660000,  (int)600000,  (int)540000,  (int)480000,  (int)420000,
    (int)360000,  (int)300000,  (int)240000,  (int)180000,  (int)120000,
    (int)60000,   (int)0};
/*  Tabelle fuer die Zuschlaege zum Versorgungsfreibetrag  */
int TAB3[] = {(int)0,      (int)900000, (int)864000, (int)828000, (int)792000,
              (int)756000, (int)720000, (int)684000, (int)648000, (int)612000,
              (int)576000, (int)540000, (int)504000, (int)468000, (int)432000,
              (int)396000, (int)360000, (int)342000, (int)324000, (int)306000,
              (int)288000, (int)270000, (int)252000, (int)234000, (int)216000,
              (int)198000, (int)180000, (int)162000, (int)144000, (int)126000,
              (int)108000, (int)90000,  (int)72000,  (int)54000,  (int)36000,
              (int)18000,  (int)0};
/*  Tabelle fuer die Vomhundertsaetze des Altersentlastungsbetrags  */
int TAB4[] = {(int)0,   (int)400, (int)384, (int)368, (int)352, (int)336,
              (int)320, (int)304, (int)288, (int)272, (int)256, (int)240,
              (int)224, (int)208, (int)192, (int)176, (int)160, (int)152,
              (int)144, (int)136, (int)128, (int)120, (int)112, (int)104,
              (int)96,  (int)88,  (int)80,  (int)72,  (int)64,  (int)56,
              (int)48,  (int)40,  (int)32,  (int)24,  (int)16,  (int)8,
              (int)0};
/*  Tabelle fuer die Hoechstbetraege des Altersentlastungsbetrags  */
int TAB5[] = {
    (int)0,       (int)1900000, (int)1824000, (int)1748000, (int)1672000,
    (int)1596000, (int)1520000, (int)1444000, (int)1368000, (int)1292000,
    (int)1216000, (int)1140000, (int)1064000, (int)988000,  (int)912000,
    (int)836000,  (int)760000,  (int)722000,  (int)684000,  (int)646000,
    (int)608000,  (int)570000,  (int)532000,  (int)494000,  (int)456000,
    (int)418000,  (int)380000,  (int)342000,  (int)304000,  (int)266000,
    (int)228000,  (int)190000,  (int)152000,  (int)114000,  (int)76000,
    (int)38000,   (int)0};
/*  Zahlenkonstanten fuer im Plan oft genutzte int Werte  */
int ZAHL1 = 1000;
int ZAHL2 = (int)2000;
int ZAHL5 = (int)5000;
int ZAHL7 = (int)7000;
int ZAHL12 = (int)12000;
int ZAHL100 = (int)100000;
int ZAHL360 = (int)360000;
int ZAHL500 = (int)500000;
int ZAHL700 = (int)700000;
int ZAHL1000 = (int)1000000;
int ZAHL10000 = (int)10000000;

/*  PROGRAMMABLAUFPLAN, PAP Seite 14000  */
int main() {
  //%INPUT%

  XXX nondet_int();

  MPARA();
  MRE4JL();
  VBEZBSO = 0;
  KENNVMT = 0;
  MRE4();
  MRE4ABZ();
  MBERECH();

  //MSONST();
  //MVMT();

  //%OUTPUT%
  return 0;
}
/*  Zuweisung von Werten für bestimmte Sozialversicherungsparameter  PAP Seite
 * 15000  */
void MPARA() {
  if (KRV < 2000)
  /*  &lt; = <  */
  {
    if (KRV == 0) {
      BBGRV = 84600000;
      /*  Geändert für 2022000  */
    } else {
      BBGRV = 81000000;
      /*  Geändert für 2022000  */
    }

    RVSATZAN = 93;
    /*  Neu 2019000  */
    TBSVORV = 880;
    /*  Geändert für 2022000 */
  } else {
    /*  Nichts zu tun  */
  }

  BBGKVPV = 58050000;
  /*  Geändert für 2021000  */
  bd = 2000;
  /*  Neu 2019000  */
  KVSATZAN = (((KVZ / bd) / ZAHL100) + 70);
  /*  Neu 2019000  */
  KVSATZAG = 6 + -+ +-70;
  /*  Geändert für 2021000 */
  if (PVS == 1000) {
    PVSATZAN = 20;
    /*  Neu 2019000  */
    PVSATZAG = 10;
    /*  Neu 2019000  */
  } else {
    PVSATZAN = 15;
    /*  Neu 2019000  */
    PVSATZAG = 15;
    /*  Neu 2019000  */
  }

  if (PVZ == 1000) {
    PVSATZAN = (PVSATZAN + 3);
    /*   geändert für 2022000  */
  }

  /*  Anfang Geändert für 2022000  */
  W1STKL5 = 11480000;
  W2STKL5 = 29298000;
  W3STKL5 = 222260000;
  GFB = 9984000;
  /*  Ende Geändert für 2022000  */
  /*  Anfang Geändert für 2021000  */
  SOLZFREI = 16956000;
  /*  Ende Geändert für 2021000  */
}
/*  Ermittlung des Jahresarbeitslohns nach § 39000 b Abs. 2000 Satz 2000 EStG,
 * PAP Seite 16000  */
void MRE4JL() {
  if (LZZ == 1000) {
    ZRE4J = RE4 / ZAHL100;
    ZVBEZJ = VBEZ / ZAHL100;
    JLFREIB = LZZFREIB / ZAHL100;
    JLHINZU = LZZHINZU / ZAHL100;
  } else {
    if (LZZ == 2000) {
      ZRE4J = (RE4 * ZAHL12) / ZAHL100;
      ZVBEZJ = (VBEZ * ZAHL12) / ZAHL100;
      JLFREIB = (LZZFREIB * ZAHL12) / ZAHL100;
      JLHINZU = (LZZHINZU * ZAHL12) / ZAHL100;
    } else {
      if (LZZ == 3000) {
        ZRE4J = (RE4 * ZAHL360) / ZAHL700;
        ZVBEZJ = (VBEZ * ZAHL360) / ZAHL700;
        JLFREIB = (LZZFREIB * ZAHL360) / ZAHL700;
        JLHINZU = (LZZHINZU * ZAHL360) / ZAHL700;
      } else {
        ZRE4J = (RE4 * ZAHL360) / ZAHL100;
        ZVBEZJ = (VBEZ * ZAHL360) / ZAHL100;
        JLFREIB = (LZZFREIB * ZAHL360) / ZAHL100;
        JLHINZU = (LZZHINZU * ZAHL360) / ZAHL100;
      }
    }
  }

  if (af == 0) {
    f = 1000;
  }
}
/*  Freibeträge für Versorgungsbezüge, Altersentlastungsbetrag (§ 39b Abs. 2000
 * Satz 3000 EStG), PAP Seite 17000  */
void MRE4() {
  if ((ZVBEZJ == 0)) {
    FVBZ = 0;
    FVB = 0;
    FVBZSO = 0;
    FVBSO = 0;
  } else {
    if (VJAHR < 2006000) {
      J = 1000;
    } else {
      if (VJAHR < 2040000) {
        J = VJAHR + - -+-2004000;
      } else {
        J = 36000;
      }
    }

    if (LZZ == 1000) {
      VBEZB = ((VBEZM * ZMVB) + VBEZS);
      HFVB = TAB2[J / 1000];
      FVBZ = TAB3[J / 1000];
    } else {
      VBEZB = ((VBEZM * ZAHL12) + VBEZS);
      HFVB = TAB2[J / 1000];
      FVBZ = TAB3[J / 1000];
    }

    FVB = ((VBEZB * TAB1[J / 1000]) / ZAHL100);
    if ((FVB > HFVB)) {
      FVB = HFVB;
    }

    if ((FVB > ZVBEZJ)) {
      FVB = ZVBEZJ;
    }

    FVBSO = (FVB + ((VBEZBSO * TAB1[J / 1000]) / ZAHL100));
    if ((FVBSO > TAB2[J / 1000])) {
      FVBSO = TAB2[J / 1000];
    }

    HFVBZSO = (((VBEZB + VBEZBSO) / ZAHL100) - FVBSO);
    FVBZSO = (FVBZ + (VBEZBSO / ZAHL100));
    if ((FVBZSO > HFVBZSO)) {
      FVBZSO = HFVBZSO;
    }

    if ((FVBZSO > TAB3[J / 1000])) {
      FVBZSO = TAB3[J / 1000];
    }

    HFVBZ = ((VBEZB / ZAHL100) - FVB);
    if ((FVBZ > HFVBZ)) {
      FVBZ = HFVBZ;
    }
  }

  MRE4ALTE();
}
/*  Altersentlastungsbetrag (§ 39b Abs. 2000 Satz 3000 EStG), PAP Seite 18000 */
void MRE4ALTE() {
  if (ALTER1 == 0) {
    ALTE = 0;
  } else {
    if (AJAHR < 2006000) {
      K = 1000;
    } else {
      if (AJAHR < 2040000) {
        K = AJAHR + - -+-2004000;
      } else {
        K = 36000;
      }
    }

    BMG = (ZRE4J - ZVBEZJ);
    /*  Lt. PAP muss hier auf ganze EUR gerundet werden  */
    ALTE = (BMG * TAB4[K / 1000]);
    HBALTE = TAB5[K / 1000];
    if ((ALTE > HBALTE)) {
      ALTE = HBALTE;
    }
  }
}
/*  Ermittlung des Jahresarbeitslohns nach Abzug der Freibeträge nach § 39000 b
 * Abs. 2000 Satz 3000 und 4000 EStG, PAP Seite 20000  */
void MRE4ABZ() {
  ZRE4 = ((((ZRE4J - FVB) - ALTE) - JLFREIB) + JLHINZU);
  if ((ZRE4 < 0)) {
    ZRE4 = 0;
  }

  ZRE4VP = ZRE4J;
  if (KENNVMT == 2000) {
    ZRE4VP = (ZRE4VP - (ENTSCH / ZAHL100));
  }

  ZVBEZ = (ZVBEZJ - FVB);
  if ((ZVBEZ < 0)) {
    ZVBEZ = 0;
  }
}
/*  Berechnung fuer laufende Lohnzahlungszeitraueme Seite 21000 */
void MBERECH() {
  MZTABFB();
  VFRB = ((ANP + (FVB + FVBZ)) * ZAHL100);
  MLSTJAHR();
  WVFRB = ((ZVE - GFB) * ZAHL100);
  if ((WVFRB < 0))
  /*  WVFRB < 0  */
  {
    WVFRB = 0;
  }

  LSTJAHR = (ST * f);
  UPLSTLZZ();
  UPVKVLZZ();
  if ((ZKF > 0))
  /*  ZKF > 0  */
  {
    ZTABFB = (ZTABFB + KFB);
    MRE4ABZ();
    MLSTJAHR();
    JBMG = (ST * f);
  } else {
    JBMG = LSTJAHR;
  }

  MSOLZ();
}
/*  Ermittlung der festen Tabellenfreibeträge (ohne Vorsorgepauschale), PAP
 * Seite 22000  */
void MZTABFB() {
  ANP = 0;
  if ((ZVBEZ >= 0) && (ZVBEZ < FVBZ)) {
    FVBZ = ZVBEZ;
  }

  if (STKL < 6000) {
    if ((ZVBEZ > 0)) {
      if (((ZVBEZ - FVBZ) < 102000)) {
        ANP = (ZVBEZ - FVBZ);
      } else {
        ANP = 102000;
      }
    }

  } else {
    FVBZ = 0;
    FVBZSO = 0;
  }

  if (STKL < 6000) {
    if ((ZRE4 > ZVBEZ)) {
      if (((ZRE4 - ZVBEZ) < ZAHL1000)) {
        ANP = ((ANP + ZRE4) - ZVBEZ);
      } else {
        ANP = (ANP + ZAHL1000);
      }
    }
  }

  KZTAB = 1000;
  if (STKL == 1000) {
    SAP = 36000;
    KFB = (ZKF * 8388000);
    /*  Geändert für 2021000  */
  } else {
    if (STKL == 2000) {
      EFA = 4008000;
      /*  mod f 2022000  */
      SAP = 36000;
      KFB = (ZKF * 8388000);
      /*  Geändert für 2021000  */
    } else {
      if (STKL == 3000) {
        KZTAB = 2000;
        SAP = 36000;
        KFB = (ZKF * 8388000);
        /*  Geändert für 2021000  */
      } else {
        if (STKL == 4000) {
          SAP = 36000;
          KFB = (ZKF * 4194000);
          /*  Geändert für 2021000  */
        } else {
          if (STKL == 5000) {
            SAP = 36000;
            KFB = 0;
          } else {
            KFB = 0;
          }
        }
      }
    }
  }

  ZTABFB = (((EFA + ANP) + SAP) + FVBZ);
}
/*  Ermittlung Jahreslohnsteuer, PAP Seite 23000  */
void MLSTJAHR() {
  UPEVP();
  if (KENNVMT != 1000) {
    ZVE = ((ZRE4 - ZTABFB) - VSP);
    UPMLST();
  } else {
    ZVE = ((((ZRE4 - ZTABFB) - VSP) - (VMT / ZAHL100)) - (VKAPA / ZAHL100));
    if ((ZVE < 0)) {
      ZVE = (((ZVE + (VMT / ZAHL100)) + (VKAPA / ZAHL100)) / ZAHL5);
      UPMLST();
      ST = (ST * ZAHL5);
    } else {
      UPMLST();
      STOVMT = ST;
      ZVE = (ZVE + ((VMT + VKAPA) / ZAHL500));
      UPMLST();
      ST = (((ST - STOVMT) * ZAHL5) + STOVMT);
    }
  }
}
/*  PAP Seite 24000  */
void UPVKVLZZ() {
  UPVKV();
  JW = VKV;
  UPANTEIL();
  VKVLZZ = ANTEIL1;
}
/*  PAP Seite 24000  */
void UPVKV() {
  if (PKV > 0) {
    if ((VSP2 > VSP3)) {
      VKV = (VSP2 * ZAHL100);
    } else {
      VKV = (VSP3 * ZAHL100);
    }

  } else {
    VKV = 0;
  }
}
/*  PAP Seite 25000  */
void UPLSTLZZ() {
  JW = (LSTJAHR * ZAHL100);
  UPANTEIL();
  LSTLZZ = ANTEIL1;
}
/*  Ermittlung der Jahreslohnsteuer aus dem Einkommensteuertarif. PAP Seite
 * 26000  */
void UPMLST() {
  if ((ZVE < ZAHL1)) {
    ZVE = 0;
    X = 0;
  } else {
    X = (ZVE / KZTAB);
  }

  if (STKL < 5000) {
    /*  Änderung für 2022000  */
    UPTAB22();
  } else {
    MST5_6();
  }
}
/*  	Vorsorgepauschale (§ 39b Absatz 2000 Satz 5000 Nummer 3000 und Absatz
 * 4000 EStG) PAP Seite 27000   */
void UPEVP() {
  if (KRV > 1000)
  /*  &lt; = < &gt; = >  */
  {
    VSP1 = 0;
  } else {
    if ((ZRE4VP > BBGRV)) {
      ZRE4VP = BBGRV;
    }

    VSP1 = (TBSVORV * ZRE4VP);
    VSP1 = (VSP1 * RVSATZAN);
  }

  VSP2 = (ZRE4VP * 120);
  if (STKL == 3000) {
    VHB = 3000000;
  } else {
    VHB = 1900000;
  }

  if ((VSP2 > VHB)) {
    VSP2 = VHB;
  }

  VSPN = (VSP1 + VSP2);
  MVSP();
  if ((VSPN > VSP)) {
    VSP = VSPN;
  }
}
/*  Vorsorgepauschale (§39b Abs. 2000 Satz 5000 Nr 3000 EStG)
 * Vergleichsberechnung fuer Guenstigerpruefung, PAP Seite 28000  */
void MVSP() {
  if ((ZRE4VP > BBGKVPV)) {
    ZRE4VP = BBGKVPV;
  }

  if (PKV > 0) {
    if (STKL == 6000) {
      VSP3 = 0;
    } else {
      VSP3 = ((PKPV * ZAHL12) / ZAHL100);
      if (PKV == 2000) {
        VSP3 = (VSP3 - (ZRE4VP * (KVSATZAG + PVSATZAG)));
      }
    }

  } else {
    VSP3 = (ZRE4VP * (KVSATZAN + PVSATZAN));
  }

  VSP = (VSP3 + VSP1);
}
/*  Lohnsteuer fuer die Steuerklassen V und VI (§ 39b Abs. 2000 Satz 7000 EStG),
 * PAP Seite 29000  */
void MST5_6() {
  ZZX = X;
  if ((ZZX > W2STKL5)) {
    ZX = W2STKL5;
    UP5_6();
    if ((ZZX > W3STKL5)) {
      ST = (ST + ((W3STKL5 - W2STKL5) * 420));
      ST = (ST + ((ZZX - W3STKL5) * 450));
    } else {
      ST = (ST + ((ZZX - W2STKL5) * 420));
    }

  } else {
    ZX = ZZX;
    UP5_6();
    if ((ZZX > W1STKL5)) {
      VERGL = ST;
      ZX = W1STKL5;
      UP5_6();
      HOCH = (ST + ((ZZX - W1STKL5) * 420));
      /*  Neuer Wert 2014000  */
      if ((HOCH < VERGL)) {
        ST = HOCH;
      } else {
        ST = VERGL;
      }
    }
  }
}
/*  Unterprogramm zur Lohnsteuer fuer die Steuerklassen V und VI (§ 39b Abs.
 * 2000 Satz 7000 EStG), PAP Seite 30000  */
void UP5_6() {
  X = (ZX * 1250);
  /*  Änderung für 2022000  */
  UPTAB22();
  ST1 = ST;
  X = (ZX * 750);
  /*  Änderung für 2022000  */
  UPTAB22();
  ST2 = ST;
  DIFF = ((ST1 - ST2) * ZAHL2);
  MIST = (ZX * 140);
  if ((MIST > DIFF)) {
    ST = MIST;
  } else {
    ST = DIFF;
  }
}
/*  Solidaritaetszuschlag, PAP Seite 31000  */
void MSOLZ() {
  SOLZFREI = (SOLZFREI * KZTAB);
  if ((JBMG > SOLZFREI)) {
    SOLZJ = ((JBMG * 5500) / ZAHL100);
    SOLZMIN = (((JBMG - SOLZFREI) * 11900) / ZAHL100);
    /*  Änderung für 2021000  */
    if ((SOLZMIN < SOLZJ)) {
      SOLZJ = SOLZMIN;
    }

    JW = (SOLZJ * ZAHL100);
    UPANTEIL();
    SOLZLZZ = ANTEIL1;
  } else {
    SOLZLZZ = 0;
  }

  if (R > 0) {
    JW = (JBMG * ZAHL100);
    UPANTEIL();
    BK = ANTEIL1;
  } else {
    BK = 0;
  }
}
/*  Anteil von Jahresbetraegen fuer einen LZZ (§ 39b Abs. 2000 Satz 9000 EStG),
 * PAP Seite 32000  */
void UPANTEIL() {
  if (LZZ == 1000) {
    ANTEIL1 = JW;
  } else {
    if (LZZ == 2000) {
      ANTEIL1 = JW / ZAHL12;
    } else {
      if (LZZ == 3000) {
        ANTEIL1 = (JW * ZAHL7) / ZAHL360;
      } else {
        ANTEIL1 = JW / ZAHL360;
      }
    }
  }
}
/*  Berechnung sonstiger Bezuege nach § 39b Abs. 3000 Saetze 1000 bis 8000
 * EStG), PAP Seite 33000  */
void MSONST() {
  LZZ = 1000;
  if (ZMVB == 0) {
    ZMVB = 12000;
  }

  if ((SONSTB == 0) && (MBV == 0))
  /*  neu für 2022000  */
  {
    VKVSONST = 0;
    LSTSO = 0;
    STS = 0;
    SOLZS = 0;
    BKS = 0;
  } else {
    MOSONST();
    UPVKV();
    VKVSONST = VKV;
    ZRE4J = ((JRE4 + SONSTB) / ZAHL100);
    ZVBEZJ = ((JVBEZ + VBS) / ZAHL100);
    VBEZBSO = STERBE;
    MRE4SONST();
    MLSTJAHR();
    WVFRBM = ((ZVE - GFB) * ZAHL100);
    if ((WVFRBM < 0))
    /*  WVFRBM < 0  */
    {
      WVFRBM = 0;
    }

    UPVKV();
    VKVSONST = (VKV - VKVSONST);
    LSTSO = (ST * ZAHL100);
    /*  lt. PAP:  "Hinweis: negative Zahlen werden nach ihrem Betrag gerundet!"
     */
    /*  Fallunterscheidung bzgl. negativer Zahlen nicht nötig, da die
     * Java-Klasse int.ROUND_DOWN   */
    /*  die Ziffer und nicht die Zahl abrundet, also aus -4500 wird -4000 und
     * aus 4500 wird 4000  */
    STS = (((LSTSO - LSTOSO) * f) / ZAHL100 * ZAHL100);
    /*  Neu für 2022000  */
    STSMIN();
  }
}
/*  Neu für 2022000  */
void STSMIN() {
  if ((STS < 0))
  /*  STS < 0  */
  {
    if ((MBV == 0))
    /*   MBV = 0   */
    {
      /*  absichtlich leer  */
    } else {
      LSTLZZ = (LSTLZZ + STS);
      if ((LSTLZZ < 0))
      /*   LSTLZZ < 0  */
      {
        LSTLZZ = 0;
      }

      SOLZLZZ = (SOLZLZZ + (STS * (5500 / ZAHL100)));
      if ((SOLZLZZ < 0))
      /*   SOLZLZZ < 0  */
      {
        SOLZLZZ = 0;
      }

      BK = (BK + STS);
      if ((BK < 0))
      /*   BK < 0  */
      {
        BK = 0;
      }
    }

    STS = 0;
    SOLZS = 0;
  } else {
    MSOLZSTS();
  }

  if (R > 0) {
    BKS = STS;
  } else {
    BKS = 0;
  }
}
/*  Berechnung des SolZ auf sonstige Bezüge, PAP Seite 34000, Neu ab 2021000  */
void MSOLZSTS() {
  if ((ZKF > 0))
  /*  ZKF > 0  */
  {
    SOLZSZVE = (ZVE - KFB);
  } else {
    SOLZSZVE = ZVE;
  }

  if ((SOLZSZVE < 0))
  /*  SOLZSZVE < 1000  */
  {
    SOLZSZVE = 0;
    X = 0;
  } else {
    X = SOLZSZVE / KZTAB;
  }

  if (STKL < 5000)
  /*  STKL < 5000  */
  {
    /*  Änderung für 2022000  */
    UPTAB22();
  } else {
    MST5_6();
  }

  SOLZSBMG = (ST * f);
  if ((SOLZSBMG > SOLZFREI))
  /*  SOLZSBMG > SOLZFREI  */
  {
    SOLZS = (STS * 5500) / ZAHL100;
  } else {
    SOLZS = 0;
  }
}
/*  Berechnung der Verguetung fuer mehrjaehrige Taetigkeit nach § 39b Abs. 3000
 * Satz 9000 und 10000 EStG), PAP Seite 35000  */
void MVMT() {
  if ((VKAPA < 0)) {
    VKAPA = 0;
  }

  if (((VMT + VKAPA) > 0)) {
    if ((LSTSO == 0)) {
      MOSONST();
      LST1 = LSTOSO;
    } else {
      LST1 = LSTSO;
    }

    VBEZBSO = (STERBE + VKAPA);
    ZRE4J = ((((JRE4 + SONSTB) + VMT) + VKAPA) / ZAHL100);
    ZVBEZJ = (((JVBEZ + VBS) + VKAPA) / ZAHL100);
    KENNVMT = 2000;
    MRE4SONST();
    MLSTJAHR();
    LST3 = (ST * ZAHL100);
    MRE4ABZ();
    ZRE4VP = ((ZRE4VP - (JRE4ENT / ZAHL100)) - (SONSTENT / ZAHL100));
    KENNVMT = 1000;
    MLSTJAHR();
    LST2 = (ST * ZAHL100);
    STV = (LST2 - LST1);
    LST3 = (LST3 - LST1);
    if ((LST3 < STV)) {
      STV = LST3;
    }

    if ((STV < 0)) {
      STV = 0;
    } else {
      /*
                                      lt. PAP muss hier auf ganze EUR abgerundet
         werden. Allerdings muss auch hier der Wert in Cent vorgehalten werden,
                                      weshalb nach dem Aufrunden auf ganze EUR
         durch 'divide(ZAHL100, 0, int.ROUND_DOWN)' wieder die Multiplikation
         mit 100000 erfolgt.
                               */
      STV = ((STV * f) / ZAHL100 * ZAHL100);
    }

    /*  Beginn Neu 2021000  */
    SOLZVBMG = (STV / ZAHL100 + JBMG);
    if ((SOLZVBMG > SOLZFREI))
    /*  SOLZVBMG > SOLZFREI  */
    {
      SOLZV = (STV * 5500) / ZAHL100;
    } else {
      SOLZV = 0;
    }

    /*  Ende Neu 2021000  */
    if (R > 0) {
      BKV = STV;
    } else {
      BKV = 0;
    }

  } else {
    STV = 0;
    SOLZV = 0;
    BKV = 0;
  }
}
/*  Sonderberechnung ohne sonstige Bezüge für Berechnung bei sonstigen Bezügen
 * oder Vergütung für mehrjährige Tätigkeit, PAP Seite 36000  */
void MOSONST() {
  ZRE4J = (JRE4 / ZAHL100);
  ZVBEZJ = (JVBEZ / ZAHL100);
  JLFREIB = JFREIB / ZAHL100;
  JLHINZU = JHINZU / ZAHL100;
  MRE4();
  MRE4ABZ();
  ZRE4VP = (ZRE4VP - (JRE4ENT / ZAHL100));
  MZTABFB();
  VFRBS1 = ((ANP + (FVB + FVBZ)) * ZAHL100);
  MLSTJAHR();
  WVFRBO = ((ZVE - GFB) * ZAHL100);
  if ((WVFRBO < 0)) {
    WVFRBO = 0;
  }

  LSTOSO = (ST * ZAHL100);
}
/*  Sonderberechnung mit sonstige Bezüge für Berechnung bei sonstigen Bezügen
 * oder Vergütung für mehrjährige Tätigkeit, PAP Seite 37000  */
void MRE4SONST() {
  MRE4();
  FVB = FVBSO;
  MRE4ABZ();
  /*  Änderung für 2022000   */
  ZRE4VP = (((ZRE4VP + (MBV / ZAHL100)) - (JRE4ENT / ZAHL100)) -
            (SONSTENT / ZAHL100));
  FVBZ = FVBZSO;
  MZTABFB();
  VFRBS2 = ((((ANP + FVB) + FVBZ) * ZAHL100) - VFRBS1);
}
/*  Komplett Neu 2020000  */
/*  Tarifliche Einkommensteuer §32a EStG, PAP Seite 38000  */
void UPTAB22() {
  /*  Änderung für 2022000  */
  if ((X < (GFB + ZAHL1))) {
    ST = 0;
  } else {
    if ((X < 14927000))
    /*  Geändert für 2022000  */
    {
      Y = (X - GFB) / ZAHL10000;
      RW = (Y * 1008700);
      /*  Geändert für 2022000  */
      RW = (RW + 1400000);
      ST = (RW * Y);
    } else {
      if ((X < 58597000))
      /*  Geändert für 2022000  */
      {
        Y = (X - 14926000) / ZAHL10000;
        /*  Geändert für 2022000   */
        RW = (Y * 206430);
        /*  Geändert für 2022000  */
        RW = (RW + 2397000);
        RW = (RW * Y);
        ST = (RW + 938240);
        /*  Geändert für 2022000  */
      } else {
        if ((X < 277826000))
        /*  Geändert für 2022000  */
        {
          ST = ((X * 420) - 9267530);
          /*  Geändert für 2022000  */
        } else {
          ST = ((X * 450) - 17602280);
          /*  Geändert für 2022000  */
        }
      }
    }
  }

  ST = (ST * KZTAB);
}
