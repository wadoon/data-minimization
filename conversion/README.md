# Lohnsteuer4C

Lohnsteuer is the german tax on wages. The calculated of this tax is defined in flow diagrams (Programmablaufpläne, PAP,
DIN 66001). The PAPs can be found at the pages of the Finance Ministry:

* [Programmablaufplan für die maschinelle Berechnung der vom Arbeitslohn einzubehaltenden Lohnsteuer, des Solidaritätszuschlags und der Maßstabsteuer für die Kirchenlohnsteuer für 2022](https://www.bundesfinanzministerium.de/Content/DE/Downloads/Steuern/Steuerarten/Lohnsteuer/Programmablaufplan/2021-11-05-PAP-2022-anlage-1.pdf?__blob=publicationFile&v=3)

* [Programmablaufplan für die Erstellung von Lohnsteuertabellen für 2022 zur manuellen Berechnung der Lohnsteuer (einschließlich der Berechnung des Solidaritätszuschlags und der Bemessungsgrundlage für die Kirchenlohnsteuer)](https://www.bundesfinanzministerium.de/Content/DE/Downloads/Steuern/Steuerarten/Lohnsteuer/Programmablaufplan/2021-11-05-PAP-2022-anlage-2.pdf?__blob=publicationFile&v=3)

These PAP are also provided in "Pseudocode" (XML format). This XML is mainly tagged Java assignments and expressions.
The XML file is [checked in](conversion/2022.xml), but can also be
found  [here](https://www.bmf-steuerrechner.de/interface/pseudocodes.xhtml).

This repository contains the extraction tool `convertXml2C.py`, which translate the XML/Java into plain C.

## How to use

`convertXml2C.py` converts the given calculations in `2022.xml` into valid plain C code using double values or int values. `extractMetadata.py` creates a YAML meta-data file required by the data-minimization pipeline.
