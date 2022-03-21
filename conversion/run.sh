#!/bin/sh -x

./extractMetadata.py >meta.yml
./convertXml2C.py int >lohnsteuer_int.c
./convertXml2C.py float >lohnsteuer_float.c
