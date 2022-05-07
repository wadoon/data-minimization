#!/bin/bash -x

shopt -x
M=examples/tax_rate.input_1.yml
P=examples/tax_rate.paper.c

./exec --mode run $M $P
./exec --mode check $M $P
./exec --mode facts -o new.yml $M $P