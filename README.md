# data-minization 


* `exec.py` is for execution the pipeline, which consists of three steps:
    1. A program execution with concrete input
    2. Extraction of Facts
    3. Facts minimization by CBMC and z3

  `exec.py` takes `--mode {run,cbmc,facts}` to execute a particular steps. The program is given as the second positional
  argument. Additional information are given as a YAML files in the first positional place.

### Conversion from XML to C 

```shell
$ ./convertXml2C.py [int]
```

Converts the given `2022.xml` into plain. Either into a version using `double` data type or to version 
only using `int` (if `int` is given as an paramter).

### Additional information

### Structure of the program

* All input and output variables are accessible in the main program.  
  For example `lohnsteuer.c` uses global variables.

* The program contains markers to inject code.
    - `//%HEADER%` to add additional header files
      (ie., `stdio.h` for execution)
    - `//%INPUT%`  marks the place before the execution of the program (at the beginning of `main`)
    - `//%OUTPUT%` marks the end of the `main` function.

* Headers can be disabled by `-DNOHEADER=1` required by the `pycparser`

* Symbolic Execution is limited, and does not support function calls with arguments.

* Program has no output on `stdout`

* Loop-free (for facts extraction)

### Pipeline Steps

#### Running with concrete input

```
$ ./exec.py --mode run <input.yml> <program.c>
``` 

Executes the given C program by injecting the input values given in the YAML file into the program. The temp file is
then compiled and executed. Additional to the input values, the program is modified to print a YAML fragment with the
value of the output variables. The assignment of the output variable is weaved into the given YAML file.

#### Extraction of facts (under construction)

```
$ ./exec.py --mode facts <input.yml> <program.c>
``` 

The given C program is parsed and symbolical executed. The result is in SSA-form. Facts are then written to the given
YAML file in the `FACTS:` section.

####  

```
$ ./exec.py --mode cbmc <input.yml> <program.c>
``` 

The given C program is prepared for CBMC:

* First, the conditional assumption is inserted for each fact in the YAML file.
  ```c
  _CPROVER_Bool FACT_X; 
  _CPROVER_input("FACT_X", FACT_X);
  if(FACT_X) __CPROVER_assume( ... )
  ``` 
  The assumption takes place at the input marker `//%INPUT%`.

* The output variable are asserted to have the same value as given in the YAML file, which can filled in automatically
  by `--mode run`.

The augmented program is translated into SMT2 by using `cbmc`. The SMT2 is enriched by some `:named` tags. This helps us
later to identified the facts in the unsat-core. Also some commands are dropped to control SMT solver (TODO).

The SMT file is solved by z3. The resulting unsat-core shows conflicting facts.