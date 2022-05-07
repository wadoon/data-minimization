time python ../exec.py execute account_charges.2.yml account_charges.c
time python ../exec.py fact-consistency account_charges.2.yml account_charges.c
time python ../exec.py facts-preciseness account_charges.2.yml account_charges.c
time python ../exec.py minimize-facts-core account_charges.2.yml account_charges.c


time python ../exec.py fact-consistency account_charges.2.yml account_charges.c -f USER_FACTS_B
time python ../exec.py symbex account_charges.2.yml account_charges.c -f USER_FACTS_B
time python ../exec.py facts-preciseness account_charges.2.yml account_charges.c -f USER_FACTS_B
