##########################################################################################
#  This script is intended to make it easy to adjust the parameters of the MWU system    #
#    by propagating the correct values through the (verified) oracle, the OCaml shim     #
#    and the python interface.                                                           #
#                                                                                        #
#  Use: Adjust the values of STRATEGIES, NUM_ROUNDS and ETA below, then call             #
#       `python3 config.py`.                                                             #
#                                                                                        #
#  Restrictions:                                                                         #
#    - ETA : float, STRATEGIES : int, NUM_ROUNDS : int                                   #
#    - 0 < [STRATEGIES/NUM_ROUNDS/ETA]                                                   #
#    - ETA <= 1/2                                                                        #
#    - Very large values for STRATEGIES and NUM_ROUNDS may cause memory issues in Coq    #
#      due to the fact that Coq reperesents them in unary.                               #
#                                                                                        #
##########################################################################################


import math
import re
import fileinput
import sys


############################
# Parameters to propagate
############################
STRATEGIES = 17
NUM_ROUNDS = 24
ETA = .375

############################
# String patterns for Coq
############################
strat_pattern_coq = re.compile('  Definition num_strategies :=*')
strat_string_coq = "  Definition num_strategies := " + str(STRATEGIES) + ".\n"

eta_pattern_coq = re.compile('  Definition eta :=*')
eta_string_coq = ("  Definition eta := dyadic.Dmake (" +
                    str(float.as_integer_ratio(ETA)[0]) + "%Z) (" +
                    str(int(math.log(float.as_integer_ratio(ETA)[1], 2))) + "%positive).\n")

round_pattern_coq = re.compile('  Definition num_rounds := N.of_nat*')
round_string_coq = ("  Definition num_rounds := N.of_nat " + str(NUM_ROUNDS) + ".\n")

#############################
# String patterns for OCaml
#############################
strat_pattern_ocaml = re.compile('let num_strats =*')
strat_string_ocaml = "let num_strats = " + str(STRATEGIES) + "\n"

round_pattern_ocaml = re.compile('let num_rounds =*')
round_string_ocaml = "let num_rounds = " + str(NUM_ROUNDS) + "\n"


#############################
# String patterns for Python
#############################
strat_pattern_python = re.compile('num_strats =*')
strat_string_python = "num_strats = " + str(STRATEGIES) + "\n"

round_pattern_python = re.compile('num_rounds =*')
round_string_python = "num_rounds = " + str(NUM_ROUNDS) + "\n"


for line in fileinput.input(["oracleExtract.v", "./runtime/OTP.ml", "./runtime/envProc.py"], inplace=1):
    if strat_pattern_coq.match(line) :
        line = strat_string_coq
    if eta_pattern_coq.match(line) :
        line = eta_string_coq
    if round_pattern_coq.match(line) :
        line = round_string_coq
    if strat_pattern_ocaml.match(line) :
        line = strat_string_ocaml
    if round_pattern_ocaml.match(line) :
        line = round_string_ocaml
    if strat_pattern_python.match(line) :
        line = strat_string_python
    if round_pattern_python.match(line) :
        line = round_string_python
    sys.stdout.write(line)
