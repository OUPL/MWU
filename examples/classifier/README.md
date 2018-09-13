# MWU/runtime

This is directory to which OCaml files are extracted from `MWU/oracleExtract.v`.
It also contains code for connecting the extracted program to a larger system
that employs the verified MWU to to solve a randomly generated linear
classification problem.

# Detailed Description

The Python program in envProc.py randomly generates a hyperplane of given
dimension as well as a set of examples classifiable by the random hyperplane.

This environment then proceeds receiving weight vectors from the client and in
turn generates cost vectors and sends them back. In the case of this
classification algorithm, the cost vectors returned are actually defined as
"gain vectors" and are generated by finding a misclassified example and
generating a gain vector according to the following formula:

(-1/rho) * violating_example * label

This exchange of new weight vectors and gains proceeds until the set of
examples is fully classified. The system then proceeds to classify the same
example set via a Python implementation for comparison purposes.

## Prerequisites
* OCaml (>= 4.04.0)
* Ocamlfind (>= 1.8.0)
* Zrith library

### As before, [OPAM](https://opam.ocaml.org/) is the best way to install prereqs:

#### Once OPAM is set-up with OCaml (>= 4.04.0):

```
opam install ocamlfind
opam install zarith
```

## Build Instructions

### Generating verified `extractedMWU.ml` (Optional)

```
cd ../
make
cd /examples/classifier
```
### Buidling from source

```
make
./init.sh
```

### Executing the system

Simply execute the three processes:

```
clientProc
```
```
envProc
```
```
env_client_interface
```

## Modifying the system

Check MWU_networking.pdf for a more detailed description of
how networking and communication between the processes can
be adapted.