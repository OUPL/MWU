# MWU/runtime

This is directory to which OCaml files are extracted from `MWU/oracleExtract.v`. It also contains some small pieces of code for connecting the extracted program to a larger system. Instructions for building and execution follow.

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
cd /runtime
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