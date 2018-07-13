# MWU
Verified Multiplicative Weights Update

## Prerequisites

* Coq 8.8.1
* Ssreflect 1.7.0
* OCaml (>= 4.04.0)
* Ohio University Verification Toolsuite (OUVerT)

### [OPAM](https://opam.ocaml.org/) is the best way to install prereqs:

Using aptitude in debian/Ubuntu linux:

#### Install and set up OPAM:
```
apt-get install opam
opam init
opam switch 4.04.0
eval `opam config env`
```

#### Once OPAM is set-up with OCaml (>= 4.04.0):
```
opam install coq
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
apt-get install libgmp-dev
opam install coq-mathcomp-algebra
```
#### Install Ohio University Verification Toolsuite (OUVerT)
Clone the OUVerT library from https://github.com/OUPL/OUVerT

```
make
make install
```

The latter command installs the OUVerT files in your local .opam directory.

## Build Instructions

```
make
```