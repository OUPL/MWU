all: big.o extractedMWU.cmi extractedMWU.o env_client_interface clientProc

big.o : big.ml
	ocamlfind ocamlc -package zarith -c big.ml

extractedMWU.cmi : extractedMWU.mli
	ocamlfind ocamlc extractedMWU.mli

extractedMWU.o : extractedMWU.ml extractedMWU.mli
	ocamlfind ocamlopt -package zarith -c big.ml extractedMWU.ml

clientProc : extractedMWU.o extractedMWU.cmi
	ocamlfind ocamlopt -package zarith -o clientProc zarith.cmxa big.cmx extractedMWU.ml

env_client_interface : big.o OTP.ml
	ocamlfind ocamlopt -package zarith,str -o env_client_interface zarith.cmxa str.cmxa big.ml OTP.ml

clean :
	rm *.o *.cmx *.cmi *.cmo *.pyc env_client_interface clientProc clientInput clientOutput envInput envOutput
