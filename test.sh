!sh
make
pushd tests
ocamlopt CDCLTests.mli CDCLTests.ml CDCLPrintTests.ml -o testCDCL &> \null
./testCDCL
popd