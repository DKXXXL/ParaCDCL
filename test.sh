make
pushd tests
ocamlopt CDCLTests.mli CDCLTests.ml CDCLPrintTests.ml -o testCDCL &> /dev/null
./testCDCL
popd