SHELL := /bin/bash

all:
	pushd src/quasy; make all; popd  ## quasy package
	pushd mdpsolver; make; popd      ## c++ linear program solver
	pushd src/test; make all; popd   ## test package

clean: 
	rm -rf ./bin distr tempf.gff
	pushd mdpsolver; make clean; popd

run:
	scala -classpath bin quasy.Main


