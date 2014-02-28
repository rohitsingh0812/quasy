#!/bin/bash

export CLASSPATH=.:bin

if [ -d results ]; then
	echo "Output directory results exists."
else
	mkdir results
fi

cd ../..

#back to the main folder
scala quasy.Main prodAPPEND ./Examples/LexMPG/w0.gff ./Examples/LexMPG/w1.gff ./Examples/LexMPG/w01.gff

scala quasy.Main solveLMPGr ./Examples/LexMPG/w01.gff ./Examples/LexMPG/safe2.gff Examples/LexMPG/results/
