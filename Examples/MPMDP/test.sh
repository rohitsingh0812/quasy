#!/bin/bash

export CLASSPATH=.:bin

if [ -d results ]; then
	echo "Output directory results exists."
else
	mkdir results
fi

cd ../..

#back to the main folder
scala quasy.Main prodADD ./Examples/MPMDP/w0.gff ./Examples/MPMDP/w1.gff ./Examples/MPMDP/w01.gff

scala quasy.Main solveMDP ./Examples/MPMDP/w01.gff ./Examples/MPMDP/finalparity.gff ./Examples/MPMDP/distro2.txt Examples/MPMDP/results/
