#!/bin/bash

export CLASSPATH=.:bin

if [ -d results ]; then
	echo "Output directory results exists."
else
	mkdir results
fi

cd ../..

#back to the main folder
scala quasy.Main prodADD ./Examples/MDPPar/w0.gff ./Examples/MDPPar/w1.gff ./Examples/MDPPar/w01.gff

#we have 2 parity automaton and one safety
#construct final parity using goal
time scala quasy.Main solveMDPPext ./Examples/MDPPar/w01.gff ./Examples/MDPPar/st01_excl_tool_BA.gff ./Examples/MDPPar/distro2.txt Examples/MDPPar/results/
#2.71 , 8,26,8,4
time scala quasy.Main solveMDPPext ./Examples/MDPPar/more_clients/w012.gff ./Examples/MDPPar/more_clients/fin_det_parity3.gff ./Examples/MDPPar/more_clients/distro3.txt Examples/MDPPar/results3/
#16.30 , 22,198,20,10

