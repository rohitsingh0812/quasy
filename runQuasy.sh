#!/bin/bash
export CLASSPATH=.:./bin

if [ -f bin/quasy/Main.class ]; then

   if [ "$1" == "" ]; then
	echo "Usage: $0 quasy_options"
	scala quasy.Main
	exit
   fi
   scala quasy.Main $*
else
   echo "Compile quasy with 'make'"
fi
