#!/bin/bash

if [ "$1" == "" ]; then
	echo "Usage: $0 num_of_client output_filename"
	exit
fi
scala -classpath bin test.TestResponse $*

# or
# #!/bin/sh
# exec scala $0 $@
# !#
# // Say hello to the first argument
# println("Hello, " + args(0) + "!")
