QUASY=../../
BIN_DIR=${QUASY}/bin

all: ${BIN_DIR} ${BIN_DIR}/test/TestResponse.class ${BIN_DIR}/test/OptionParser.class ${BIN_DIR}/test/distr

${BIN_DIR}/test/TestResponse.class: ${BIN_DIR} TestResponse.scala
	fsc -deprecation -d ${BIN_DIR} TestResponse.scala Options.scala

${BIN_DIR}/test/OptionParser.class: ${BIN_DIR} Options.scala
	fsc -deprecation -d ${BIN_DIR} Options.scala

${BIN_DIR}/test/distr: ${BIN_DIR} distr.cpp
	g++ -o ${BIN_DIR}/test/distr distr.cpp

${BIN_DIR}:
	mkdir -p ${BIN_DIR}
clean:
	rm -rf ${BIN_DIR}/test

