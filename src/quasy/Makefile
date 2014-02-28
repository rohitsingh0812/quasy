BIN_DIR=../../bin
BIN_DIR_P=${BIN_DIR}/quasy

FSC=fsc -classpath ${BIN_DIR} -d ${BIN_DIR} -deprecation

all: ${BIN_DIR} ${BIN_DIR_P}/GaussianElimination.class ${BIN_DIR_P}/Main.class

${BIN_DIR}:
	mkdir -p ${BIN_DIR}

${BIN_DIR_P}/GaussianElimination.class: ${BIN_DIR} GaussianElimination.java
	javac GaussianElimination.java -d ${BIN_DIR}

${BIN_DIR_P}/Main.class: ${BIN_DIR} Main.scala ${BIN_DIR_P}/Game.class ${BIN_DIR_P}/MDP.class
	${FSC} Main.scala


${BIN_DIR_P}/MDP.class: ${BIN_DIR} MDP.scala ${BIN_DIR_P}/Game.class ${BIN_DIR_P}/GaussianElimination.class
	${FSC} MDP.scala

${BIN_DIR_P}/Game.class: ${BIN_DIR} Game.scala ${BIN_DIR_P}/State.class ${BIN_DIR_P}/disjunct.class
	${FSC} Game.scala

${BIN_DIR_P}/disjunct.class: ${BIN_DIR} disjunct.scala
	${FSC} disjunct.scala

${BIN_DIR_P}/State.class: ${BIN_DIR} State.scala
	${FSC} Edge.scala Action.scala State.scala

${BIN_DIR_P}/Edge.class: ${BIN_DIR} Edge.scala ${BIN_DIR_P}/State.class
	${FSC} Edge.scala

${BIN_DIR_P}/Action.class: ${BIN_DIR} Action.scala ${BIN_DIR_P}/State.class ${BIN_DIR_P}/Edge.class
	${FSC} Action.scala

clean:
	rm -rf ${BIN_DIR_P}
