#!/bin/bash
# script to run MDP test for NUM clients

export CLASSPATH=.:bin

OUTDIR="test"
SPECDIR="test/spec"
CDIR="c"
QSPEC="react_quickly_c"
SSPEC="mutual_exclusion_c"
DISTR="distribution_c"
NUM=2

if [ -n "$1" ]; then
    NUM=$1
fi

echo "Creating optimal system for $NUM clients"

##################################
# Build name of final specification
for (( i=0; i<$NUM; i++ )); do
    final=${final}$i
done
	
##################################
# Check output directories
if [ ! -d $OUTDIR ]; then
    echo "Creating output directory $OUTDIR"
    mkdir $OUTDIR
fi

if [ ! -d $OUTDIR/$CDIR${final} ]; then
    echo "Creating output directory $OUTDIR/$CDIR${final}"
    mkdir $OUTDIR/$CDIR${final}
fi

##################################
# Directory for specification files
if [ ! -d ${SPECDIR} ]; then
    echo "Create directory for automaton files"
    mkdir ${SPECDIR}
fi

##################################
# Check quantitative specification
file=${SPECDIR}/${QSPEC}${final}.gff
if [ ! -f $file ]; then

    if [ ! -f ${SPECDIR}/${QSPEC}0.gff ]; then
    echo "Creating initial quantitative specification: ${SPECDIR}/${QSPEC}0.gff"
    cat > ${SPECDIR}/${QSPEC}0.gff <<EOF
<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<!--GFF created with GOAL 2010-02-01.-->
<structure label-on="transition" type="fa">
    <!--The list of alphabets.-->
    <alphabet type="propositional">
        <prop>g0</prop>
        <prop>r0</prop>
        <prop>w0</prop>
        <prop>w1</prop>
    </alphabet>
    <!--The list of states.-->
    <stateSet>
        <state sid="0">
            <x>188.0</x>
            <y>157.0</y>
        </state>
        <state sid="1">
            <x>328.0</x>
            <y>156.0</y>
        </state>
    </stateSet>
    <!--The list of transitions.-->
    <transitionSet>
        <transition tid="1">
            <from>0</from>
            <to>0</to>
            <read>g0 w1</read>
        </transition>
        <transition tid="3">
            <from>1</from>
            <to>1</to>
            <read>~g0 w0</read>
        </transition>
        <transition tid="2">
            <from>0</from>
            <to>1</to>
            <read>~g0 r0 w0</read>
        </transition>
        <transition tid="0">
            <from>0</from>
            <to>0</to>
            <read>~g0 ~r0 w1</read>
        </transition>
        <transition tid="4">
            <from>1</from>
            <to>0</to>
            <read>g0 w1</read>
        </transition>
    </transitionSet>
    <!--The list of initial states.-->
    <initialStateSet>
        <stateID>0</stateID>
    </initialStateSet>
    <!--The ACC record.-->
    <acc type="buchi">
    <stateID>0</stateID>
    <stateID>1</stateID>
    </acc>
    <!--The automaton description record.-->
    <description/>
</structure>
EOF
    fi


    echo "Creating quantitative specification for ${NUM} clients: $file"
    for (( c=0; c<$NUM; c++ )); do
	file="${SPECDIR}/${QSPEC}${c}.gff"
	if [ ! -f $file ]; then
	    echo "Creating quantitative specification for client $c: $file"
	    cat ${SPECDIR}/${QSPEC}0.gff | sed "s/r0/r${c}/g" | sed "s/g0/g${c}/g" > $file
	fi
    done
    input=${QSPEC}0.gff
    name="0"
    for (( i=1; i<$NUM; i++ )); do
	j=$[$i+1]
	name=$name$i
	output=${QSPEC}${name}.gff
	if [ ! -f ${SPECDIR}/$output ]; then
	    scala quasy.Main prodADD ${SPECDIR}/$input ${SPECDIR}/${QSPEC}${i}.gff ${SPECDIR}/$output
	fi
	input=$output
    done	
fi

##################################
# Check safety specification
file=${SPECDIR}/$SSPEC${final}.gff
if [ ! -f $file ]; then
    echo "Creating safety specification for ${NUM} clients: $file"

cat > "$file" <<EOF
<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<structure label-on="transition" type="FiniteStateAutomaton">
    <!--The list of alphabets.-->
    <alphabet type="propositional">
EOF

    for (( i=0; i<$NUM; i++ )); do
        echo "<prop>g${i}</prop>" >> $file
    done
cat >> "$file" <<EOF
    </alphabet>
    <stateSet>
        <state sid="0">
            <x>197.0</x>
            <y>118.0</y>
        </state>
    </stateSet>
    <transitionSet>
EOF
    id=0
    for (( i=0; i<$NUM; i++ )); do
	label=g${i}
	for (( j=0; j<$NUM; j++ )); do
	    if [ "$i" != "$j" ]; then
		label="${label} ~g${j}"
	    fi
	done
	cat >> "$file" <<EOF
        <transition tid="${i}">
            <from>0</from>
            <to>0</to>
            <read>${label}</read>
        </transition>
EOF
    done
    label="~g0"
    for (( i=1; i<$NUM; i++ )); do
	label="${label} ~g${i}"
    done
    cat >> "$file" <<EOF
        <transition tid="${NUM}">
            <from>0</from>
            <to>0</to>
            <read>${label}</read>
        </transition>
    </transitionSet>
    <initialStateSet>
        <stateID>0</stateID>
    </initialStateSet>
    <acc type="buchi">
        <stateID>0</stateID>
    </acc>
    <description/>
</structure>
EOF
fi

##################################
# Check probabilitiy distrubtion
file=${SPECDIR}/$DISTR${final}.txt
if [ ! -f $file ]; then
    echo "Creating probability distribution for ${NUM} clients: $file"
    p=""
    for (( i=0; i<${NUM}; i++ )); do
	v=$[3+i]
        p="${v} ${p}"
    done
    echo $p
    ./bin/test/distr ${NUM} $p > $file
fi

##################################
# Call QUASY
#old MDP solver
#scala -classpath bin quasy.Main solveMDP ${SPECDIR}/$QSPEC${final}.gff ${SPECDIR}/$SSPEC${final}.gff ${SPECDIR}/$DISTR${final}.txt $OUTDIR/$CDIR${final}
#new solver
echo "Run quasy"
echo "scala -classpath bin quasy.Main solveMDPext ${SPECDIR}/$QSPEC${final}.gff ${SPECDIR}/$SSPEC${final}.gff ${SPECDIR}/$DISTR${final}.txt $OUTDIR/$CDIR${final}"
scala -classpath bin quasy.Main solveMDPext ${SPECDIR}/$QSPEC${final}.gff ${SPECDIR}/$SSPEC${final}.gff ${SPECDIR}/$DISTR${final}.txt $OUTDIR/$CDIR${final}

