/**
 * Deterministic automata generator for formulas for the form
 * /\_i G(ri --> F(gi))               Response property for n clients
 * /\_i,j (i==j) \/ G( ~gi \/ ~gj)    Mutual Exclusion for n clients
 *
 * The automaton is generated as the product of n automata of the
 * following form:
 * 
 * States: OK,RQ
 * Initial state: OK
 * Transitions: state -label-> state, where the label = (request, grant)
 * OK -(F,F)-> OK
 * OK -(T,F)-> RQ
 * OK -(X,T)-> OK
 * RQ -(X,T)-> OK
 * RQ -(X,F)-> RQ
 * Accepting states: OK
 *
 * To obtain a parity condition, the product includes a counter
 * indicating with client should be served next. More precisely,
 * the product automaton consides of n+1 layers labeled with {0..n},
 * where n is the number of clients.
 * The automaton starts in Layer n, which is the only accepting layer.
 * In Layer n, the counter is always reset to 0.
 * In Layer i, if the current State s is accepting with respect to
 * Client i, then the counter is incremented by 1 and all outgoing
 * transitionf of State s go to states in the next layer.
 * (We check this condition starting with Client 0 upto n. So, a
 * transition can jump over layers, if the current state is accepting
 * wrt several clients. E.g., in Layer 3, if State s is accepting
 * wrt to Client 3, 4 and 5, then all outgoing transitions from
 * State (s,3) in the product will lead to states in Layer 6.
 * */

import scala.List
import scala.collection.mutable.Set
import java.io.FileWriter
package test {

sealed abstract class Proposition
case object T extends Proposition //value true
case object F extends Proposition //value false
case object X extends Proposition //value don't care

sealed abstract class State
case object OK extends State //no outstanding request
case object RQ extends State //outstanding request

object TestResponse {

  /**
   * Type declarations
   */
  type PLabel = List[(Proposition, Proposition)]
  type PState = List[State]
  type PTrans = Map[PLabel,PState]

  /**
   * Data
   */
  val transitions : Map[State, PTrans] = Map(
    OK -> Map( List((F,F)) -> List(OK), List((X,T)) -> List(OK), List((T,F)) -> List(RQ) ), 
    RQ -> Map( List((X,T)) -> List(OK), List((X,F)) -> List(RQ) ))

  object config {
    var num = 2                   //number of clients
    var filename = "response.gff" //ouput files
    var debug = false             //debug value
    var accept = 0                //format of acceptance condition
  }
  var pStates      : Set[(PState,Int)] = Set[(PState,Int)]()
  var pStateIds    : Map[(PState,Int),Int] = Map[(PState,Int),Int]()
  var pTransitions : Set[((PState,Int),PLabel,(PState,Int))] = Set[((PState,Int),PLabel,(PState,Int))]()

  var pStatesToExpand : Set[(PState,Int)] = Set[(PState,Int)]()

  
  /**
   * String version of states and labels
   */
  def toStringPState ( s : (PState, Int) ) : String = s._1.foldLeft("")((b,a) => b + a) + s._2
  def toStringPLabel( ll : PLabel, pos: Int ) : String = ll match {
    case Nil => ""
    case l::ll => {
      val req = l._1 match {
	case T => " r" + pos
	case F => " ~r" + pos
	case X => "" //don't care value
      }
      val grant = l._2 match {
	case T => " g" + pos
	case F => " ~g" + pos
	case X => "" //don't care value
      }
      req + grant + toStringPLabel(ll, pos+1)
    }
  }
  
  /**
   * functions to print automaton in GOAL format to file
   */
  def writeAutomaton( file: FileWriter ) : Unit = {
    writeHeader(file)
    writePropositions(file)
    writeStates(file)
    writeTransitions(file)
    writeAcceptance(file)
    writeFooter(file)
  }
  def writeHeader( file: FileWriter ) : Unit = {
    file.write("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n")
    file.write("<structure label-on=\"transition\" type=\"FiniteStateAutomaton\">\n")
    file.write("    <name/>\n")
    file.write("    <description/>\n")
    file.write("    <formula/>\n")
  }
  def writePropositions( file: FileWriter ) : Unit = {
    file.write("    <!--The list of alphabets.-->\n")
    file.write("    <alphabet type=\"propositional\">\n")
    for (i <- 0 to config.num-1) {
      file.write("    <prop>r" + i + "</prop>\n");
      file.write("    <prop>g" + i + "</prop>\n");
    }
    file.write("    </alphabet>\n")
  }
  def writeFooter( file: FileWriter ) : Unit = {
    file.write("    <properties/>\n")
    file.write("</structure>\n")
  }

  def getStateXPos ( s: PState) : Int = {
    s.foldLeft(0)( (i,s) => {
      val m : Int = s match {
	case OK => 0
	case RQ => 1
      }
      2*i + m
    })
  }
  def writeStates( file: FileWriter ) : Unit = {
    file.write("    <stateSet>\n")
    for ( pState <- pStates ) {
      val id = pStateIds.apply(pState)
      val pos  = getStateXPos(pState._1)
      val rank = pState._2
      if (config.debug) {
	println("state: " + pState._1 + " id: " + id + " rank: " + rank + " pos: " + pos)
      }
      file.write("        <state sid=\"" + id + "\">\n")
      file.write("            <X>" + 200*(pos+1) + "</X>\n")
      file.write("            <Y>" + 200*(rank+1) + "</Y>\n")
      file.write("            <properties/>\n")
      file.write("        </state>\n")
    }
    file.write("    </stateSet>\n")
    file.write("    <initialStateSet>\n")
    file.write("        <stateID>0</stateID>\n")
    file.write("    </initialStateSet>\n")
  }
  def writeTransitions( file: FileWriter ) : Unit = {
    var tId = 0
    file.write("    <transitionSet>\n")
      pTransitions.map( e => {
	val stateId =  pStateIds.apply(e._1)
	val label : PLabel = e._2
	val succId = pStateIds.apply(e._3)
	file.write("        <transition tid=\"" + tId  + "\">\n")
	tId = tId + 1
	file.write("            <from>" + stateId + "</from>\n")
	file.write("            <to>" + succId + "</to>\n")
	file.write("            <label>" + toStringPLabel(e._2, 0) + "</label>\n")
	file.write("            <properties/>\n")
	file.write("        </transition>\n")
      } )		     
    file.write("    </transitionSet>\n")
  }
  def writeAcceptance( file: FileWriter ) : Unit = {
    config.accept match {
      case 1 => file.write("""    <acc type="Bchi">""")
      case _ => file.write("""    <acc type="Parity">""")
    }

    file.write("\n        <accSet>\n")
    pStates.filter( e => (e._2 == config.num)).map( e => {
      file.write("            <stateID>" + pStateIds(e) + "</stateID>\n")
    })
    file.write("        </accSet>\n")

    if (config.accept == 0) {
      file.write("        <accSet>\n")
      pStates.filter( e => (e._2 != config.num)).map( e => {
	file.write("            <stateID>" + pStateIds(e) + "</stateID>\n")
      })
      file.write("        </accSet>\n")
    }

    file.write("    </acc>\n")
  }

  def makeProduct (m: PTrans, p: PLabel, s: PState ) : PTrans = {
    if (m.isEmpty) {
      m
    } else {
      val newMap : PTrans = m.map( e => {
	val e1 = e._1 ::: p
	val e2 = e._2 ::: s
	(e1,e2)
      })
      newMap
    }
  }

  /**
   * functions to generate the product automaton
   */
  def makeInitialPState( n : Int ) : PState = n match {
    case 0 => Nil
    case n => OK::makeInitialPState(n-1)
  }

  def addNewStates( tr : PTrans, nRank: Int) : Unit = {
      val tmp : List[(PState,Int)] = tr.map( e => (e._2, nRank)).toList
      for (s <- tmp) {
	if (pStates.exists ( u => (s == u) ) ) {
	  //println ("State already listed")
	} else {
	  pStatesToExpand += s
	  val entry = (s , pStateIds.size)
	  pStateIds +=  entry
	  pStates += s
//	  println("New State: " + s)
	}
      }
  }

  def addNewTransitions( pState : PState, rank : Int, tr: PTrans, nRank :Int) : Unit = {
      for (t <- tr) {
	val entry : ((PState,Int),PLabel,(PState,Int)) = ((pState,rank), t._1, (t._2,nRank))
	  pTransitions += entry
	//	println("New Transition: " + entry)
      }
  }

  /**
   * remove all edges that violate mutual exclusion, i.e., edges that
   * have more than one grant
   */
  def enforceMutualExclusion( m: PTrans ) : PTrans =  
    m.filter( e => {
      val label = e._1
      (label.count( p => (p._2 == T)) <= 1)
    } )

  /**
   * MAIN
   */
  def main(args : Array[String]) : Unit = {

    //parse command-line options
    val commandLineParser = new OptionParser("testReponse") {
      intOpt("n","num", "number of clients", {v: Int => config.num = v})
      opt("o","output", "<filename>", "output file name", {v: String => config.filename = v})
      booleanOpt("d", "debug", "turn debugging on/off", {v: Boolean => config.debug = v})
      intOpt("a", "accept", "format of acceptance condition: \n\t0..parity (default)\n\t1..Buechi", {v: Int => config.accept = v})
    }
    if (!commandLineParser.parse(args)) {
      System.exit(0)
    }
    println("Building response specification for " + config.num + " clients.")
    println("Writing specification to " + config.filename + ".")

    val init = (makeInitialPState(config.num), config.num)
    pStates += init
    pStatesToExpand += init
    val initId = (init , pStateIds.size)
    pStateIds +=  initId

    while (! pStatesToExpand.isEmpty) {
      val  (pState, rank) = pStatesToExpand.head
      pStatesToExpand.remove( (pState, rank) )
      if (config.debug) println("Expanding state: " + toStringPState( (pState, rank) ) )

      //all pStates with rank = num are accepting
      //rank is always reset to 0, in a state with rank=n
      var nRank = rank % config.num

      //Client 0
      val state = pState(0)
      var tr = transitions(state)
      if ( (nRank == 0) && (state == OK) ) { nRank = nRank + 1 }

      //Client 1 to n-1
      for (i <- 1 to pState.length-1) {
	val state = pState(i)
	if ( (nRank == i) && (state == OK) ) { nRank = nRank + 1 }
	var nTr = tr.empty
	for ( edge <- transitions(state) ) {
	  val prod = makeProduct( tr, edge._1, edge._2 )
	  prod.map( e => nTr = nTr + e)
	}
	tr = enforceMutualExclusion(nTr)
      }
      addNewStates( tr, nRank )
      addNewTransitions( pState, rank, tr, nRank )
    }
    //open and write to output file
    val file = new FileWriter(config.filename)
    writeAutomaton(file)
    file.close
  }
}

}
