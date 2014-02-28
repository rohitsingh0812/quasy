import scala.xml._
import scala.collection.mutable._
import scala.io.Source
import java.util.Arrays._
package quasy {

/*********************************************
 * A State
 *********************************************/
class State { //Generic state used for representing a game as well as automaton
     //for directed Graph representation
     var id = 0
     var outgoing = new HashMap[Int,Edge]
     var incoming = new HashMap[Int,Edge]
     //for reachability check from starting state
     var marked : Boolean = false
     //for product of automaton
     var ti = 0
     var tj = 0 // (i,j) -> ni + j
     var copiedID = 0 //auto2game conversion 
     var viDone = false //dynamic improvement in value iteration in MPG
     //for Game representation
     var parity = -1
     var DFSmark = false
     var DFSparent : Int = -1
     var player = 0
     var value = 0.0 
     var oldv = 0.0 // for storing old value of the state while redoing value
                    //iteration for optimal strategy computation
     var valueVect = new HashMap[Int,Double] //for lexicographic Games
     //methods
     def addOutgoingEdge(e: Edge) = {
	 outgoing(e.id) = e
     }
     def addIncomingEdge(e: Edge) = {
	incoming(e.id) = e
     }
     //for MDP
     var actions = new HashMap[Int,Action] //set of all actions
     var selAct : Int = 0 //selected action for policy iteration
     var pDistr = new HashMap[Int,Double] //probability distribution
     //mapping stateID to prob
     var useless = 0; //
}




}


