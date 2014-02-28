import scala.xml._
import scala.collection.mutable._
import scala.io.Source
import java.util.Arrays._
package quasy {

/*********************************************
 * An Action for MDP
 *********************************************/
class Action { //associated to a state
     var id : Int = 0
     var pState = new State //parent State
     var distr = new HashMap[State,Double] //probability mapped to states
     var weight : Int = 0
     var edge = new Edge
     def printAct = {
         print("{" + weight +" , " + pState.id)
         for(s <- distr.keys){
             print(" : (" + s.id + ","+ distr(s) +")" )
         }
         println("}")
     } //print Attributes of the action
     def stringAct = {
         var STR = ""
         for(s <- distr.keys){
             STR += "\t\tEDGE\t" + s.id + "\t-1\t"+ distr(s) +"\t"+weight+"\t1\n"
         }
         STR
     } //String of the action
}




}
