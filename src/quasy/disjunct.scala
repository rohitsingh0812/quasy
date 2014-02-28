import scala.xml._
import scala.collection.mutable._
import scala.io.Source
import java.util.Arrays._
package quasy {

/*********************************************
 * A Boolean Disjunction
 *********************************************/
class disjunct { //used for conversion of automaton into games

    def pow(n: Int, m: Int): Int = {
    def _pow(m: Int, acc: Int): Int  = m match {
        case 0 => acc
        case _ => _pow(m - 1, acc * n)
    }
     _pow(m, 1)
    }

    //representing disjunction of input variable r0,r1,...
     var pos = new java.util.HashSet[Int]()
     var neg = new java.util.HashSet[Int]()

     //to check if a disjunctive formula implies other
     //useful in merging newly created player 0 states
     def implies(b : disjunct) : Boolean ={
     	//does this => b
	if(pos.containsAll(b.pos) && neg.containsAll(b.neg)){
		return true
	}
	else return false
     }

     def TOINT() : Int = {
         var itr = pos.iterator
         var sum : Int = 0
         while(itr.hasNext()){
            sum = sum + pow(2,itr.next)
         }
         return sum
     }
}


}
