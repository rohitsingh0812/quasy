import scala.xml._
import scala.collection.mutable._
import scala.io.Source
import java.util.Arrays._
package quasy {
/*********************************************
 * * An Edge
 *********************************************/
class Edge {//Generic edge used for representing edges in game as well as automaton
  //for general directed Graph with weights
  var id = 0
  var from = new State
  var to = new State
  //for automaton(specifications)
  var weight = 0 //actual value of weights
  var dweight = new HashMap[Int,Int] //for d-dimensional weights
  var Rpos = new java.util.HashSet[Int]() //for representing Request Part of the label
  var Rneg = new java.util.HashSet[Int]()
  var Gpos = new java.util.HashSet[Int]() //for representing Grants Part of the label
  var Gneg = new java.util.HashSet[Int]()
  //for Game
  var TypeOfEdge = 0 // player 0 to 1 is type 0 and player 1 to 0 is type 1
  var pos = List[Int]()
  var neg = List[Int]()
  var label = "" //input AP : r0,r1,... & Output AP : g0,g1,...
  //for MDP
  var prob : Double = 0.0 //probability for edges of type P1-P0 (environment choice)
  //methods
  def sortedUKeys(map: Map[Int, Int]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
  def checkWeight : Boolean = {
  	var d : Int = dweight.size
  	for(i <- 0 to d-1){
  		if(!(dweight.isDefinedAt(i))){
  			println("Error!!! edge id : " + id)
  			return false
  		}
  	}
  	return true
  } //ensures contiguous mapping of dimensions in weight vectors
  //sets label for a Game edge using lists pos and neg
  def setLabel = { 
        label = ""
        if(TypeOfEdge == 1){
     		pos.foreach{ i =>
  			label = label + " r" + (i).toString
  		}
  		neg.foreach{ i =>
  			label = label + " ~r" + (i).toString
  		}
  	}
  	else {
  		pos.foreach{ i =>
  			label = label + " g" + (i).toString
  		}
  		neg.foreach{ i =>
  			label = label + " ~g" + (i).toString
  		}
  	}
  	//println(95)
  	var wStr = ""
  	for(i <- sortedUKeys(dweight)){
  		wStr = wStr + "v" + dweight(i)
  	}
  	//println(wStr)
  	wStr = "w" + wStr.substring(1,wStr.length)
  	label = label + " "+wStr
  	//println(103)
   }
}
}
