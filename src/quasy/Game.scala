import scala.xml._
import scala.math._
import scala.collection.mutable._
import scala.io.Source
import java.util.Arrays._

package quasy {

/* ********************************************
 * A Game
 * Also used for representing Specification automaton (generic)
 ******************************************** */
class Game { 
  //auxiliary functions
  def max(a : Double, b: Double) : Double = {
  	if(a < b) return b
  	else return a
  }
  def min(a : Double, b: Double) : Double = {
   	if(a > b) return b
   	else return a
  }
  def abs(a : Double) : Double = {
  	if (a < 0) return (-1 * a)
  	else return a
  }
  def TOLIST(S : java.util.HashSet[Int]) : List[Int] ={
  	var L : List[Int] = List[Int]()
  	var itr = S.iterator
  	while(itr.hasNext()){
  		L = L ::: List[Int](itr.next)
  	}
  	return L
  }
  object Int {
    def unapply(s : String) : Option[Int] = try {
      Some(s.toInt)
    } catch {
      case _ : java.lang.NumberFormatException => None
    }
  }
  def getValue(s: String): Int = s match {
       case "inf" => Integer.MAX_VALUE
       case Int(x) => x
       case _ => -1
  }
  var dbgstop = false
  var vals = new Array[Double](1) //Array of all possible values for MPG
  var Cchk = 20000
  var EPSDBL = 1e-10
  def Equals (a : Double, b : Double) : Boolean ={
    if (a==b) return true
    else if( a < b && (b-a) < EPSDBL) return true
    else if (a > b && (a-b)<EPSDBL) return true
    else return false
  }
  //used for dynamic improvement
  def updateVals() ={
  	var n = states.size
  	var W = maxWeight()
        println(W)
	var S = scala.collection.immutable.HashSet[Double]()
	S = S + 0.0
        //println(n*(n+2)*W/8)
	for(k <- 1 to (n/2).toInt){
		for(p <- 1 to (k*W).toInt){
		  //println(S.size)
                  S = S + ((p*1.0)/(2.0*k))
		}
	}
	vals = S.toArray
	sort(vals)
  }
  var numStates = 0; //for MDP
  def isUnique(lb : Double, ub : Double) : Double ={

        //var dne = false
        //var ctr = 0
        var num = -1
        var den = -1
        var n = states.size
        var k = 0
        var li : Int = 0
        var ui : Int = 0
        var W = maxWeight()
        for(l <- 1 to (n/2).toInt){
          k = 2* ((n/2).toInt -l +1)
          li = (math.floor(k*lb)).toInt
          ui = (math.floor(k*ub)).toInt
          assert(li <= k*lb && ui <= k*ub )
          
          //assert(li>=0 && ui >=0)
          if (!Equals(li.toDouble,k*lb) && ui  - li  >= 2 && li <= (k/2)*W -2 ){
            if(dbgstop) println("Case 1 :" + li + "," + ui + "," + k + "," + W)
            return -1
          }
          else if (Equals(li.toDouble,k*lb) && ui - li >= 1 && li <= (k/2)*W -1){
            if(dbgstop) println("Case 2 :" + li + "," + ui + "," + k + "," + W)
            return -1
          }
          else if (ui != li) {
            if(num == -1){
              num = ui
              den = k  
            }
            else{
              if(num*k != ui * den ){
                if(dbgstop) println("Case 3 : "+ num/den.toDouble + " , " + ui/k.toDouble + " bounds : (" + lb + "," + ub +") li :" + li + " ui :" + ui)
                return -1
              }
            }
          }
        }
        assert(num != -1)
        return (num/(den.toDouble))
/*         var l = binarySearch(vals,lb)
  	var u = binarySearch(vals,ub)
//  	print("values :")
  	var n= vals.size
  	var old_l = 0
  	if(l<0) {
  		old_l = -l - 1
  		l = n + l + 1
  	}
	else{
		old_l = l
		l = n - l
	}
  	if(u<0) u  = -u - 1
	else u = u +1
	var num = u +l-n
//	println("("+u+","+l+","+n+","+old_l+")")
	if(num > 1) return -1
	if(num == 1){
//	  println(old_l)
	  return vals(old_l)
	}
	println(" DEBUG : ERROR!!!")
  	return -1
 */
  }
  var modeparity = false
  //checks if the
  //current approximation is unique in (lb,ub) using binary search in vals
  var redmpg_mode = 0 //LexMPG mode with weight conversions using base
  var mode_MDP = 0 //Markov Tree Measure
  var b:Int = 0 //base for lex conversions
  var lex_mode = 0 //1 for lex addition
  //general HashMaps for states and edges
  var states = new HashMap[Int, State]
  var edges = new HashMap[Int, Edge]
  //for discounted Game
  var L = 1.0 //lambda for discounted Game
  var wMax = 0 //specifying range of weights from -wMax to wMax
  //( or 0 to 2*wMax... addition of constants to each weight doesn't matter)
  var bufferedEdges = new HashMap[Int, Edge] //for finding optimal strategy
  //from values we use this as buffer to retain removed edges
  //for debugging
  var countG = 0
  var ni = 1 // no. of input vars (r0,r1,...)
  //for specification(automaton)
  var dim = 1 //dimension of weights (LMPA)
  //debugging and printing
  /* ************************************ */
  def printAutomaton = { //for debugging
    for ( s <- sortedSKeys(states)) {
      Console.print(states(s).id +"= label : ("+ states(s).ti +"," + states(s).tj + ")\tin: ")
      for ( e <- states(s).incoming.values) {
	Console.print(e.id + " ")
      }
      Console.print(" \tout: ")
      for ( e <- states(s).outgoing.values) {
	Console.print(e.id + " ")
      }
      Console.println
    }
    for ( t <- sortedEKeys(edges)) {
      Console.print( edges(t).id + ": " + edges(t).from.id + "->" + edges(t).to.id)

      Console.print(" w: (")
      for ( i <- edges(t).dweight.values){
      	Console.print(i)
      	Console.print(" ")
      }
      print(")")
      printSet2(edges(t).Rpos)
      printSet2(edges(t).Rneg)
      printSet2(edges(t).Gpos)
      printSet2(edges(t).Gneg)
      println(") l: "+ edges(t).label)

    }
  }
  def check = {
  	for(s <- states.values){
  		if(states(s.id) != s){
  			println("ERROR State ID " + s.id )
  		}
  	}

  	for(e <- edges.values){
  		if(edges(e.id) != e){
  			println("ERROR Edge ID "+e.id)
  		}
  	}
  }
  def showMapDSet(M : HashMap[disjunct,java.util.HashSet[Int] ]){
  	println("Rpart :")
  	for(R <-M.keys){
  		printSet2(R.pos)
  		printSet2(R.neg)
  		print (" : ")
  		printSet2(M(R))
  		println()
  	}
  }
  def printSet(S : java.util.HashSet[Int]){
  	return
  }
  def printSet2(S : java.util.HashSet[Int]){
  	var itr = S.iterator
  	print("( ")
  	while(itr.hasNext()){
  		print(itr.next + " ")
  	}
  	print(") ")
  }
  def printSetD(S : java.util.HashSet[disjunct]){
  	var itr = S.iterator
  	print("( ")
  	while(itr.hasNext()){
  		var D = itr.next
  		printSet2(D.pos)
  		print(" ")
  		printSet2(D.neg)
  	}
  	print(") ")
  }
  //sorting keys of hashMaps
  def sortedSKeys(map: Map[Int, State]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
  def sortedEKeys(map: Map[Int, Edge]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
  def sortedUKeys(map: Map[Int, Int]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
  def sortedRKeys(map: Map[Float, Float]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
  /* ******************************************* */
  //for debugging
  def printMachine = {
    for ( s <- sortedSKeys(states)) {
      Console.print(states(s).id + "\tin: ")
      for ( e <- states(s).incoming.values) {
	Console.print(e.id + " ")
      }
      Console.print(" \tout: ")
      for ( e <- states(s).outgoing.values) {
	Console.print(e.id + " ")
      }
      Console.println
    }
    for ( t <- sortedEKeys(edges)) {
      print( edges(t).id + ": " + edges(t).from.id + "->" + edges(t).to.id)

      println(" l: " + edges(t).label);
    }
  }
  /* ******************************************* */
  //export mealy machine to .gff file
  def exportMachine = {
    var out_file = new java.io.FileOutputStream("tempf.gff")
var os = new java.io.PrintStream(out_file)


    os.print("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?> \n <!--GFF created with GOAL 2009-04-19.--> \n <structure label-on=\"transition\" type=\"fa\">\n<!--The list of alphabets.-->\n<alphabet type=\"propositional\">\n</alphabet>\n<!--The list of states.-->\n<stateSet>\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<state sid=\"" + states(s).id  + "\">\n</state>\n")
    }
    os.print("</stateSet>\n<!--The list of transitions.-->\n<transitionSet>\n")
    for ( t <- sortedEKeys(edges)) {
      os.print( "<transition tid=\"" + t + "\">\n<from>" + edges(t).from.id + "</from>\n<to>" + edges(t).to.id + "</to>\n<read>" + edges(t).label + "</read>\n</transition>\n")
    }
    os.print("</transitionSet>\n<!--The list of initial states.-->\n<initialStateSet>\n<stateID>0</stateID>\n</initialStateSet>\n<!--The ACC record.-->\n<acc type=\"buchi\">\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<stateID>"+ states(s).id +"</stateID>\n")
    }
    os.print("</acc>\n<!--The automaton description record.-->\n<description/>\n</structure>\n")
    os.close
  }
  /* ******************************************* */
  //debugging
  def printGame = {
    for ( s <- sortedSKeys(states)) {
      Console.print(states(s).id +"= player : "+ states(s).player + "\tin: ")
      for ( e <- states(s).incoming.values) {
	Console.print(e.id + " ")
      }
      Console.print(" \tout: ")
      for ( e <- states(s).outgoing.values) {
	Console.print(e.id + " ")
      }
      Console.println
    }
    for ( t <- sortedEKeys(edges)) {
      print( edges(t).id + ": " + edges(t).from.id + "->" + edges(t).to.id)

      print(" w: " + edges(t).weight)
      edges(t).setLabel
      println(" label :" + edges(t).label)
    }
  }
  /* ******************************************* */
  //algorithm : converting optimal strategy to a Mealy Machine
  def buildMealyMachine(): Game = {
  	var G = new Game
  	for ( s <- states.values){
  		if(s.player == 1){
  		        var s1 = new State
  		        s1.id = s.id
  			G.states(s.id) = s1
  		}
  	}
	for ( s <- states.values){
  		if(s.player == 1){
  		        for ( e <- s.outgoing.values){
  		        	val t = e.to
  		        	if(t.outgoing.size != 1) {
  		        	 println("error!!! more than 1 edge")
  		        	}
  		        	for ( f <- t.outgoing.values){
  		        		var h = new Edge
  		        		h.id = e.id
  		        		h.from = G.states(e.from.id)
  		        		h.to = G.states(f.to.id)
  		        		e.pos.foreach{ i =>
  		        			h.label = h.label + " r" + (i).toString
  		        		}
  		        		e.neg.foreach{ i =>
  		        			h.label = h.label + " ~r" + (i).toString
  		        		}
  		        		f.pos.foreach{ i =>
  		        			h.label = h.label + " g" + (i).toString
  		        		}
  		        		f.neg.foreach{ i =>
  		        			h.label = h.label + " ~g" + (i).toString
  		        		}
  		        		G.addEdge(h)
  		        	}
  		        }
  		}
  	}
  	return G
  }
  /* ******************************************* */

  /* ******************************************* */
  //algorithm : converting optimal strategy to a Mealy Machine
  def buildMealyMachineActs(): Game = {
  	var G = new Game
  	for ( s <- states.values){
  		if(s.player == 1){
  		        var s1 = new State
  		        s1.id = s.id
  			G.states(s.id) = s1
  		}
  	}
	for ( s <- states.values){
  		if(s.player == 1){
  		        for ( e <- s.outgoing.values){
  		        	val t = e.to //p0 state
  		        	var f = t.actions(t.selAct).edge
                                /*if(t.outgoing.size != 1) {
  		        	 println("error!!! more than 1 edge")
  		        	}*/
  		        	//for ( f <- t.outgoing.values){
                                var h = new Edge
                                h.id = e.id
                                h.from = G.states(e.from.id)
                                h.to = G.states(f.to.id)
                                e.pos.foreach{ i =>
                                        h.label = h.label + " r" + (i).toString
                                }
                                e.neg.foreach{ i =>
                                        h.label = h.label + " ~r" + (i).toString
                                }
                                f.pos.foreach{ i =>
                                        h.label = h.label + " g" + (i).toString
                                }
                                f.neg.foreach{ i =>
                                        h.label = h.label + " ~g" + (i).toString
                                }
                                G.addEdge(h)
  		        	//}
  		        }
  		}
  	}
  	return G
  }
  /* ******************************************* */
  // Assumption : sids are ordered contiguous from 0 to size - 1
  // Assumption : Stateid 0 is the starting state
  /* ******************************************* */
  def buildGame(filename: String,lambda : Double) = { //from .gff file to a Game in Memory
    val data = XML.loadFile(filename)
    L = lambda
    val entry = data \\ "stateSet"
    for ( state <- entry \\ "state") {
      val id = state \\ "@sid"
      val s = new State
      val player = state \\ "player"
      s.player = player.text.toInt
      s.id = id.text.toInt
      states(s.id) = s
    }
    var tid = 0
    val transitions = data \\ "transitionSet"
    for ( trans <- transitions \\ "transition") {
      val id = trans \\ "@tid"
      val from = trans \\ "from"
      val to = trans \\ "to"
      val label = trans \\ "read"
      var labels = label.text.split(' ')
      var e = new Edge
      e.id = tid
      tid = tid+1
      e.from = states(from.text.toInt)
      states(from.text.toInt).addOutgoingEdge(e)
      e.to = states(to.text.toInt)
      states(to.text.toInt).addIncomingEdge(e)
      if(e.from.player == 0) e.TypeOfEdge = 0
      else e.TypeOfEdge = 1
      for ( l1 <- labels) {
	var l =(l1).toString
	if(l.head == '~'){
	  var l2 = l.substring(1,l.length)
	  if (l2.head == 'r') {
	    if(ni -1 < l2.substring(1,l2.length).toInt){
	    	ni = 1+l2.substring(1,l2.length).toInt
	    }
	    e.neg = e.neg ::: List(l2.substring(1,l2.length).toInt)
	  }
	  else if (l2.head == 'g') {
	    e.neg = e.neg ::: List(l2.substring(1,l2.length).toInt)
	  }
	}
	else if (l.head == 'r') {
	  e.pos = e.pos ::: List(l.substring(1,l.length).toInt)
	}
	else if (l.head == 'g') {
	  e.pos = e.pos ::: List(l.substring(1,l.length).toInt)
	}
 	else if (l.head == 'w') {
 	  var wts = l.substring(1,l.length).split('v')
	  var ctr = 0
	  for ( w1 <- wts){

	  	var test = w1.toInt
	  	e.dweight(ctr) = test
	  	if(test > 0 && test > wMax){ wMax = test }
	  	if(test < 0 && (-1 * test) > wMax){ wMax = -1*test }
	  	ctr = ctr + 1
	  }
	  dim = ctr
	} else if (l != "True") println("Label " + l + " not recognized.")
      }
      edges(e.id) = e
    }
  }
  /* ******************************************* */
  /*find unreachable states and remove them (BFS)*/
  def reduceAutomaton() = {
  	//mark starting states and then all reachable states and so on
  	var n : Int = states.size
        println("Num of states: " + n)

  	//assumption : starting state is states(0)
  	for(i<-states.keys){
  		states(i).marked = false
  	}
  	states(0).marked = true
  	for(i <- 1 to n){
  		for(s <- states.values){
  			if(s.marked){
				for(e <- s.outgoing.values){
					e.to.marked = true
				}
			}
  		}
  	}
  	for(s <- states.values){
  		if(!s.marked){
  			removeState(s)
  		}
  	}
  }
  def reduceAutomaton2() = {
  	reduceAutomaton
  	var n : Int = states.size
  	var found = false
  	var r = states(0)
  	for(i <- 1 to n){
  		found = false
  		for(s <- states.values){
  			if(!found && s.outgoing.size == 0){
				found = true
				r = s
			}
  		}
  		if(found) removeState(r)
  	}
  }
  /*
  def reduceAutomatonSpecial() = {
  	//mark starting states and then all reachable states and so on
  	//zero weight paradigm here
  	var old_n = states.size
  	states(old_n) = new State
  	var ectr = edges.size
  	var e = new Edge
  	e.id = ectr
  	e.from = states(old_n)
  	e.to = states(old_n)
  	e.weight = 0
  	e.dweight(0) = 0
  	e.label="w0"
  	edges(e.id) = e
  	states(old_n).addOutgoingEdge(e)
  	states(old_n).addIncomingEdge(e)
  	ectr = ectr +1
  	var n : Int = states.size
  	var Se : List[Edge] = List[Edge]()
  	for(e <- edges.values){
  		if(e.weight == 0 && e.to.id != old_n){
  			Se = Se ::: List[Edge](e)
  		}
  	}
  	for(e <- Se){
  		var e1 = new Edge
  		e1.id = ectr
  		e1.from = e.from
  		e1.to = states(old_n)
  		e1.weight = 0
  		e1.dweight(0) = 0
  		e1.label=e.label
  		edges(e1.id) = e1
  		e.from.addOutgoingEdge(e1)
  		states(old_n).addIncomingEdge(e1)
  		e1.Rpos = e.Rpos
  		e1.Rneg = e.Rneg
  		e1.Gpos = e.Gpos
  		e1.Gneg = e.Gneg
  		ectr = ectr+1

  	}
  	for(e <- Se){
  		removeEdge(e)
  	}
  	cleanUp
  	//assumption : starting state is states(0)
  	for(i<-states.keys){
  		states(i).marked = false
  	}
  	states(0).marked = true
  	for(i <- 1 to n){
  		for(s <- states.values){
  			if(s.marked){
				for(e <- s.outgoing.values){
					e.to.marked = true
				}
			}
  		}
  	}
  	for(s <- states.values){
  		if(!s.marked){
  			removeState(s)
  		}
  	}
  }
*/
 /* functions for adding/removing edges and states.
  * Manipulating graph/automaton/game for algorithms*/
 /* ******************************************* */
  def addEdge(e : Edge) = {
  	var u = e.from
  	var v = e.to
  	edges(e.id)=e
	u.outgoing(e.id) = e
	v.incoming(e.id) = e
  }
   /* ******************************************* */
  def addBufferedEdges() = {
  	for(e <- bufferedEdges.values){
  		addEdge(e)
  	}
  }
 /* ******************************************* */
  def removeEdge(e : Edge) = {
  	var U = e.from
  	var V = e.to
  	edges.remove(e.id)
	U.outgoing.remove(e.id)
	V.incoming.remove(e.id)
  }
 /* ******************************************* */
  def removeAllOutgoingEdges(s : State) = {
  	for(e <- s.outgoing.values){
  		removeEdge(e)
  	}
  }
 /* ******************************************* */
  def removeAllIncomingEdges(s : State) = {
  	for(e <- s.incoming.values){
  		removeEdge(e)
  	}
  }
 /* ******************************************* */
  def removeState(s : State) = {
	removeAllOutgoingEdges(s)
	removeAllIncomingEdges(s)
	var id = s.id
	states.remove(s.id)
  }
  /* ******************************************* */
  def removeAndBufferEdge(e : Edge) = {
  	var U = e.from
  	var V = e.to
  	edges.remove(e.id)
	U.outgoing.remove(e.id)
	V.incoming.remove(e.id)
	bufferedEdges(e.id) = e
  }
  /* ******************************************* */
  def emptyBuffer() = {
  	bufferedEdges.clear
  }
  /* ******************************************* */
  /*printing values of states onto Console*/
  def printValues() = {
  	//print(dim)
  	  		println("<!-------------------------------------!>")
  	for ( s <- sortedSKeys(states)){
  		printf("State \t%d has value : ",states(s).id)
  		if(redmpg_mode == 1 || dim == 1) println(states(s).value)
  		else {
  		for(i <- 0 to dim -1){
  			if(i==0) print("("+ states(s).valueVect(i) )
  			else print("," + states(s).valueVect(i) )
  		}
  		println(")")
  		}
  	}
  		println("<!-------------------------------------!>\n")
  }

  def printValuesDIM() = {
  	//print(dim)
  	println("<!-------------------------------------!>")
  	for ( s <- sortedSKeys(states)){
  		print("State \t" + states(s).id +" has value : ")
  		for(i <- 0 to dim -1){
  			if(i==0) print("("+ states(s).valueVect(i) )
  			else print("," + states(s).valueVect(i) )
  		}
  		println(")")
  		}
  	println("<!-------------------------------------!>\n")
  }

  def printValues1D() = {
  	//print(dim)
  	println("<!-------------------------------------!>")
  	for ( s <- sortedSKeys(states)){
  		printf("State \t%d has value : ",states(s).id)
  		println(states(s).value)
  	}
  	println("<!-------------------------------------!>\n")
  }
  //to decide if value of a state is changed or not using a threshold
  def notChanged2(a:Double,b:Double,th: Double) : Boolean = {
  	if(a == b) return true
  	var c = abs(a-b)
  	if(c < 10*th) return true
  	else return false
  }
  /* ******************************************* */
  //threshold check instead of equality of values
  def notChanged(a:HashMap[Int,Double],b:HashMap[Int,Double],th: Double) : Boolean = {
  	for(i <- 0 to dim-1){
  		if(abs(a(i) - b(i)) > 10*th) return false
  	}
  	return true
  }
  def restoreValues(threshold : Double) = {

  	for ( s <- states.values){
  		 s.value = s.oldv
  	}
  }
  def storeValues(threshold : Double) = {

  	for ( s <- states.values){
  		 s.oldv = s.value
  	}
  }
  /* finding Optimal Strategy from values being obtained by value iteration*/
  /* ******************************************* */
  def optimalStrategy2(threshold : Double) = {
  	var oldVal = 0.0
  	for ( s <- states.values){
  		if(s.player == 0 ){
  			while(s.outgoing.size > 1){
  				oldVal = s.value
  				val d = s.outgoing.size
  				var db2 = 0
  				if(d % 2 == 0) db2 = d/2
  				else db2 = (d+1)/2
  				var ctr=0
  				emptyBuffer()
  				for(e <- s.outgoing.values){
  					if(ctr < db2){
  						removeAndBufferEdge(e)
  					}
  					ctr = ctr+1
  				}

  				storeValues(threshold)
  				valueIteration2(threshold)
  				if(notChanged2(s.value,oldVal,threshold)){
  					emptyBuffer()
  				}
  				else{
  					removeAllOutgoingEdges(s)
  					addBufferedEdges()
  					restoreValues(threshold)
  					//valueIteration2(threshold)
  				}
  			}
  		}
  	}
  }
  def optimalStrategyDPG(threshold : Double) = {
  	for ( s <- states.values){
  		if(s.player == 0 ){
                        var firstdone = false
                        var maxVal = 0.0
                        var bestEdge : Edge = new Edge
                        for(e <- s.outgoing.values){
                            if(!(firstdone)){
                                maxVal = (1-L)*e.weight + L * e.to.value
                                bestEdge = e
                                firstdone = true
                            }
                            else if(maxVal < (1-L)*e.weight + L * e.to.value){
                                maxVal = (1-L)*e.weight + L * e.to.value
                                bestEdge = e
                            }
                        }
                        for(e <- s.outgoing.values){
                            if(e != bestEdge) removeEdge(e)
                        }
  		}
  	}
  }
  def optimalStrategyL(threshold : Double) = {
  	var oldVal = 0.0
  	for ( s <- states.values){
  		if(s.player == 0 ){
  			while(s.outgoing.size > 1){
  				oldVal = s.value
  				val d = s.outgoing.size
  				var db2 = 0
  				if(d % 2 == 0) db2 = d/2
  				else db2 = (d+1)/2
  				var ctr=0
  				emptyBuffer()
  				for(e <- s.outgoing.values){
  					if(ctr < db2){
  						removeAndBufferEdge(e)
  					}
  					ctr = ctr+1
  				}
  				valueIteration(threshold)
  				if(notChanged2(s.value,oldVal,threshold)){
  					emptyBuffer()
  				}
  				else{
  					removeAllOutgoingEdges(s)
  					addBufferedEdges()
  					valueIteration(threshold)
  				}
  			}
  		}
  	}
  }
  /* finding Optimal Strategy from values being obtained by value iteration*/
  /* ******************************************* */
  def optimalStrategy(threshold : Double) = {
  	var oldVal = zeroVectD(dim)
  	for ( s <- states.values){
  		if(s.player == 0 ){
  			while(s.outgoing.size > 1){
  				oldVal = s.valueVect
  				val d = s.outgoing.size
  				var db2 = 0
  				if(d % 2 == 0) db2 = d/2
  				else db2 = (d+1)/2
  				var ctr=0
  				emptyBuffer()
  				for(e <- s.outgoing.values){
  					if(ctr < db2){
  						removeAndBufferEdge(e)
  					}
  					ctr = ctr+1
  				}
  				valueIteration(threshold)
  				if(notChanged(s.valueVect,oldVal,threshold)){
  					emptyBuffer()
  				}
  				else{
  					removeAllOutgoingEdges(s)
  					addBufferedEdges()
  					valueIteration(threshold)
  				}
  			}
  		}
  	}
  }
  /******************************************* */
  def TODOUBLE(v : HashMap[Int,Int]) : HashMap[Int,Double] = {
  	var rVal = new HashMap[Int,Double]
  	for(i <- 0 to dim -1){
  		rVal(i) = v(i)* 1.0
  	}
  	return rVal
  }
/* ******************************************* */
  /*for converting d dimensional weights in appropriate base to numerical weights*/
  def updateWeights() = {
  	if(dim == 1){
  		for ( e <- edges.values){
  			for(v <- e.dweight.values){
  				e.weight = v
  			}
  		}
  	}
  	else{
  		b = states.size * states.size * wMax + 1 //assuming range of weights is 0 to wMax (both inclusive)
  		println("Choosen Base =" + b)
                for ( e <- edges.values){
  			var temp = 1
  			var sum = 0
  			for ( i <- e.dweight.keys.toList.sortWith((e1,e2) => (e1 > e2))){
  				//lexicographic order from left
  				sum = sum + temp*(e.dweight(i))
  				temp =  temp *b
  			}
  			e.weight = sum
  		}
  	}
  }
  def execLoop( delta : Double, vNext : HashMap[Int, Double]) : Boolean = {
     for(s <-states.values){
      	 	if(s.viDone == false){
      	 	var is = isUnique(vNext(s.id) - delta,vNext(s.id) + delta)
      	 	if(is >= 0.0){
      	 		s.value = is
      	 		s.viDone = true
      	 		//if(prmd) println("State :" + s.id +" , value :" + s.value + " , iteration :" + vK)
      	 	}
      	 	else{
      	 		return false
      	 	}
      	 	}
      	 }
         return true
  }
  def valueIterationMPG(threshold : Double) = {
    val n = states.size
    var vCurrent = new HashMap[Int, Double]
    var approxVal = new HashMap[Int, Double]
    var vNext = new HashMap[Int, Double]
    for ( s <- sortedSKeys(states)) vCurrent(s) = 0
    var brk = 0 //there's no way to break a loop in scala! (have to implement ourselves... let it loop without doing anything once done)
    var vK = 0
    var x = 1.0
    var y = 0.0
    var W = maxWeight()
    var bK = 2*n*n*n* W
    var sm = false
    var prmd = false
    if(prmd) println(bK +" :")
    for(s <- states.values) s.viDone =false
    while(brk == 0) {
      vK = vK +1
      x = 1.0/vK
      y = 1.0 - x
      //if(vK % (n*n*W) == 1)print(vK +";")
      sm=false
      if(vK % (Cchk) == 1){
        sm = true
        if(prmd) print(vK + ";")
      }
      for ( v <- states.values) {
        if(v.viDone == false){
	if(v.player == 0){
		var firstdone = 0
		var maxSum = 0.0
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				maxSum = x*e.weight + y*vCurrent(e.to.id)
			}
			else{
				val u = e.to.id
				val newSum = x*e.weight + y*vCurrent(u)
				if (maxSum < newSum){
					maxSum = newSum
				}
			}
		}
		vNext(v.id) = maxSum
	}
	else{
		var firstdone = 0
		var minSum = 0.0
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				minSum = x*e.weight + y*vCurrent(e.to.id)
			}
			else{
				val u = e.to.id
				val newSum = x*e.weight + y*vCurrent(u)
				if (minSum > newSum){
					minSum = newSum
				}
			}
		}
		vNext(v.id) = minSum
	}
	}
      }
      if(vK>1){

      if(sm){
         //println(vK + " : Checking Values... ")
      	 var delta = n*W/(vK.toDouble)
      	 var noneLeft =true

         noneLeft = execLoop(delta,vNext)
      	 if(noneLeft == true) brk = 1
      }
      //println("vK :" +vK + "maxDiff :" +maxDiff)
      //if(maxDiff < threshold || vK == bK)  break = 1 //condition of convergence with a threshold
      //}
      //else{
      	if(vK >= bK) brk = 1
      //}
      }
//      var prmd = false
      //if(vK <= 10 || vK >= 240) prmd = true
      if(prmd) print(vK+":")
      for ( v <- sortedSKeys(states)){
         if(prmd) print( (vNext(v)*vK).toInt + " & ")
      	vCurrent(v) = vNext(v)
      }
      if(prmd) println("| \\\\")
      /*if(vK==250){

      for ( v <- sortedSKeys(states)){
        print("\t" + vNext(v))
      }
      }*/


    }
    //println (break + " < break at : vK = " + vK + " and bK = " + bK)
    if(vK>=bK){
    for ( a <- sortedSKeys(states)){
    	approxVal(a) = (vCurrent(a)).toDouble
    	//print("("+a+":"+approxVal(a)+")")
	/* compute interval */
	var lb = approxVal(a) - 1/((2*n*(n-1)).toDouble)
	var ub = approxVal(a) + 1/((2*n*(n-1)).toDouble)
	var done =0
	for (l <- 1 to ((n).toInt)) {
		if(done == 0){
		var nval = approxVal(a) * l
		var cFrac = 0.0
  		if(nval == (nval).toInt){
  			 cFrac = approxVal(a)
  			 if(cFrac < ub && cFrac > lb){
  			 	states(a).value = cFrac
  			 	done = 1
  			 }
  		}
  		else{
  			cFrac = ((nval).toInt).toDouble/(l).toDouble
  			 if(cFrac < ub && cFrac > lb){
  			 	states(a).value = cFrac
  			 	done = 1
  			 }
  			 cFrac = ((nval).toInt + 1).toDouble/(l).toDouble
  			 if(cFrac < ub && cFrac > lb){
  			 	states(a).value = cFrac
  			 	done = 1
  			 }
  		}
  	    }
	}
    }
    }
    else{
    	for ( a <- sortedSKeys(states)){
    		if(states(a).viDone == false) states(a).value = (vCurrent(a)).toDouble
    	}
    }
    //printValues1D()
    //println()
if(prmd)    println("VI Done! :" + vK)
  }
  def gcd(x:Int, y:Int): Int =  {
    if (x==0) y
    else if (x<0) gcd(-x, y)
    else if (y<0) -gcd(x, -y)
    else gcd(y%x, x)
  }
  def breakingK() : Int = {
    var n = states.size
    var p : Int = (1000*L).toInt
    var q : Int = 1000
    var d : Int = gcd(p,q)
    p = p/d
    q = 1000/d
    var rK: Double  = (2*n+1) * log(q) + log(2*wMax)
    rK = rK/(log(q)-log(p))
    return (rK+1).toInt
  } //for DPG Algorithm
  def valueIteration2(threshold : Double) = {
    val n = states.size
    Cchk = n * n * n
    //println("Check @ :" + Cchk)
     if(dbgstop) println("Value Iteration 2 :-/")
    //can try calculating maximum weight here again
    if(L==1){
    	valueIterationMPG(threshold)
    }
    else {
    var vK = 0
    var vCurrent = new HashMap[Int, Double]
    var vNext = new HashMap[Int, Double]
    for ( s <- sortedSKeys(states)) vCurrent(s) = 0
    var break = 0 //there's no way to break a loop in scala! (have to implement ourselves... let it loop without doing anything once done)
    var bK = breakingK()
    println("going to break at : k= " + bK)
    while(break == 0) {
      vK = vK + 1
      for ( v <- states.values) {
	if(v.player == 0){
		var firstdone = 0
		var maxSum = 0.0
		for ( e <- v.outgoing.values){
			//println(e.weight + "," + L)
                        if(firstdone == 0){
				firstdone = 1
				maxSum = (1-L)*e.weight + L* vCurrent(e.to.id)
			}
			else{
				val u = e.to.id
				val newSum = (1-L)*e.weight + L*vCurrent(u)
				if (maxSum < newSum){
					maxSum = newSum
				}
			}
                        //println(e.weight + "," + L + ", " + maxSum)
		}
		vNext(v.id) = maxSum
	}
	else{
		var firstdone = 0
		var minSum = 0.0
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				minSum = (1-L)*e.weight + L*vCurrent(e.to.id)
			}
			else{
				val u = e.to.id
				val newSum = (1-L)*e.weight + L*vCurrent(u)
				if (minSum > newSum){
					minSum = newSum
				}
			}
		}
		vNext(v.id) = minSum
	}
        
        //print(v.id + " : "+vNext(v.id) +",")
      }
      for ( v <- states.values) {
            vCurrent(v.id) = vNext(v.id)
        }
      //println()
      if(vK == bK) break = 1 //condition of convergence with a threshold
      
    }
    for ( v <- states.keys){
      	states(v).value = vCurrent(v)
    }
    //printValuesDIM()
    }
  }
  /********************************************
  Algorithm for finding values of states of discounted Game
  ********************************************
  */
  def valueIteration(threshold : Double) = {
    //println("Value Iteration :-/")
    val n = states.size
    //can try calculating maximum weight here again
    var vCurrent = new HashMap[Int, HashMap[Int,Double]]
    var vNext = new HashMap[Int, HashMap[Int,Double]]
    if(L==1){
    	valueIterationLMPG(threshold)
    }
    else{
    for ( s <- sortedSKeys(states)) vCurrent(s) = zeroVectD(dim)
    var break = 0 //there's no way to break a loop in scala! (implemented by letting it loop without doing anything once done)
    var dk = 0
    while(break == 0) {
      dk = dk + 1
      for ( v <- states.values) {
	if(v.player == 0){
		var firstdone = 0
		var maxSum = zeroVectD(dim)
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				maxSum = add(multD(TODOUBLE(e.dweight),(1.0-L)) , multD(vCurrent(e.to.id),L))
			}
			else{
				val u = e.to.id
				var newSum = add(multD(TODOUBLE(e.dweight),(1.0-L)) , multD(vCurrent(u),L))
				if (lesser(maxSum , newSum)){
					maxSum = newSum
				}
			}
		}
		vNext(v.id) = maxSum
	}
	else{
		var firstdone = 0
		var minSum = zeroVectD(dim)
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				minSum = add(multD(TODOUBLE(e.dweight),(1.0 - L)) , multD(vCurrent(e.to.id),L))
			}
			else{
				val u = e.to.id
				val newSum = add(multD(TODOUBLE(e.dweight),(1.0 - L)) , multD(vCurrent(u),L))
				if ( lesser(newSum,minSum)){
					minSum = newSum
				}
			}
		}
		vNext(v.id) = minSum
	}
      }
      var maxDiff = 0.0
      for ( v <- states.keys){
        var d = dim
      	for(i <- 0 to d -1){
      		maxDiff = max(maxDiff,abs(vCurrent(v)(i) - vNext(v)(i)))
      	}
      }
      	if(maxDiff < threshold*(1.0-L)) break = 1 //condition of convergence with a threshold
      	var prmd = false
      //if(dk <= 10 || dk >= 1138) prmd = true
      if(prmd) print(dk + " & ")

      	for ( v <- sortedSKeys(states)){
      		if(prmd) printf("%.3f & ",vNext(v)(0))
      		vCurrent(v) = vNext(v)
      	}
      	if(prmd) println("| ")
      }
      println("break :" +dk)
    for ( v <- states.keys){
       	states(v).valueVect = vCurrent(v)

    }
    //printValuesDIM
    }
  }
  def maxWeight() : Double = {
  	var d = dim
  	if(d==1) return wMax
  	//println("b :" +b + ", dim :" +dim)
  	return wMax * (Game.pow(b,dim) - 1.0)/(b-1.0)
  }
  def baseConvert(v : HashMap[Int,Double]) : Double ={
  	var sum = 0.0
  	for(i <- 0 to dim-1){
  		sum = b*sum + v(i)
  	}
  	return sum
  }
  def getFrac(d : Double) : Double = {
    	var approxVal = 0.0
    	val n = states.size
    	var cFrac = 0.0
    	approxVal = d
	var lb = approxVal - 1/((2*n*(n-1)).toDouble)
	var ub = approxVal + 1/((2*n*(n-1)).toDouble)
	var done =0
	//print("("+lb+","+ub+") : ")
	for (l <- 1 to ((n).toInt)) {
	    if(done == 0){
		var nval = approxVal * l.toDouble
		cFrac = 0.0
  		if(nval == (nval).toInt){
  			 cFrac = approxVal
  			 if(cFrac < ub && cFrac > lb){
  			 	//print(l+","+cFrac + "\t\t")
  			 	done = 1
  			 	return cFrac
  			 }
  		}
  		else{
  			 cFrac = ((nval).toInt).toDouble/(l).toDouble
  			 if(cFrac < ub && cFrac > lb){
  			 	//print(l+","+cFrac + "\t\t")
  			 	done = 1
  			 	return cFrac
  			 }
  			 cFrac = ((nval).toInt + 1).toDouble/(l).toDouble
  			 if(cFrac < ub && cFrac > lb){
  			 	//print(l+","+cFrac + "\t\t")
  			 	done = 1
  			 	return cFrac
  			 }
  		}
  	    }
	}
	return cFrac
  } //get exact values from approximations
  def valueIterationLMPG(threshold : Double) = {
    val n = states.size
    //can try calculating maximum weight here again
    var vCurrent = new HashMap[Int, HashMap[Int,Double]]
    var vNext = new HashMap[Int, HashMap[Int,Double]]
    for ( s <- sortedSKeys(states)) vCurrent(s) = zeroVectD(dim)
    var break = 0 //there's no way to break a loop in scala! (implemented by letting it loop without doing anything once done)
    var vK =0
    var x = 1.0
    var y = 0.0
    var W = maxWeight()
    var bK = 2*n*n*n*W
    //println(n +":"+maxWeight())
    //println(bK +" : wmax = " + wMax + "BASE :" + b )
    var sm = false
    for(s <- states.values) s.viDone =false
    while(break == 0) {
      vK = vK +1
      x = 1.0/vK
      y = 1-x
      sm = false
      if(vK % (Cchk) == 1){
        sm = true //check it!!!!
       // print(vK + ";")
      } 

     /*if(vK % 5 == 1){
      	print(vK +";")
      	for ( v <- states.keys){
      		println("VAL("+v+") :" + baseConvert(vCurrent(v)) + " -> " +(getFrac(baseConvert(vCurrent(v)))).toDouble )

      	}
      }*/
      for ( v <- states.values) {
	if(v.player == 0){
		var firstdone = 0
		var maxSum = zeroVectD(dim)
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				maxSum = add(multD(TODOUBLE(e.dweight),x) , multD(vCurrent(e.to.id),y))
			}
			else{
				val u = e.to.id
				var newSum = add(multD(TODOUBLE(e.dweight),x) , multD(vCurrent(u),y))
				if (lesser(maxSum , newSum)){
					maxSum = newSum
				}
			}
		}
		vNext(v.id) = maxSum
	}
	else{
		var firstdone = 0
		var minSum = zeroVectD(dim)
		for ( e <- v.outgoing.values){
			if(firstdone == 0){
				firstdone = 1
				minSum = add(multD(TODOUBLE(e.dweight),x) , multD(vCurrent(e.to.id),y))
			}
			else{
				val u = e.to.id
				val newSum = add(multD(TODOUBLE(e.dweight),x) , multD(vCurrent(u),y))
				if (lesser(newSum,minSum)){
					minSum = newSum
				}
			}
		}
		vNext(v.id) = minSum
	}
      }
      if(vK>1){
      	if(sm){
      	 var delta = n*W/(vK.toDouble)
      	 var noneLeft =true
      	 for(s <-states.values){
      	 	if(s.viDone == false){
                var bC = baseConvert(vNext(s.id))
      	 	var is = isUnique(bC - delta, bC + delta)
      	 	if(is >= 0.0){
      	 		s.value = is
      	 		s.viDone = true
      	 		//println("State :" + s.id +" , value :" + s.value + " , iteration :" + vK)
      	 	}
      	 	else{
      	 		noneLeft =false
      	 	}
      	 	}
      	 }
      	 if(noneLeft == true) break =1
      }

      	if(threshold > 0){
      		var maxDiff = 0.0
      		for ( v <- states.keys){
        		var d = dim
      			for(i <- 0 to d -1){
      				maxDiff = max(maxDiff,abs(vCurrent(v)(i) - vNext(v)(i)))
      			}
      		}
      		if(maxDiff < threshold || vK == bK) break = 1 //condition of convergence with a threshold
      	}
      	else {
      		if(vK == bK) break = 1
      	}
      }
      for ( v <- states.keys){
      		vCurrent(v) = vNext(v)

      }
     }
     //println ("break at : vK = " + vK + " and bK = " + bK)
    if(vK >= bK){
    for ( v <- states.keys){
       		states(v).value = getFrac(baseConvert(vCurrent(v)))
    }
    }
    else{
    	for ( a <- sortedSKeys(states)){
    		if(states(a).viDone == false) states(a).value = baseConvert(vCurrent(a))
    	}
    }
    //printValues1D
    //println("ValueIteration Done!")
    println("VI Done! :" + vK)
  }
  /********************************************
  Input from .gff file to create an
  automaton in memory (MP/Safety specification)
  ******************************************* */
  def buildautomaton(filename: String) = {
    val data = XML.loadFile(filename)
    val entry = data \\ "stateSet"
    for ( state <- entry \\ "state") {
      val id = state \\ "@sid"
      var pr = state \\ "label"
      val s = new State
      s.id = id.text.toInt
      println("New State: " + s.id)
      if(modeparity){
        s.parity = getValue(pr.text)
	println ("Parity:" + s.parity)
      }
      states(s.id) = s
      //println("State: " + states(s.id)) 
    }
    //check if state numbers are consecutive
    val keys = states.keySet.toArray
    scala.util.Sorting.quickSort(keys)
    var num = 0
    for (id <- keys) {
      if (id != num) {
	println("State ids do not follow conventions.")
	println("We require them to be consecutive starting from 0.")
	println("Use \"Reorder States\" in the context menu of GOAL.")
	println("We apologize for the inconvenience.")
	sys.exit(1)
      } else {
	num = num + 1
      }
    }
    var tid = 0
    val transitions = data \\ "transitionSet"
    for ( trans <- transitions \\ "transition") {
      val from = trans \\ "from"
      val to = trans \\ "to"
      val label = trans \\ "read"
      var e = new Edge
      var wtfound = false
      e.id = tid
      tid = tid+1
      println("New Edge: from " + from.text + " to " + to.text)
      e.from = states(from.text.toInt)
      states(from.text.toInt).addOutgoingEdge(e)
      e.to = states(to.text.toInt)
      states(to.text.toInt).addIncomingEdge(e)
      println("Labels: " + label.text)
      var labels = label.text.split(' ')
      for ( l1 <- labels) {
	var l =(l1).toString
	try {
	  if(l.head == '~'){
	    var l2 = l.substring(1,l.length)
	    if (l2.head == 'r') {
	      if(ni - 1 < l2.substring(1,l2.length).toInt){
	  	ni = 1 + l2.substring(1,l2.length).toInt
	      }
	      e.Rneg.add(l2.substring(1,l2.length).toInt)
	    } else if (l2.head == 'g') {
	      e.Gneg.add(l2.substring(1,l2.length).toInt)
	    }
	  } else if (l.head == 'r') {
	    e.Rpos.add(l.substring(1,l.length).toInt)
	  } else if (l.head == 'g') {
	    e.Gpos.add(l.substring(1,l.length).toInt)
	  } else if (l.head == 'w') {
	    wtfound = true
 	    var wts = l.substring(1,l.length).split('v')
	    var ctr = 0
	    for ( w1 <- wts){
	      var test = w1.toInt
	      e.dweight(ctr) = test
	      if(test > 0 && test > wMax){ wMax = test }
	      if(test < 0 && (-1 * test) > wMax){ wMax = -1*test }
	      ctr = ctr + 1
	    }
	    dim = ctr //updateWeights needed to ensure proper allocation of equivalent 1-dim weights --not needed
	  } else println("Label " + l + " not recognized.")
	} catch {
	  case e: NumberFormatException => {
	    println("Automaton does not following the desired input format: ")
	    println("Labels have to be of the form ([~](r | g)N)^* wN, where")
	    println("N is an arbitrary integer, e.g., r0 ~g0 g1 w0.")
	    println("We apologize for the inconvenience!")
	    sys.exit(1)
	  }
	  case e: Exception => throw e
	  sys.exit(1)
	}
      }
      if(!wtfound){
        e.dweight(0) = 1
      }
      edges(e.id) = e
      var itr = e.Rpos.iterator()
      while(itr.hasNext()){
      	e.label = e.label + "r" + itr.next + " "
      }
      itr = e.Rneg.iterator()
      while(itr.hasNext()){
      	e.label = e.label + "~r" + itr.next + " "
      }
      itr = e.Gpos.iterator()
      while(itr.hasNext()){
      	e.label = e.label + "g" + itr.next + " "
      }
      itr = e.Gneg.iterator()
      while(itr.hasNext()){
  	e.label = e.label + "~g" + itr.next + " "
      }
    }
    val acc = data \\ "acc"
    val type1 = acc \\ "@type"
    //println("TYPE :"+type1)
    if(modeparity && type1 == "parity"){
      var parctr = 0
      for ( aset <- acc \\ "accSet") {
        for ( sid <- aset \\ "stateID"){
          states(sid.text.toInt).parity = parctr
        }
        parctr = parctr +1
      }
      for(s <- states.values) assert(s.parity != -1)
    }
    //updateWeights()
  }
  /* ****************************************************** */
  //exporting game with values as labels to .gff file
  def exportGameWithValues(filename : String) = {
    var out_file = new java.io.FileOutputStream(filename)
    var os = new java.io.PrintStream(out_file)
    os.print("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?> \n <!--GFF created with GOAL 2009-04-19.--> \n <structure label-on=\"transition\" type=\"game\">\n<!--The list of alphabets.-->\n<alphabet type=\"propositional\">\n</alphabet>\n<!--The list of states.-->\n<stateSet>\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<state sid=\"" + states(s).id  + "\">\n"+ "<label>" + (states(s).value).toString+"</label>"+ "<player>" + states(s).player+"</player>"+"</state>\n")
    }
    os.print("</stateSet>\n<!--The list of transitions.-->\n<transitionSet>\n")
    for ( t <- sortedEKeys(edges)) {
      edges(t).setLabel
      os.print( "<transition tid=\"" + t + "\">\n<from>" + edges(t).from.id + "</from>\n<to>" + edges(t).to.id + "</to>\n<read>" + edges(t).label +" w" + edges(t).weight + "</read>\n</transition>\n")
    }
    os.print("</transitionSet>\n<!--The list of initial states.-->\n<initialStateSet>\n<stateID>0</stateID>\n</initialStateSet>\n<!--The ACC record.-->\n<acc type=\"buchi\">\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<stateID>"+ states(s).id +"</stateID>\n")
    }
    os.print("</acc>\n<!--The automaton description record.-->\n<description/>\n</structure>\n")
    os.close
  }
  /* ****************************************************** */
  def exportGame(filename : String) = {
    var f = new java.io.File(filename)
    var out_file = new java.io.FileOutputStream(f)
    var os = new java.io.PrintStream(out_file)
    os.print("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?> \n <!--GFF created with GOAL 2009-04-19.--> \n <structure label-on=\"transition\" type=\"game\">\n<!--The list of alphabets.-->\n<alphabet type=\"propositional\">\n</alphabet>\n<!--The list of states.-->\n<stateSet>\n")
    for ( s <- sortedSKeys(states)) {
      if(modeparity){
        os.print("<state sid=\"" + states(s).id  + "\">\n"+ "\">\n"+ "<player>" + states(s).player+"</player>" + "<label>" + states(s).parity + "</label>"+"</state>\n")
      }
      else{
        os.print("<state sid=\"" + states(s).id  + "\">\n"+ "<player>" + states(s).player+"</player>"+"</state>\n")
      }

    }
    os.print("</stateSet>\n<!--The list of transitions.-->\n<transitionSet>\n")
    for ( t <- sortedEKeys(edges)) {
      edges(t).setLabel
      os.print( "<transition tid=\"" + t + "\">\n<from>" + edges(t).from.id + "</from>\n<to>" + edges(t).to.id + "</to>\n<read>" + edges(t).label  + "</read>\n</transition>\n")
    }
    os.print("</transitionSet>\n<!--The list of initial states.-->\n<initialStateSet>\n<stateID>0</stateID>\n</initialStateSet>\n<!--The ACC record.-->\n<acc type=\"buchi\">\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<stateID>"+ states(s).id +"</stateID>\n")
    }
    os.print("</acc>\n<!--The automaton description record.-->\n<description/>\n</structure>\n")
    os.close
  }
  /* ****************************************************** */
  def exportStrategy(filename : String) = {
    var f = new java.io.File(filename)
    var out_file = new java.io.FileOutputStream(f)
    var os = new java.io.PrintStream(out_file)
    os.print("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?> \n <!--GFF created with GOAL 2009-04-19.--> \n <structure label-on=\"transition\" type=\"game\">\n<!--The list of alphabets.-->\n<alphabet type=\"propositional\">\n</alphabet>\n<!--The list of states.-->\n<stateSet>\n")
    for ( s <- sortedSKeys(states)) {
      if(modeparity){
        os.print("<state sid=\"" + states(s).id  + "\">\n"+ "\">\n"+ "<player>" + states(s).player+"</player>" + "<label>" + states(s).parity + "</label>"+"</state>\n")
      }
      else{
        os.print("<state sid=\"" + states(s).id  + "\">\n"+ "<player>" + states(s).player+"</player>"+"</state>\n")
      }

    }
    os.print("</stateSet>\n<!--The list of transitions.-->\n<transitionSet>\n")
    var t=0
    for ( i <- sortedSKeys(states)) {
      if(states(i).useless == 0 && states(i).player == 0){
        for(a <- states(i).actions.values){
          a.edge.setLabel
          if(a.id == states(i).selAct){
              os.print( "<transition tid=\"" + t + "\">\n<from>" + a.edge.from.id + "</from>\n<to>" + a.edge.to.id + "</to>\n<read>" + a.edge.label  + "</read>\n</transition>\n")
              t=t+1
          }
        }
      }
      if(states(i).player == 1){
        for(e <- states(i).outgoing.values){
          e.setLabel
          os.print( "<transition tid=\"" + t + "\">\n<from>" + e.from.id + "</from>\n<to>" + e.to.id + "</to>\n<read>" + e.label  + "</read>\n</transition>\n")
          t=t+1
        }
      }

    }
    
    os.print("</transitionSet>\n<!--The list of initial states.-->\n<initialStateSet>\n<stateID>0</stateID>\n</initialStateSet>\n<!--The ACC record.-->\n<acc type=\"buchi\">\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<stateID>"+ states(s).id +"</stateID>\n")
    }
    os.print("</acc>\n<!--The automaton description record.-->\n<description/>\n</structure>\n")
    os.close
  }
  /* *************************************************** */
  def exportAutomaton(filename : String) = {
    var out_file = new java.io.FileOutputStream(filename)
    //java.io.File f = new java.io.File(filename)
    //var out_file = new java.io.FileOutputStream(filename)
    var os = new java.io.PrintStream(out_file)

    os.print("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?> \n <!--GFF created with GOAL 2009-04-19.--> \n <structure label-on=\"transition\" type=\"fa\">\n<!--The list of alphabets.-->\n<alphabet type=\"propositional\">\n</alphabet>\n<!--The list of states.-->\n<stateSet>\n")
    for ( s <- sortedSKeys(states)) {
      if(modeparity){
        os.print("<state sid=\"" + states(s).id  + "\">\n"+ "<label>" + states(s).parity + "</label>"+"</state>\n")
      }
      else{
        os.print("<state sid=\"" + states(s).id  + "\">\n"+ "<label>(" + states(s).ti+"," + states(s).tj + ")</label>"+"</state>\n")
      }
        //os.print("<state sid=\"" + states(s).id  + "\">\n"+ "<label>(" + states(s).ti+"," + states(s).tj+ ")</label>"+"</state>\n")
    }
    os.print("</stateSet>\n<!--The list of transitions.-->\n<transitionSet>\n")
    for ( t <- sortedEKeys(edges)) {
      os.print( "<transition tid=\"" + t + "\">\n<from>" + edges(t).from.id + "</from>\n<to>" + edges(t).to.id + "</to>\n<read>" + edges(t).label + "</read>\n</transition>\n")
    }
    os.print("</transitionSet>\n<!--The list of initial states.-->\n<initialStateSet>\n<stateID>0</stateID>\n</initialStateSet>\n<!--The ACC record.-->\n<acc type=\"buchi\">\n")
    for ( s <- sortedSKeys(states)) {
      os.print("<stateID>"+ states(s).id +"</stateID>\n")
    }
    os.print("</acc>\n<!--The automaton description record.-->\n<description/>\n</structure>\n")
    os.close
  }
  /* *************************************************** */

  def cleanUp = {
  	//reassignment of state and transitions ids from 0 to max-1
  	var fs = new HashMap[Int,Int]
  	var fe = new HashMap[Int,Int]
  	var i = 0
  	for(s <- sortedSKeys(states)){

  		fs(s) = i
  		states(s).id = i
  		i = i+1
  	}
  	i=0
  	for(e <- edges.values){

  		fe(e.id)=i
  		e.id = i
  		i=i+1
  	}
  	var newstates = new HashMap[Int,State]
  	var newedges = new HashMap[Int,Edge]
  	for(k<-fs.keys){
  		newstates(fs(k)) = states(k)
  	}
  	for(k<-fe.keys){
  		newedges(fe(k)) = edges(k)
  	}
  	states = newstates
  	edges = newedges
  }

  /* *************************************************** */
  def zeroVect(d : Int) : HashMap[Int,Int] = {
  	var rVal = new HashMap[Int,Int]
  	for(i <- 0 to d -1){
  		rVal(i) = 0
  	}
  	return rVal
  }
  /* *************************************************** */

  /* *************************************************** */
  def zeroVectD(d : Int) : HashMap[Int,Double] = {
  	var rVal = new HashMap[Int,Double]
  	for(i <- 0 to d -1){
  		rVal(i) = 0
  	}
  	return rVal
  }
  /* *************************************************** */

  /* *************************************************** */
  def add(v : HashMap[Int,Double],w : HashMap[Int,Double]) : HashMap[Int,Double] = {
  	var rVal = new HashMap[Int,Double]
  	for(i <- 0 to dim -1){
  		rVal(i) = v(i) + w(i)
  	}
  	return normalize(rVal)
  }
  /* *************************************************** */

  /* *************************************************** */
  def updateBase() = {
  	//base is b
  	b = states.size * states.size * wMax + 1
  }
  /* *************************************************** */

  /* *************************************************** */
  def normalize(v : HashMap[Int,Double]) : HashMap[Int,Double] = {
  	//base is b, sending all extra components to first one
  	if(lex_mode == 0){
  		return v
  	}
  	else{
  	var w = new HashMap[Int,Double]
  	var c = 0.0
  	for(i <- 1 to dim){
  		if(v(dim-i)+c > b){
  			var q = b*1.0* ((v(dim - i)+c)/(b*1.0)).toInt
  			w(dim - i) = v(dim-i) + c - q
  			c = q
  		}
  		else{
  			w(dim - i) = v(dim-i) + c
  			c=0
  		}
  	}
  	w(0) = w(0) + c
  	return w
  	}
  }
  /* *************************************************** */

  /* *************************************************** */
  def lex_lesser(v : HashMap[Int,Double],w : HashMap[Int,Double]) : Boolean = {
  	//base is b
  	for(i <- 0 to dim-1){
  		if(v(i) < w(i)) return true
  		if(v(i) > w(i)) return false
  	}
  	return false
  }
  /* *************************************************** */

  /* *************************************************** */
  def lesser(v : HashMap[Int,Double],w : HashMap[Int,Double]) : Boolean = {
  	//base is b
  	if(lex_mode == 1){
  		return lex_lesser(v,w)
  	}
  	else {
  	var diff = 0.0
  	for(i <- 1 to dim){
  		diff = diff/(b*1.0) + v(dim-i) - w(dim -i)
  		//if(v(i) < w(i)) return true
  		//if(v(i) > w(i)) return false
  	}
  	if(diff < 0) return true
  	else return false
  	}
  }
  /* *************************************************** */

  /* *************************************************** */
  def mult(v : HashMap[Int,Int],k : Int) : HashMap[Int,Int] = {
  	var rVal = new HashMap[Int,Int]
  	for(i <- 0 to dim -1){
  		//print(i)
  		rVal(i) = v(i) * k
  	}
  	return rVal
  }
  /* *************************************************** */

  /* *************************************************** */
  def multD(v : HashMap[Int,Double],k : Double) : HashMap[Int,Double] = {
  	var rVal = new HashMap[Int,Double]
  	for(i <- 0 to dim -1){
  		rVal(i) = v(i) * k
  	}
  	return normalize(rVal)
  }
  /* *************************************************** */

  /* *************************************************** */
  def divD(v : HashMap[Int,Double],k : Double) : HashMap[Int,Double] = {
  	var rVal = new HashMap[Int,Double]
  	for(i <- 0 to dim -1){
  		rVal(i) = v(i) / k
  	}
  	return normalize(rVal)
  }

  /* ****************************************************
  Coverting a Mean Payoff Automaton to a discounted Game
  **************************************************** */
  def auto2Game(minterms : HashMap[Int,disjunct]) : Game = {
  	//given a transition labelled LMPA(this) convert it into a dMPG
  	//assumption : state ids are 0 to n-1 (imp)
  	cleanUp
  	var G = new Game
  	var n = states.size
  	var i = 0
  	var ei =0
  	G.dim = dim
  	G.wMax = wMax
  	//ni = no. of inp vars r0,r1,...
  	
  	val v2pni = Game.pow(2,ni)
  	for(i <- 0 to v2pni-1){
  		var R = new disjunct
  		var m : Int = i
  		var ictr = 0
  		while(ictr < ni){
  			if(m%2 == 1){
  				R.pos.add(ictr)
  			}
  			else{
  				R.neg.add(ictr)
  			}
  			m= (m/2.0).toInt
  			ictr = ictr + 1
  		}
  		minterms(i) = R
  	}
  	var Rtr = new HashMap[Int,HashMap[disjunct,java.util.HashSet[Int]]]
  	var RP = new HashMap[Int,java.util.HashSet[java.util.HashSet[disjunct]]]
  	for ( t <- sortedSKeys(states)){
  		var s = states(t)
  		s.copiedID = i
  		G.states(i) = new State
                if(modeparity) G.states(i).parity = s.parity
  		G.states(i).player = 1
  		G.states(i).id = i
  		var Rpart = new HashMap[disjunct,java.util.HashSet[Int]]
  		for(i <- 0 to v2pni-1){
  			Rpart(minterms(i)) = new java.util.HashSet[Int]
  		}
  		for(e <- s.outgoing.values){
  			var R = new disjunct
  			R.pos.addAll(e.Rpos)
  			R.neg.addAll(e.Rneg) 
  			//check if R is implied by any of the minterms
  			//here transition for R will be added to that minterm's mapped set
  			for(i <- 0 to v2pni-1){
  				if(minterms(i).implies(R)){
  					Rpart(minterms(i)).add(e.id)
  				}
  			}
		}
		//println("936 !")
		//for each key of Rpart look for it being equal to one of the already existing set representatives' mapping through Rpart in Rsets
		var Rsets = new java.util.HashSet[java.util.HashSet[disjunct]]
		var dbg = 0
		for(R <- Rpart.keys){
			//println(dbg)
			dbg = dbg + 1
			var itr = Rsets.iterator
			var added = false
			var RTset = Rpart(R)
			while(itr.hasNext()){
				if(!added){
					var Rset = itr.next
					var itr2 = Rset.iterator
					var Tset = Rpart(itr2.next)
					if(RTset.equals(Tset)){
						Rset.add(R)
						added=true
					}
				}
				else {
					itr.next
				}
			}
			if(!added){
				var Rset = new java.util.HashSet[disjunct]
				Rset.add(R)
				Rsets.add(Rset)
			}
		}
		//println("960 !")
  		Rtr(i) = Rpart
  		RP(i) = Rsets
  		i = i + 1
  	}
  	//println("965 !")
  	//RP(s.id) has partition of set of distinct R-minterms for which G-disjuctions can be obtained using set of T-ids stored in Rtr
  	//constructing new P0 states using this data
  	//printAutomaton
  	var continue = 0;
  	var contin = 0;
  	var splTr = new java.util.HashSet[State]
  	for(s <- states.values){
  		var sitr = RP(s.copiedID).iterator
  		while(sitr.hasNext()){
  			contin = 0;
  			if(continue==0){
  				var SD = sitr.next
  				var itr = SD.iterator
  				var R = itr.next
  				var TS = Rtr(s.copiedID)(R) //set of all transition ids of original automaton for G-Transitions from st
  				if(TS.isEmpty){
  					//splTr.add(st)
  					if(mode_MDP==1) contin = 1;
  				}
  				if(contin == 0){
  				var st = new State
  				st.player = 0
  				G.states(i) = st
                                if(modeparity) G.states(i).parity = s.parity
  				st.id = i
  				if(TS.isEmpty){
  					splTr.add(st)
  				}
  				var itr2 = TS.iterator
  				while(itr2.hasNext()){
  					var tid = itr2.next
  					var e = new Edge
  					e.from = st
  					/*print("A Problem : " +tid)
  					println( " , " +edges(tid).to.copiedID)*/
  					e.to = G.states(edges(tid).to.copiedID)
  					e.TypeOfEdge = 0
  					e.pos = TOLIST(edges(tid).Gpos)
  					e.neg = TOLIST(edges(tid).Gneg)
  					e.dweight = edges(tid).dweight
  					e.setLabel
  					G.edges(ei) = e
  					e.id = ei
  					st.addOutgoingEdge(e)
  					G.states(edges(tid).to.copiedID).addIncomingEdge(e)
  					ei = ei +1
  				}
  				 itr = SD.iterator
  				while(itr.hasNext()){
  					var R = itr.next
                    	            var minIndex = R.TOINT
  					var e = new Edge
                    	            if(s.pDistr.isDefinedAt(minIndex)){
                    	                e.prob = s.pDistr(minIndex)
                    	            }
  					e.from = G.states(s.copiedID)
  					e.to = st
  					e.TypeOfEdge = 1
  					e.pos = TOLIST(R.pos)
  					e.neg = TOLIST(R.neg)
  					e.dweight = zeroVect(dim)
  					//println(1058)
  					e.setLabel
  					//println(1060)
  					G.edges(ei) = e
  					e.id = ei
  					G.states(s.copiedID).addOutgoingEdge(e)
  					st.addIncomingEdge(e)
  						ei = ei +1
  				}
  				
  				i=i+1
  				}
  				}
  			}	
  		}	
  		//speacial Treatment for P0 states with no outgoing edges
  		if(mode_MDP != 1 && !(splTr.isEmpty())){
  		  	var s0 = new State
  			s0.player = 0
  			G.states(i) = s0
                        if(modeparity) G.states(i).parity = 1 //any odd parity -- stuck in odd parity
  			s0.id = i
  			i = i + 1
  			var s1 = new State
  			G.states(i) = s1
                        if(modeparity) G.states(i).parity = 1
  			s1.id = i
  			s1.player = 1
  			if(mode_MDP==1){
  				s1.pDistr = G.states(0).pDistr
  				s0.pDistr = G.states(0).pDistr
  				//println("BPP");
  			}
  			i = i + 1
  			var e = new Edge
  			e.from = s0
  			e.to = s1
  			e.TypeOfEdge = 0
  			e.dweight = zeroVect(dim)
  			e.setLabel
  			e.prob = 1.0
  			G.edges(ei) = e
  			e.id = ei
  			s0.addOutgoingEdge(e)
  			s1.addIncomingEdge(e)
  			ei = ei +1
  			//another one
  			e = new Edge
  			e.from = s1
  			e.to = s0
  			e.TypeOfEdge = 1
  			e.dweight = zeroVect(dim)
  			e.setLabel
  			e.prob = 1.0
  			G.edges(ei) = e
  			e.id = ei
  			s1.addOutgoingEdge(e)
  			s0.addIncomingEdge(e)
  			ei = ei +1
			var STitr = splTr.iterator
			while(STitr.hasNext()){
				e = new Edge
  				e.from = STitr.next
  				e.to = s1
  				e.TypeOfEdge = 1
  				e.dweight = zeroVect(dim)
  				e.setLabel
  				e.prob = 1.0
  					G.edges(ei) = e
  				e.id = ei
  				e.from.addOutgoingEdge(e)
  				s1.addIncomingEdge(e)
  				ei = ei +1
			}
		}
		if(mode_MDP==1){
			var STitr = splTr.iterator
			while(STitr.hasNext()){
				var S = STitr.next
  				S.useless =1;
		}
	}
	
  	return G
  }
}

object Game {
  //auxillary functions
  def pow(n: Int, m: Int): Int = {
    def _pow(m: Int, acc: Int): Int  = m match {
        case 0 => acc
        case _ => _pow(m - 1, acc * n)
    }
     _pow(m, 1)
  }

  def Prod(A : Game, B : Game) : Game = { //product of two 1-D mean payoff specifications using addition of weights
  	var m = A.states.size
  	var n = B.states.size
  	var k = m*n
  	var C = new Game
  	for(i <- 0 to m-1){
  		for(j <- 0 to n-1){
  			C.states(m*j + i) = new State
  			C.states(m*j + i).id = m*j + i
  			C.states(m*j + i).ti = i
  			C.states(m*j + i).tj = j
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = 1
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id 
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]() 
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]() 
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]() 
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]() 
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos) 
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			if(intR.isEmpty() && intG.isEmpty() ){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.from = C.states(m*j+i)
  				e.to = C.states(m*l + k)
  				e.weight = eA.dweight(0) + eB.dweight(0)
  				e.dweight(0) = e.weight
  				if(C.wMax < e.weight){
  					C.wMax = e.weight
  				}
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				var wStr = ""
  				wStr = "w" + e.weight.toString
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				} 	
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}	
  				e.label = e.label + wStr	
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  		}
  	}
  	return C
  	
  }
  def sortedUKeys(map: Map[Int, Int]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
  def ProdMult(A : Game, B : Game) : Game = { //product of two mean payoff specifications using multiplication of weights
  // Assumption : dim(B) = 1
  	var m = A.states.size
  	var n = B.states.size
  	var k = m*n
  	var C = new Game
  	for(i <- 0 to m-1){
  		for(j <- 0 to n-1){
  			C.states(m*j + i) = new State
  			C.states(m*j + i).id = m*j + i
  			C.states(m*j + i).ti = i
  			C.states(m*j + i).tj = j
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = A.dim
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id 
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]() 
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]() 
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]() 
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]() 
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos) 
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			if(intR.isEmpty() && intG.isEmpty() ){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.from = C.states(m*j+i)
  				e.to = C.states(m*l + k)
  				//e.weight = eA.weight + eB.weight
  				//multiply a vector with a scalar
  				var wStr = ""
  				for ( i <- sortedUKeys(eA.dweight)){
  					e.dweight(i) = eA.dweight(i) * eB.dweight(0)
  					wStr = wStr + "v" + e.dweight(i)
  					if(C.wMax < e.dweight(i)){
  						C.wMax = e.dweight(i)
  					}
  				
  				}
  				wStr = "w" + wStr.substring(1,wStr.length)
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				} 	
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}	
  				e.label = e.label + wStr	
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  		}
  	}
  	return C
  	
  }
  def ProdMult2(A : Game, B : Game) : Game = { //product of one Lex mean payoff specification and 1 safety auto using multiplication of weights
  // Assumption : dim(B) = 1
  	var m = A.states.size
  	var n = B.states.size
  	var k = m*n
  	var C = new Game
  	for(i <- 0 to m-1){
  		for(j <- 0 to n-1){
  			C.states(m*j + i) = new State
  			C.states(m*j + i).id = m*j + i
  			C.states(m*j + i).ti = i
  			C.states(m*j + i).tj = j
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = A.dim
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id 
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]() 
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]() 
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]() 
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]() 
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos) 
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			if(intR.isEmpty() && intG.isEmpty() ){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.from = C.states(m*j+i)
  				e.to = C.states(m*l + k)
  				//e.weight = eA.weight + eB.weight
  				//multiply a vector with a scalar
  				var wStr = ""
  				for ( i <- sortedUKeys(eA.dweight)){
  					e.dweight(i) = eA.dweight(i) * eB.dweight(0)
  					wStr = wStr + "v" + e.dweight(i)
  					if(C.wMax < e.dweight(i)){
  						C.wMax = e.dweight(i)
  					}
  				}
  				wStr = "w" + wStr.substring(1,wStr.length)
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				e.label = ""
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				} 	
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}	
  				e.label = e.label + wStr	
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  		}
  	}
  	return C
  	
  }
  def ProdMultMDP(A : Game, B : Game, fname : String) : Game = { //product of one Lex mean payoff specification and 1 safety auto using multiplication of weights
  // Assumption : dim(B) = 1
  	var m = A.states.size
  	//println("m : " + m)
  	var n = B.states.size
  	var k = m*n
  	var C = new Game
        C.ni = max(A.ni,B.ni)
        var st_no : Int = 0
        for ((line) <- Source.fromFile(fname).getLines) {
            var labels = line.split(' ')
            var firstdone = 0
            var CTR: Int = 0
            for(l <- labels){
                if(firstdone==0){
                    firstdone =1
                    st_no = l.toInt
                }
                else{
                    //println("BWAH : " + st_no + " HAHA : "+CTR)
                    A.states(st_no).pDistr(CTR) = l.toDouble
                    CTR = CTR + 1
                }
            }
        }
        var CTR = pow(2,C.ni)
  	for(i <- 0 to m-1){
                if(A.states(i).pDistr.isEmpty){
                    //println("Empty : "+i)
                    for(mi <- 0 to CTR){
                        A.states(i).pDistr(mi) = 1.0/CTR
                    }
                }
                else{
                    for(mi <- 0 to CTR){
                        if(!(A.states(i).pDistr.isDefinedAt(mi))){
                            A.states(i).pDistr(mi) = 0.0
                        }
                    }
                }
  		for(j <- 0 to n-1){
  			C.states(m*j + i) = new State
  			C.states(m*j + i).id = m*j + i
  			C.states(m*j + i).ti = i
  			C.states(m*j + i).tj = j
                        C.states(m*j + i).pDistr = A.states(i).pDistr
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = A.dim
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]()
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]()
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]()
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]()
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos)
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			if(intR.isEmpty() && intG.isEmpty() ){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.from = C.states(m*j+i)
  				e.to = C.states(m*l + k)
  				//e.weight = eA.weight + eB.weight
  				//multiply a vector with a scalar
  				var wStr = ""
  				for ( i <- sortedUKeys(eA.dweight)){
  					e.dweight(i) = eA.dweight(i) * eB.dweight(0)
  					wStr = wStr + "v" + e.dweight(i)
  					if(C.wMax < e.dweight(i)){
  						C.wMax = e.dweight(i)
  					}
  				}
  				wStr = "w" + wStr.substring(1,wStr.length)
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				e.label = ""
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				}
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}
  				e.label = e.label + wStr
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  		}
  	}
  	return C

  }


  def ProdMultMDPP(A : Game, B : Game, fname : String) : Game = { //product of one Lex mean payoff specification and 1 safety auto using multiplication of weights
  // Assumption : dim(B) = 1
  	assert(B.modeparity)
        var m = A.states.size
  	//println("m : " + m)
  	var n = B.states.size
  	var k = m*n
  	var C = new Game
        C.ni = max(A.ni,B.ni)
        C.modeparity = true
        var st_no : Int = 0
        for ((line) <- Source.fromFile(fname).getLines) {
            var labels = line.split(' ')
            var firstdone = 0
            var CTR: Int = 0
            for(l <- labels){
                if(firstdone==0){
                    firstdone =1
                    st_no = l.toInt
                }
                else{
                    A.states(st_no).pDistr(CTR) = l.toDouble
                    CTR = CTR + 1
                }
            }
        }
        var CTR = pow(2,C.ni)
  	for(i <- 0 to m-1){
                if(A.states(i).pDistr.isEmpty){
                    //println("Empty : "+i)
                    for(mi <- 0 to CTR){
                        A.states(i).pDistr(mi) = 1.0/CTR
                    }
                }
                else{
                    for(mi <- 0 to CTR){
                        if(!(A.states(i).pDistr.isDefinedAt(mi))){
                            A.states(i).pDistr(mi) = 0.0
                        }
                    }
                }
  		for(j <- 0 to n-1){
  			C.states(m*j + i) = new State
  			C.states(m*j + i).id = m*j + i
  			C.states(m*j + i).ti = i
  			C.states(m*j + i).tj = j
                        C.states(m*j + i).pDistr = A.states(i).pDistr
                        C.states(m*j + i).parity = B.states(j).parity
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = A.dim
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]()
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]()
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]()
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]()
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos)
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			if(intR.isEmpty() && intG.isEmpty() ){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.from = C.states(m*j+i)
  				e.to = C.states(m*l + k)
  				//e.weight = eA.weight + eB.weight
  				//multiply a vector with a scalar
  				var wStr = ""
  				for ( i <- sortedUKeys(eA.dweight)){
  					e.dweight(i) = eA.dweight(i) * eB.dweight(0)
  					wStr = wStr + "v" + e.dweight(i)
  					if(C.wMax < e.dweight(i)){
  						C.wMax = e.dweight(i)
  					}
  				}
  				wStr = "w" + wStr.substring(1,wStr.length)
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				e.label = ""
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				}
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}
  				e.label = e.label + wStr
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  		}
  	}
  	return C

  }

  def ProdAppend(A : Game, B : Game) : Game = { //product of two lexicographic mean payoff specifications
  	var m = A.states.size
  	var n = B.states.size
  	var k = m*n
  	var C = new Game
  	for(i <- 0 to m-1){
  		for(j <- 0 to n-1){
  			C.states(m*j + i) = new State
  			C.states(m*j + i).id = m*j + i
  			C.states(m*j + i).ti = i
  			C.states(m*j + i).tj = j
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = A.dim + B.dim
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id 
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]() 
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]() 
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]() 
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]() 
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos) 
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			if(intR.isEmpty() && intG.isEmpty() ){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.from = C.states(m*j+i)
  				e.to = C.states(m*l + k)
  				//e.weight = eA.weight + eB.weight
  				//calculate weights later from lexicograpic weights
  				/*if(C.wMax < e.weight){
  					C.wMax = e.weight
  				}*/
  				//append the dweights
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				//set d dim weight for this new edge
  				var ct = 0
  				var wStr = ""
  				for ( i <- eA.dweight.values){
  					e.dweight(ct) = i
  					ct += 1
  					wStr = wStr + "v" + i 
  				}
  				for ( i <- eB.dweight.values){
  					e.dweight(ct) = i
  					ct += 1
  					wStr = wStr + "v" + i
  				}
  				wStr = "w" + wStr.substring(1,wStr.length)
  				var wts = wStr.substring(1,wStr.length).split('v')
	  			var tr = 0
	  			for ( w1 <- wts){
	  				tr = tr + 1
	  				var test = w1.toInt
	  				e.dweight(tr) = test
	  				if(test > 0 && test > C.wMax){ C.wMax = test }
	  				if(test < 0 && (-1 * test) > C.wMax){ C.wMax = -1*test }
	  			}
	  			if(C.dim != tr) println("error line 1020\n")
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				} 	
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}	
  				e.label = e.label + wStr	
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  		}
  	}
  	return C
  	
  }
  
  //product of a Mean Payoff specification and a safety automaton
  def ProdSafety(A : Game, B : Game) : Game = { //B as a deterministic safety automaton
  //safety automaton : 1 D LMPA with labels in {0,1} and after seeing a 0-edge no more 1 edges can be seen...
  //incorporating safety conditions : assigning -1 to the word which is rejected by safety automaton annd others > 0 and then adding 1 to each of them
  //Assume A also has weights in range 0 to W (integers) : LMPA
  	var m = A.states.size
  	var n = B.states.size
  	//assume special vertex of B (unsafe vertex) is n-1
  	var C = new Game
  	for(i <- 0 to m-1){
  		for(j <- 0 to n-1){
  			if(j!=n-1 || i == 0){
  			C.states(j*m + i) = new State
  			C.states(j*m + i).id = j*m + i
  			C.states(j*m + i).ti = i
  			C.states(j*m + i).tj = j
  			}
  		}
  	}
  	var ctrid =0
  	C.wMax = 0
  	C.dim = A.dim
  	for(eA <- A.edges.values){
  		for(eB <- B.edges.values){
  			var i = eA.from.id 
  			var k = eA.to.id
  			var j = eB.from.id
  			var l = eB.to.id
  			// i-> k & j -> l are edges in A and B resp.
  			//To decide if there should be an adge from (i,j) -> (k,l)
  			var Rpos  = new java.util.HashSet[Int]() 
  			Rpos.addAll(eB.Rpos)
  			Rpos.addAll(eA.Rpos)
  			var Rneg = new java.util.HashSet[Int]() 
  			Rneg.addAll(eB.Rneg)
  			Rneg.addAll(eA.Rneg)
  			var Gpos  = new java.util.HashSet[Int]() 
  			Gpos.addAll(eB.Gpos)
  			Gpos.addAll(eA.Gpos)
  			var Gneg = new java.util.HashSet[Int]() 
  			Gneg.addAll(eB.Gneg)
  			Gneg.addAll(eA.Gneg)
  			var intR = new java.util.HashSet[Int]()
  			intR.addAll(Rpos) 
  			intR.retainAll(Rneg)
  			var intG = new java.util.HashSet[Int]()
  			intG.addAll(Gpos)
  			intG.retainAll(Gneg)
  			//println("hello : "+ i+ ","+j+","+ k+ ","+l+","+m+","+n)
  			if(j==l && l == (n-1)){
  			}
  			else{
  			if(intR.isEmpty() && intG.isEmpty()){
  				//println("Accepted")
  				var e = new Edge
  				e.id =ctrid
  				e.dweight = eA.dweight
  				e.from = C.states(m*j + i)
  				if(l!=n-1){
  				e.to = C.states(m*l + k)
  				//println(ctrid + " " + eA.weight +" " + eB.weight)
  				e.weight = eA.weight + eB.weight
  				}
  				else{
  				e.to = C.states(m*l + 0)
  				e.weight = 0	
  				}
  				if(C.wMax < e.weight){
  					C.wMax = e.weight
  				}
  				e.Rpos = Rpos
  				e.Rneg = Rneg
  				e.Gpos = Gpos
  				e.Gneg = Gneg
  				//set d dim weight for this new edge
  				var ct = 0
  				var wStr = "w" + e.weight.toString
  				//set e.label here
  				var itr = e.Rpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "r" + itr.next + " "
  				}
  				itr = e.Rneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~r" + itr.next + " "
  				} 	
  				itr = e.Gpos.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "g" + itr.next + " "
  				}
  				itr = e.Gneg.iterator()
  				while(itr.hasNext()){
  					e.label = e.label + "~g" + itr.next + " "
  				}	
  				e.label = e.label + wStr	
  				C.edges(ctrid) = e
  				C.states(e.from.id).outgoing(e.id) = e
  				C.states(e.to.id).incoming(e.id) = e
  				ctrid += 1
  			}
  			}
  		}
  	}
  	var e = new Edge
  	e.id =ctrid
  	e.from = C.states(m*(n-1))
  	e.to = C.states(m*(n-1))
  	e.weight = 0
  	e.label="w0"
  	C.edges(ctrid) = e
  	C.states(e.from.id).outgoing(e.id) = e
  	C.states(e.to.id).incoming(e.id) = e
  	ctrid += 1
  	//C.updateWeights()
  	return C
  	
  }

}

}
