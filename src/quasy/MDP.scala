import scala.xml._
import scala.collection.mutable._
import scala.io.Source
import java.util.Arrays._
package quasy {

/*********************************************
 * MDP
 *********************************************/
class MDP {
    var modeparity = false
    var G = new Game //Underlying States and Edges in the form of game
    var EPSILON = 1e-10 //to avoid precision errors A>B is taken as A>=B+epsilon
    //sorting keys of hashMaps
    def sortedAKeys(map: Map[Int, Action]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
    def sortedSKeys(map: Map[Int, State]) = map.keys.toList.sortWith((e1,e2) => (e1 < e2))
    def printActs() = {
        var n : Int = G.states.size
        print("( ")
        for(i <- 0 to n-1){
           // print(G.states(i).selAct + " ")
           G.states(i).actions(G.states(i).selAct).printAct
        }
        println(")")
    } //prints selected action's IDs'
    def printAllActs() = {
        var n : Int = G.states.size
        for(i <- 0 to n-1){
            println(i + ":")
            for(a <- G.states(i).actions.values){
                a.printAct
            }
        }
        println()
    } //pritns complete action descriptions
    def pMatrix() : Array[Array[Double]] = {
        var n : Int= G.states.size
        var P = Array.ofDim[Double](n, n)
        for(i<- 0 to n-1){
            for(j<- 0 to n-1){
                P(i)(j) = 0.0
            }
        }
        for(i<- 0 to n-1){
            val act = G.states(i).actions(G.states(i).selAct)
            for(s <- act.distr.keys){
                P(i)(s.id) = act.distr(s)
            }
        }
        return P
    } //Returns Probability
    //Transition Matrix for Current selection of actions
    def rVector() : Array[Double] = {
        var n : Int= G.states.size
        var r = new Array[Double](n)
        for(i<- 0 to n-1){
            r(i)= G.states(i).actions(G.states(i).selAct).weight
        }
        return r
    }//reward Vector for current selection
    def isGood(a : Action,phi : Array[Double],u0 : Array[Double]) : Boolean ={
        //a must not be the one selected
        var s = a.pState
        var sum : Double = 0.0
        for(t <- a.distr.keys){
            sum = sum + a.distr(t) * phi(t.id)
        }
        if(sum > phi(s.id)) return true
        if((- sum + phi(s.id))> EPSILON )  return false
        sum = 0.0
        for(t <- a.distr.keys){
            sum = sum + a.distr(t) * u0(t.id)
        }
        sum = sum + a.weight
        if(sum > phi(s.id) + u0(s.id)) return true
        return false
    }
    //Returns true is a given action is a candidate for improvement of current 
    //strategy
    def getDiff1 (a : Action,phi : Array[Double],u0 : Array[Double]) : Double ={
        var s = a.pState
        var sum : Double = 0.0
        for(t <- a.distr.keys){
            sum = sum + a.distr(t) * phi(t.id)
        }
        return (sum - phi(s.id))
    }
    //returns d1 as explained in last section
    def getDiff2 (a : Action,phi : Array[Double],u0 : Array[Double]) : Double ={
        var s = a.pState
        var sum : Double = 0.0
        for(t <- a.distr.keys){
            sum = sum + a.distr(t) * u0(t.id)
        }
        sum = sum + a.weight
        return (sum -( phi(s.id) + u0(s.id)))
    }
    //returns d2 as explained in last section
    def strategize() = {
      var n : Int= G.states.size
      for(i<- 0 to n-1){
                if(G.states(i).useless == 0 && G.states(i).player == 0){
                    for(a <- G.states(i).actions.values){
                        if(a.id != G.states(i).selAct){
                            G.removeEdge(a.edge)
                        }
                    }
                }
        }
    }

    def policyIteration()={
        val GE = new GaussianElimination()
        var n : Int= G.states.size
        var break =0
        while(break != 1){
            
            var P = pMatrix()
            var r = rVector()
            var x : Array[Double] = GE.Solve(P,r,n)
            var phi : Array[Double] = new Array[Double](n)
            var u0 : Array[Double] = new Array[Double](n)
            for(i <- 0 to n-1) phi(i) = x(i)
            for(i <- 0 to n-1) u0(i) = x(i+n)
            var foundAct = false
            var innerBreak = 0
            var outerBreak = 1
            var d1 = 0.0
            var d2 = 0.0
            for(i<- 0 to n-1){
                if(G.states(i).useless == 0 && G.states(i).player == 0){
                    var bestAct : Int = 0
                    var bestDiff : Double = 0
                    for(a<-G.states(i).actions.values){
                        if(a.id != G.states(i).selAct){
                            d1 = getDiff1(a,phi,u0)
                            //println("DBG : "+ (d1 - bestDiff) + " EPSILON :" + EPSILON + " BOOL : " + (d1 - bestDiff > EPSILON))
                            if(d1 - bestDiff > EPSILON){
                                innerBreak = 1
                                //print("HERE ; d1 = "+ d1 +"; ")
                                bestAct = a.id
                                bestDiff = d1
                            }
                        }
                    }
                    if(innerBreak == 0) {
                        var bestAct : Int = 0
                        var bestDiff : Double = 0
                        for(a<-G.states(i).actions.values){
                            if(a.id != G.states(i).selAct){
                                d1 = getDiff1(a,phi,u0)
                                if (d1 < EPSILON && d1 > -EPSILON){
                                    var d2 = getDiff2(a,phi,u0)
                                    if(d2 - bestDiff > EPSILON){
                                        innerBreak = 1
                                        //print("THERE ; d1 = " + d1 + ", d2 = " + d2 + "; ")
                                        bestAct = a.id
                                        bestDiff = d2
                                    }
                                }
                            }
                       }
                       if(innerBreak == 1){
                           
                               //print("THERE ; d1 = " + d1 + ", d2 = " + d2 + "; ")
                               //println(i + " : " + G.states(i).selAct + " -> " + bestAct)
                           G.states(i).selAct= bestAct
                       }else{
                           //print("HERE ; d1 = "+ d1 +"; ")
                           //println(i + " : " + G.states(i).selAct)
                       }
                    }
                    else{
                        //println(i + " : " + G.states(i).selAct + " -> " + bestAct)
                        G.states(i).selAct= bestAct
                    }
                    if(innerBreak == 1) outerBreak =0
                    innerBreak = 0
                }
            }
            if(outerBreak == 1) break = 1
            
        }
        //printActs()
        //remove actions which are not selected
        println("Values :")
        var P = pMatrix()
        var r = rVector()
      //  println("HOO :")
        var x : Array[Double] = GE.Solve(P,r,n)
     //   println("LALA :")
        for(i <- 0 to n-1) println("State " + i + " has value : " + x(i))
        //strategize()
        
    }
    //policy Iteration Algorithm as explained in last section
    def setActions = {
        //set actions for the game graph
        for(s <- G.states.values){
            if(s.player == 0){
                //max with deterministic transitions
                var ctr : Int = 0
                for(e <- s.outgoing.values){
                    var I : Int = 0; 
                    /*while((I < ctr)){
                    	if(s.actions(I).distr.isDefinedAt(e.to)){
                    		neglect = 1;
                    	}
                    	I = I +1
                    }*/
                    s.actions(ctr) = new Action
                    s.actions(ctr).pState = s
                    s.actions(ctr).weight = e.weight
                    s.actions(ctr).distr(e.to) = 1.0
                    s.actions(ctr).id = ctr
                    s.actions(ctr).edge = e
                    ctr = ctr + 1
                    
                }
            }
            else if(s.player == 1){
                //min with only one action with all probabilistic transitions
                s.actions(0) = new Action
                s.actions(0).pState = s
                s.actions(0).weight = 0
                s.actions(0).id = 0
                //s.actions(ctr).distr(e.to) = 1.0
                for(e <- s.outgoing.values){
                    if(s.actions(0).distr.isDefinedAt(e.to)){
                        s.actions(0).distr(e.to) = s.actions(0).distr(e.to) + e.prob
                    }
                    else {
                        s.actions(0).distr(e.to) = e.prob
                    }
                }
            }
        }
    }
    //intialize MDP by setting actions in states using the game structure
  def setParityActs() : Int = {
    //look at the MDP as a graph and find an edge closing to some min-parity(=0) state
    //for each state and then choose actions corresponding to this edge
    var q = new Queue[Int]()
    //find a state with 0 parity
    for(s <- G.states.values){
      if(s.parity == 0 && s.player == 1){
        q.enqueue(s.id)
      }
    }
    //reverse BFS
   /*  for(s<-G.states.values){
      s.selAct = 0
    } */
    
    while(!q.isEmpty){
      var tp : Int = q.dequeue()
      //look at all incoming edges to this state
      //add all predecessors to the queue which are not marked
      //also select the corresponding action to the edge being considered (if player == 0)
      G.states(tp).DFSmark = true
      for(e <- G.states(tp).incoming.values){
        var pre = e.from.id
        if(!G.states(pre).DFSmark){
          //G.states(pre).DFSmark = true
          q.enqueue(pre)
          if(G.states(pre).player == 0){
            var maxReward = -1
            var bestAct = -1
            for(a <- sortedAKeys(G.states(pre).actions)){
              if(G.states(pre).actions(a).edge.to.id == tp && G.states(pre).actions(a).edge.weight > maxReward){
                bestAct = a
                maxReward = G.states(pre).actions(a).edge.weight
              }
            }
            G.states(pre).selAct = bestAct
          }
        }
      }
      /* if(tp != start && G.states(G.states(tp).DFSparent).player == 0){
        var par = G.states(tp).DFSparent
        for(a <- sortedAKeys(G.states(par).actions)){
          if(G.states(par).actions(a).edge.to.id == tp) G.states(par).selAct = a
        }
      }
      if(G.states(tp).parity == 0) dne = true
      else{
        for(e <- G.states(tp).outgoing.values){
          if(!e.to.DFSmark){
            e.to.DFSparent = tp
            e.to.DFSmark = true
            stk.push(e.to.id)
          }
        }
      } */
    }
    return 1
  }
    /********************************************************/
  def exportMDP(filename : String) = {
    var f = new java.io.File(filename)
    var out_file = new java.io.FileOutputStream(f)
    var os = new java.io.PrintStream(out_file)
    var states = G.states
    for (s <- sortedSKeys(states)) {
     
      os.print("STATE\t"+ s +"\t-1\t"+ states(s).parity +"\t-1\n")
      for(a <- sortedAKeys(states(s).actions)){
        os.print("\tACTION\t"+a+"\t-1\n")
        os.print(states(s).actions(a).stringAct)
      }
    }
    os.close
  }

}

}
