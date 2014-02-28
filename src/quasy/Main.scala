import scala.xml._
import scala.collection.mutable._
import scala.io.Source 
import java.util.Arrays._
import scala.actors._
import scala.actors.Actor._

package quasy {

object Main {

  //auxiliary function
  def max(a : Int, b: Int) : Int = {
  	if(a < b) return b
  	else return a
  }

  private val caller = self
    private val WAIT_TIME = 20000000

    private val reader = actor {
        println("created actor: " + Thread.currentThread)
        var continue = true
        loopWhile(continue){
            reactWithin(WAIT_TIME) {
                case TIMEOUT =>
                    caller ! "react timeout"
                case proc:Process =>
                    println("entering first actor " + Thread.currentThread)
                    val streamReader = new java.io.InputStreamReader(proc.getInputStream)
                    val bufferedReader = new java.io.BufferedReader(streamReader)
                    val stringBuilder = new java.lang.StringBuilder()
                    var line:String = null
                    while({line = bufferedReader.readLine; line != null}){
                        println(line)
                        //stringBuilder.append(line)
                        //stringBuilder.append("\n")
                    }
                    bufferedReader.close
                    caller ! stringBuilder.toString
            }
        }
    }

    def run(command:String){
        println("gonna runa a command: " + Thread.currentThread)
        val args = command.split(" ")
        val processBuilder = new ProcessBuilder(args: _* )
        processBuilder.redirectErrorStream(true)
        val proc = processBuilder.start()

        //Send the proc to the actor, to extract the console output.
        reader ! proc

        //Receive the console output from the actor.
        receiveWithin(WAIT_TIME) {
                case TIMEOUT => println("receiving Timeout")
                case result:String => println(result)
        }
        println("--- Done with the command---")
    }

  def printHelp(long: Boolean) {
    if (long) {
      for {  
	(line) <- Source.fromFile("README").getLines  
      } println(line) 
    } else {
      println("""Usage: scala quasy.Main <mode> <options>
       scala quasy.Main help
       scala quasy.Main solveLMPGc LMPA_file  SA_file output_folder
       scala quasy.Main solveMPG   MPA_file   SA_file output_folder
       scala quasy.Main solveLMPGl LMPA_file  SA_file output_folder
       scala quasy.Main solveDPG   LMPA_file  SA_file lambda output_folder
       scala quasy.Main solveMDP   MPA_file   SA_file prob_file output_folder
       scala quasy.Main prodADD    LMPA_file1 LMPA_file2 output_file
       scala quasy.Main prodAPPEND LMPA_file1 LMPA_file2 output_file
       scala quasy.Main prodMULT   LMPA_file1 LMPA_file2 output_file
       scala quasy.Main solveMDPP   LMPA_file  PA_file prob_file output_folder""")
    }
  }

  def main(args : Array[String]) {
    if(args.size == 0) {
      printHelp(false)
      System.exit(1)
    }

    val mode = args(0)
    if (mode == "help") {
      printHelp(true)
      System.exit(1)
    }

    if (args.size < 4) { //all modes need at least 3 parameters
      printHelp(false)
      System.exit(1)
    }
    var file1 = args(1)
    var file2 = args(2)
    var minterms = new HashMap[Int,disjunct]
    var A1 = new Game
    A1.buildautomaton(file1) 
    // println("Automaton with weights")
    // A1.printAutomaton
    var A2 = new Game
    if (mode == "solveMDPP" || mode == "solveMDPPext") A2.modeparity = true
    A2.buildautomaton(file2)
    // println("Automaton with safety or parity condition")
    // A2.printAutomaton

//System.exit(1)
    
    if(mode == "solveLMPGc" || mode == "solveLMPGl") {//from specification as one LMPA and one safety Automaton
	// mode file1 file2 outputFolder
   	var B = Game.ProdMult2(A1,A2)
   	B.ni = max(A1.ni,A2.ni)
        var outFolder = args(3)
   	Runtime.getRuntime().exec("mkdir " + outFolder)
    	B.reduceAutomaton //incorporated the zero weight paradigm
    	B.cleanUp
    	B.check
    	B.exportAutomaton("./"+outFolder+"/Prod.gff")
    	var g = B.auto2Game(minterms)
    	if(mode == "solveLMPGl") g.lex_mode = 1
    	g.b = g.states.size * g.states.size * g.wMax + 1
    	g.L =1
	g.exportGame("./" + outFolder + "/Game.gff")
    	g.valueIteration(0)
    	g.printValues1D
    	g.optimalStrategyL(0)
    	g.exportGame("./" + outFolder + "/OptimalStrategy.gff")
    	var G1 = g.buildMealyMachine()
    	G1.exportMachine
    	var B1 = new Game
    	B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
      System.exit(0)
    }

    if(mode == "solveLMPGr" || mode == "solveMPG"){//from specification as one LMPA and one safety Automaton
	// mode file1 file2 outputFolder
   	var B = Game.ProdMult2(A1,A2)
   	B.ni = max(A1.ni,A2.ni)
   	var outFolder = args(3)
   	Runtime.getRuntime().exec("mkdir " + outFolder)
    	B.reduceAutomaton //incorporated the zero weight paradigm
    	B.cleanUp
    	B.check
    	B.exportAutomaton("./"+outFolder+"/Prod.gff")
    	var g = B.auto2Game(minterms)
    	g.updateWeights
    	g.b = g.states.size * g.states.size * g.wMax + 1
    	g.redmpg_mode = 1
    	g.L =1
	g.exportGame("./" + outFolder + "/Game.gff")
    	g.valueIteration2(0)
    	g.printValues1D
    	g.optimalStrategy2(0)
    	g.exportGame("./" + outFolder + "/OptimalStrategy.gff")
    	var G1 = g.buildMealyMachine()
    	G1.exportMachine
    	var B1 = new Game
    	B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
      System.exit(1)
    }
    
    if((mode == "solveMDPP" || mode == "solveMDPPext") && (args.size > 4)){//from specification as one LMPA,one safety Automaton and
        //one distribution for each state of LMPA
	// mode file1 file2 file-distr outputFolder
        var file_distr = args(3)
   	var B = Game.ProdMultMDPP(A1,A2,file_distr)
   	B.ni = max(A1.ni,A2.ni)
   	var outFolder = args(4)
   	Runtime.getRuntime().exec("mkdir " + outFolder)
    	B.reduceAutomaton //incorporated the zero weight paradigm
    	B.cleanUp
    	B.check
        println("Prod : "+B.states.size)
    	B.exportAutomaton("./"+outFolder+"/Prod.gff")
    	B.mode_MDP = 1;
    	var g = B.auto2Game(minterms)
    	g.updateWeights
    	g.b = g.states.size * g.states.size * g.wMax + 1
    	g.mode_MDP = 1
    	g.L =1
	g.exportGame("./" + outFolder + "/Game.gff")
        var M = new MDP
        M.modeparity = true
        M.G = g
        M.setActions
        M.exportMDP("./" + outFolder + "MDP.rff")
        println("MDP : " +g.states.size)
        if(mode=="solveMDPPext"){
          //use external program to solve MP mdp and take input from that file to decide selActs
          run("./mdpsolver/mdp ./" + outFolder+"MDP.rff ./"+outFolder+"MDPsoln.rff")
          var fnm = "./"+outFolder+"MDPsoln.rff"
          for ((line) <- Source.fromFile(fnm).getLines) {
            val labels = line.split(' ')
	    val src = labels.head.toInt
	    val dst = labels.tail.head.toInt
	    M.G.states(src).selAct = dst
          }
        }
        else{
          M.policyIteration() 
        }
        
        M.G.exportStrategy("./" + outFolder + "/OptimalStrategy.gff")
    	var G1 = M.G.buildMealyMachineActs()
    	G1.exportMachine
    	var B1 = new Game
        B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
        println("MMP : " +B1.states.size)
        //parity strategy computation
        M.setParityActs()
        var G2 = M.G.buildMealyMachineActs()
    	G2.exportMachine
    	var B2 = new Game
    	B2.buildautomaton("tempf.gff")
    	B2.reduceAutomaton
    	B2.exportAutomaton("./" + outFolder + "/MealyMachineParity.gff")
        println("MPar : " +B2.states.size)
      System.exit(0)
    }

    if(mode == "solveMDP" || mode == "solveMDPext"){//from specification as one LMPA,one safety Automaton and
        val file_distr = args(3)
   	val outFolder = args(4)
   	Runtime.getRuntime().exec("mkdir " + outFolder)
   	var B = Game.ProdMultMDP(A1,A2,file_distr)
   	B.ni = max(A1.ni,A2.ni)
    	B.reduceAutomaton //incorporated the zero weight paradigm
    	B.cleanUp
    	B.check
    	B.exportAutomaton("./"+outFolder+"/Prod.gff")
        println("Prod : "+ B.states.size)
    	B.mode_MDP = 1;
    	var g = B.auto2Game(minterms)
    	g.updateWeights
    	g.b = g.states.size * g.states.size * g.wMax + 1
    	g.mode_MDP = 1
    	g.L =1
	g.exportGame("./" + outFolder + "/Game.gff")
        println("Game : " +g.states.size)
        var M = new MDP
        M.G = g
        M.setActions
        M.exportMDP("./" + outFolder + "MDP.rff")
        if(mode=="solveMDPext"){
          //use external program to solve MP mdp and take input from that file to decide selActs
	  println("Run external solver")
	  println("./mdpsolver/mdp ./" + outFolder+"MDP.rff ./"+outFolder+"MDPsoln.rff")
	  
          run("./mdpsolver/mdp ./" + outFolder+"MDP.rff ./"+outFolder+"MDPsoln.rff")
          var fnm = "./"+outFolder+"MDPsoln.rff"
          for ((line) <- Source.fromFile(fnm).getLines) {
            val labels = line.split(' ')
	    val src = labels.head.toInt
	    val dst = labels.tail.head.toInt
	    M.G.states(src).selAct = dst
          }
        }
        else{
          M.policyIteration()
        }
        M.G.exportStrategy("./" + outFolder + "/OptimalStrategy.gff")
        var G1 = M.G.buildMealyMachineActs()
    	G1.exportMachine
    	var B1 = new Game
    	B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
        println("Mealy : "+B1.states.size)
      System.exit(0)
    }

    if((mode == "solveDPG") && (args.size > 4)){//from specification as one LMPA and one safety Automaton
   	var B = Game.ProdMult2(A1,A2)
   	B.ni = max(A1.ni,A2.ni)
   	val outFolder = args(4)
   	Runtime.getRuntime().exec("mkdir " + outFolder)
    	B.reduceAutomaton //incorporated the zero weight paradigm
    	B.cleanUp
    	B.check
    	B.exportAutomaton("./"+outFolder+"/Prod.gff")
    	var g = B.auto2Game(minterms)
    	g.updateWeights
    	g.b = g.states.size * g.states.size * g.wMax + 1
    	g.redmpg_mode = 1
    	g.L = Math.sqrt(args(3).toDouble)
	g.exportGame("./" + outFolder + "/Game.gff")
    	g.valueIteration2(0)
    	g.printValues1D
    	g.optimalStrategyDPG(0)
    	g.exportGame("./" + outFolder + "/OptimalStrategy.gff")
    	var G1 = g.buildMealyMachine()
    	G1.exportMachine
    	var B1 = new Game
    	B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
      System.exit(0)
    }
/*    else if (mode == "game2machine"){ //from game to optimal strategy and Final Machine 
    	// mode file outputFolder
      	var g = new Game
      	g.buildGame(args(1),args(2).toDouble)
      	g.b = g.states.size * g.states.size * g.wMax + 1
      	//g.updateWeights --not needed
      	g.exportGame("./" + outFolder + "/Game.gff")
    	g.valueIteration(args(3).toDouble)
    	//g.printValues()

    	if(g.L==1) g.printValues1D
    	else g.printValuesDIM()
    	//println("Here!")
    	if(g.L==1) g.optimalStrategyL(args(4).toDouble)
    	else g.optimalStrategy(args(4).toDouble)
    	outFolder = args(4)
    	g.exportGame("./" + outFolder + "/OptimalStrategy.gff")
    	var G1 = g.buildMealyMachine()
    	G1.exportMachine
    	var B1 = new Game
    	B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
    }
    else if (mode == "auto2machine"){ //from automata to game -> optimal strategy and Final Machine
    	// mode file lambda threshold outputFolder
      	var file1 = args(1)
	var B = new Game
    	B.buildautomaton(file1) 
    	outFolder = args(4)
   	Runtime.getRuntime().exec("mkdir " + outFolder)
    	B.reduceAutomaton //incorporated the zero weight paradigm
    	B.cleanUp
    	B.check
    	B.exportAutomaton("./"+outFolder+"/Prod.gff")
    	B.printAutomaton
    	var g = B.auto2Game(minterms)
    	g.L =args(2).toDouble
    	g.updateWeights
    	g.b = g.states.size * g.states.size * g.wMax + 1
      	//g.updateWeights --not needed
      	g.exportGame("./" + outFolder + "/Game.gff")
    	g.printGame
    	g.valueIteration(args(3).toDouble)    	
    	if(g.L==1) g.printValues1D
    	else g.printValuesDIM()
    	//println("Here!")
    	if(g.L==1) g.optimalStrategyL(args(3).toDouble)
    	else g.optimalStrategy(args(3).toDouble)
    	g.exportGame("./" + outFolder + "/OptimalStrategy.gff")
    	var G1 = g.buildMealyMachine()
    	G1.exportMachine
    	var B1 = new Game
    	B1.buildautomaton("tempf.gff")
    	B1.reduceAutomaton
    	B1.exportAutomaton("./" + outFolder + "/MealyMachine.gff")
    }*/

    val outFile = args(3)
    if (mode == "prodADD"){ //Product of two LMA (using addition of weights)
   	var B = Game.Prod(A1,A2)
    	B.reduceAutomaton
    	B.cleanUp
    	B.check
    	B.exportAutomaton(outFile)
    	System.exit(0)
    }
    
    if (mode == "prodAPPEND"){ //Product of two LMA using lexicographic appending of weights
   	var B = Game.ProdAppend(A1,A2)
    	B.reduceAutomaton
    	B.cleanUp
    	B.check
    	B.exportAutomaton(outFile)
    	System.exit(0)    	
    }
    if (mode == "prodMULT"){ //Product of two LMA using multiplication of weights
   	var B = Game.ProdMult(A1,A2)
    	B.reduceAutomaton2
    	B.cleanUp
    	B.check
    	B.exportAutomaton(outFile)
    	System.exit(0)
    }
    println("Unknown mode")
    printHelp(false)
    System.exit(0)
  }
}
}
