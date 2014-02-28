#include <iostream>
#include <string>
#include<map>
#include <vector>
#include <algorithm>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <ctime>
#include <sstream>
#include <utility>
#include<set>
#include<cmath>
#include <cassert>
#include "sparselib.hh" 
#define DFLAG true
#define pl() if(DFLAG) cout<<__LINE__<<endl
using namespace ::sparselib_load ;
using           ::sparselib::index_type ;
using namespace ::std ;
using ::sparselib_fun::maxval ;
using ::sparselib_fun::minval ;
using ::sparselib_fun::absval ;
#define DBG false
#define DBGP1 false
#define DBGIO false
#define ulli unsigned long long int
//#define nS 3212
#define f(i,n) for(int i=0;i<n;i++)
#define fe(i,s) for(vector<edge*>::iterator i=s.begin();i!=s.end();i++)
#define fi(i,s) for(set<int>::iterator i=s.begin();i!=s.end();i++)
//double EPS = 1e-10;
double EPS = 1e-8;
double EPSCHECK = 1e-5;
bool PROBINPUT = false;
int NNZ = 100000;
string toSTR(int n){
	string s;
	stringstream out;
	out << n;
	return out.str();
}
class sparseMat {
	public:
	vector< pair<int,int> > ij;
	vector<double> v;
	int N;
};
class edge {
	public:
	int from,to; //state number ids
	double prob; // for MDP
	int wt; //for Mean Payoff MDP
	int thread;
	edge(int Id1,int Id2, double p,int w,int th){
		from = Id1;
		to = Id2;
		prob = p;
		wt = w;
		thread = th;
	}
};
class action {
	public:
	int sid; //state to which it belongs
	int a1,a2;
	vector <edge *> edges;
	double cost;
	action(int SID,int b1,int b2) {
		sid = SID;
		a1=b1;
		a2=b2;
	}
	void addEdge(int Id1,int Id2, double p,int w,int th){
		edges.push_back(new edge(Id1,Id2,p,w,th));
	}
	void setCost(){
		cost = 0;
		f(i,edges.size()){
			edge * e = edges[i];
			cost += e->prob * e->wt;
		}
	}
};

class state{
	public:
	int id; //own id
	vector <action *> actions; //assume atleast one action in each state
	int chosen;
	bool bad;
	bool good;
	double value;
	bool badReachable;
	bool goodReachable;
	bool startReachable;
	bool mark,DFSmark;
	int OID1,OID2;
	int iden1,iden2;
	state(int Id,bool b,int i1,int i2,int oid1,int oid2){
		id = Id;
		chosen = 0;
		bad =b;
		value =0.0;
		badReachable = b;
		if(id==0) startReachable = true;
		else startReachable = false;
		iden1 = i1;
		iden2 = i2;
		good = false;
		OID1 = oid1;
		OID2 = oid2;
		DFSmark = false;
	}
	void printComp(){
		cout<<" ("<<OID1<<","<<OID2<<")";
	}
	vector <edge *> incoming; //to be set before MC computation every time!
	void print(){
		cout<<"STATE "<<id<<" ("<<iden1<<","<<iden2<<")    "<<" {"<<OID1<<","<<OID2<<"}    "<<actions.size()<<" actions. BadProb = "<<value<<endl;
		f(j,actions.size()){
			if(j==chosen) cout<<"C";
			cout<<"\tACTION "<<j<<endl;
			f(k,actions[j]->edges.size()){
				cout<<"\t\tEDGE "<<actions[j]->edges[k]->to<<" "<<actions[j]->edges[k]->prob<<" "<<actions[j]->edges[k]->wt<<endl;
			}
		}
	}
	void printsucc(){
		cout<<"STATE "<<id<<" ("<<iden1<<","<<iden2<<") -> [ ";
			f(k,actions[chosen]->edges.size()){
				if(k!=0) cout<<",";
				cout<<actions[chosen]->edges[k]->to;
			}
			cout<<" ]"<<endl;
	}
};
	bool fncomp (pair<int,int> lhs, pair<int,int> rhs) {
		if(lhs.first < rhs.first) return true;
		if(lhs.first == rhs.first && lhs.second < rhs.second) return true;
		return false;
	}

class MDP {
	public:
	
	map <int,state*> states;
	int N;
	bool valid;
	//vector <int> policy; //stored in actions as in chosen field (default 0)
	MDP(string fname,int i){
		if(!parse(fname)){
			//cout<<i<<" : "<<"Invalid MDP!"<<endl;
			valid = false;
		}
		else valid = true;
		/*f(i,states.size()){
			policy.push_back(0);
		}*/
	}

	~MDP(){
		f(i,states.size()){
			f(j,states[i]->actions.size()){
				f(k,states[i]->actions[j]->edges.size()){
					delete states[i]->actions[j]->edges[k];
				}
				delete states[i]->actions[j];
			}
			delete states[i];
		}
	}
	bool parse(string filename){
		ifstream fin(filename.c_str());
		if(!fin.is_open()){
			//cout<<"Error in reading MDP file"<<endl;
			return false;
		}
		string type;
		int bd,th,id1,id2,from,to,sid=-1,csid=-1,a1,a2,aid,wt,oldID1,oldID2;
		set<int> bad;
		double prob;
		bool w1,w2;
		bool(*fn_pt)(pair < int , int >,pair < int , int >) = fncomp;
		map < pair < int , int > , int,bool(*)(pair < int , int >,pair < int , int >) > M(fn_pt);
		/*pair<int,int> t(-1,-2);
		M[t] =-1;
		pair<int,int> s(-1,-1);
		if(M.find(s) == M.end()) cout<<"KFH"<<endl;
		M.erase(t);*/
		set < pair <int,int> > check;//,stateseen,edgeseen;
		while(fin >> type) {
			if (type == "BAD"){
				fin>>bd;
				bad.insert(bd);
			}
			else if(type == "STATE") { 
					//if(bad.empty()) return false;
					fin >> id1 >> id2 >> oldID1 >> oldID2 ; //state ids and current thread active in the state
					//cout<<id1<<","<<id2<<";"<<c<<endl;
					pair<int,int> p(id1,id2);
					check.erase(p);
					//stateseen.insert(p);
					if(M.find(p) == M.end()) {
						
						sid++;
						M[p] = sid;
						//if(p.first == 20427) cout<<"LOL:P"<<endl;
						//cout<<"SOMETHING!"<<endl;
						states[sid] = new state(sid, bad.find(id1)!=bad.end(),id1,id2,oldID1,oldID2);
						//if(bad.find(id1)!=bad.end()) cout<<"BAD STATE : "<<sid<<endl;
					}
					else{
						states[M[p]]->OID1 = oldID1;
						states[M[p]]->OID2 = oldID2;
					}
					csid = M[p];
					
					//cout<<"CSID : "<<csid<<endl;
					aid=-1;
			} else if(type == "ACTION") {
				fin>>a1>>a2;
				aid++;
				//cout<<"AID 1 : "<<aid<<endl;
				states[csid]->actions.push_back(new action(csid,a1,a2));
				//cout<<"AID 2 : "<<aid<<endl;
			} else if(type == "EDGE") {
				fin>>id1>>id2>>prob>>wt>>th;
				pair<int,int> p(id1,id2);
				//edgeseen.insert(p);
				if(M.find(p) == M.end()) {
					
					sid++;
					M[p] = sid;
					check.insert(p);
					
					//if(p.first == 20427) cout<<"LOL:P"<<endl;
					states[sid] = new state(sid, bad.find(id1)!=bad.end(),id1,id2,-1,-1);
					//if(bad.find(id1)!=bad.end()) cout<<"BAD STATE : "<<sid<<endl;
				}
				states[csid]->actions[aid]->edges.push_back( new edge (csid,M[p],prob,wt,th));
				//cout<<"EDGE "<< states[csid]->actions[aid]->edges.size() <<" ADDED IN AID : "<<aid<<endl;
			}
		}
		if(!check.empty()) {
		
			cout<<"ERRORMAX :"<< check.size()<<endl;
			for(set< pair<int,int> >::iterator it = check.begin();it != check.end();it++){
				cout<<"("<<(*it).first<<","<<(*it).second<<")"<<" ";
				//if(states[M[*it]]->bad) states[M[*it]]->bad= false;
			}
			cout<<endl;
		}
		/*set<pair<int,int> > temp_set;
		std::set_symmetric_difference(stateseen.begin(), stateseen.end(), edgeseen.begin(), edgeseen.end(), std::inserter(temp_set, temp_set.begin()));
		//cout<<temp_set.size()<<endl;
		for(set< pair<int,int> >::iterator it = temp_set.begin();it != temp_set.end();it++){
			//cout<<"("<<(*it).first<<","<<(*it).second<<")"<<" ";
			if(states[M[*it]]->bad) states[M[*it]]->bad= false;
		}*/
		fin.close();
		//cout<<112<<endl;
		//cout<<sid<<endl;
		if(DBGP1)cout<<"STATES : "<<states.size()<<endl;
		N = states.size();
		int gctr = 0;
		f(i,states.size()){
			if (states[i]->actions.size()==0) {
				if(!states[i]->bad){ states[i]->good = true; gctr++; }
				states[i]->actions.push_back(new action(i,0,-2));
				//states[i]->actions[0]->addEdge(i,i,1.0,0,0); //only for reachability
				states[i]->actions[0]->addEdge(i,0,1.0,0,0);//edge to the start state with cost 0?
			}
		}
		int acts = 0;
		f(i,states.size()){
			if(states[i]->actions.size() > 1){
				//cout<<states[i]->iden1<<endl;
				acts++;
			}
			f(j,states[i]->actions.size()){
				states[i]->actions[j]->setCost();
			}
		}
		cout<<"MAJOR ACTIONS :"<<acts<<endl;
		return true;
		//cout<<120<<endl;
	}
	void print(){
		f(i,states.size()){
			cout<<"STATE "<<i<<endl;
			f(j,states[i]->actions.size()){
				cout<<"\tACTION "<<j<<endl;
				f(k,states[i]->actions[j]->edges.size()){
					cout<<"\t\tEDGE "<<states[i]->actions[j]->edges[k]->to<<" "<<states[i]->actions[j]->edges[k]->prob<<" "<<states[i]->actions[j]->edges[k]->wt<<endl;
				}
			}
		}
	}
	void badDebug(){
		f(i,states.size()){
			
			f(j,states[i]->actions.size()){
				
				f(k,states[i]->actions[j]->edges.size()){
					if(states[states[i]->actions[j]->edges[k]->to]->bad){
						cout<<"STATE "<<i<<endl;
						cout<<"\tACTION "<<j<<endl;
						cout<<"\t\tEDGE "<<states[i]->actions[j]->edges[k]->to<<" "<<states[i]->actions[j]->edges[k]->prob<<" "<<states[i]->actions[j]->edges[k]->wt<<endl;
					}
				}
			}
		}
	}
	ulli numStrats(){
		ulli temp=1;
		f(i,states.size()){
			if(states[i]->actions.size() > 1){ cout<<states[i]->actions.size()<<","; temp++; }
		}
		return temp;
	}
	int badStates(){
		int temp=0;
		f(i,states.size()){
			if(states[i]->bad){ temp++; }
		}
		return temp;
	}
	void multAb(double **A,double b[],double res[],int &n){
		f(i,n){
			res[i] =0;
			f(j,n){
				if(A[i][j] != 0 && b[j] != 0) res[i]+=A[i][j]*b[j];
			}
		}
	}
	void Add(double a[],double b[],double res[],int &n){
		f(i,n) res[i] =a[i]+b[i];
	}
	double absDiff(double *x,double *y,int &n){
		double max = 0,temp;
		f(i,n){
			temp=x[i]-y[i];
			if(temp <0) temp = -temp;
			if(temp > max) max=temp;
		}
		return max;
	}
	void solveLinEq(double **A,double b[],double x[],int &n){
		//solve x=Ax+b
		//x=0 initialized
		f(i,n) x[i] =0.0;
		double t1[n],t2[n],val;
		int itr =0;
		while(1){
			itr++;
			multAb(A,x,t1,n);
			Add(t1,b,t2,n);
			val = absDiff(t2,x,n);
			f(i,n) x[i] = t2[i];
			//cout<<itr<<" : "<<val<<endl;
			if(val<EPS) break;			
		}

	}
	void sparseMatMethod(int ctr,map <int,int> &M, map <int,int> &N ){
		ofstream fout("tempmatrix.sce");
		sparseMat Matrix;
		vector <double> b,x;
		f(i,3*ctr){ 
			b.push_back(0.0); x.push_back(0.0);
			//f(j,ctr) Mat[i][j] = 0;
		}
		Matrix.N = 3*ctr;
		f(i,ctr){
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				if(N.find(e->to) != N.end()){
					{pair<int,int> p (i+1,N[e->to]+1);
					Matrix.ij.push_back(p);
					Matrix.v.push_back(e->prob);}
					{pair<int,int> p (ctr+i+1,ctr+N[e->to]+1);
					Matrix.ij.push_back(p);
					Matrix.v.push_back(e->prob);}
					{pair<int,int> p (2*ctr+i+1,2*ctr+N[e->to]+1);
					Matrix.ij.push_back(p);
					Matrix.v.push_back(e->prob);}
				}
				
			}
			b[ctr+i] = states[M[i]]->actions[states[M[i]]->chosen]->cost;
		}
		f(i,ctr){
			{pair<int,int> p (i+1,ctr+i+1);
			Matrix.ij.push_back(p);
			Matrix.v.push_back(-1);}
			{pair<int,int> p (ctr+i+1,2*ctr+i+1);
			Matrix.ij.push_back(p);
			Matrix.v.push_back(-1);}
			
		}
		f(i,3*ctr){
			{pair<int,int> p (i+1,i+1);
			Matrix.ij.push_back(p);
			Matrix.v.push_back(-1);}
		}
		fout<<"mn = [ "<<3*ctr<<" "<<3*ctr<<" ];"<<endl<<endl;
		fout<<"v = [ ";
		f(i,Matrix.v.size()){
			if(i!=0) fout<<";";
			fout<<Matrix.v[i];
		}
		fout<<"];"<<endl<<endl;
		
		fout<<"ij = [ ";
		f(i,Matrix.ij.size()){
			if(i!=0) fout<<";";
			fout<<Matrix.ij[i].first<<" "<<Matrix.ij[i].second;
		}
		fout<<"];"<<endl<<endl;
		
		fout<<"A = sparse(ij,v,mn)\n"<<endl;
		
		/*fout<<"b = [ ";
		f(i,b.size()){
			if(i!=0) fout<<";";
			fout<<b[i];
		}
		fout<<"];"<<endl<<endl;
		fout<<"[x,kerA] = linsolve(A,b);\n disp('OUTPUT');\n fid = mopen('x.txt', \"w\");\nif (fid == -1)\nerror('cannot open file for writing');\nend\nfor i = x\nmfprintf(fid, \"%f \\n\", i);\nend\nexit\n"<<endl;
		//fout<<"[x,kerA] = linsolve(A,b)\n\n disp('OUTPUT')\n\n disp(x)\n\n disp(kerA)\n\nexit"<<endl<<endl;*/
		fout.close();
		exit(0);
		/*system("scilab -nogui -f tempmatrix.sce > tempio.txt");
		//system("cat tempio.txt");
		ifstream fin("x.txt");
		//string c;
		//while(fin>>c && c != "OUTPUT"){}
		//cout<<"[";
		f(i,ctr){ 
			fin>>x[i];
			states[M[i]]->value = x[i];
			//should work!
			//cout<<x[i]<<" ";
			//assert(x[i] >= 0 && x[i] <= 1);
		}
		//cout<<"]"<<endl;
		fin.close();*/
	}
	void fullMatMethod(int &ctr,map <int,int> &M, map <int,int> &N ){
		double** Mat = new double*[ctr];
		f(i,ctr) Mat[i] = new double[ctr];
		//cout<<350<<endl;
		double b[ctr],x[ctr];
		f(i,ctr){ 
			b[i]=x[i]=0.0;
			f(j,ctr) Mat[i][j] = 0;
		}
		//cout<<356<<endl;
		f(i,ctr){
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				if(N.find(e->to) != N.end()){
					Mat[i][N[e->to]] = e->prob;
				}
				else if(states[e->to]->bad){
					b[i]+= e->prob;
				}
			}
		}
		//cout<<365<<endl;
		solveLinEq(Mat,b,x,ctr);
		//cout<<367<<endl;
		if(DBG) cout<<"[";
		f(i,ctr){ 
			states[M[i]]->value = x[i];
			//should work!
			if(DBG) cout<<x[i]<<" ";
		}
		if(DBG) cout<<"]"<<endl;
		f(i,ctr) delete [] Mat[i];
		delete Mat;
	}
	void Identity(CCoorMatrix<double> & Id,int &n){
		Id.new_dim(n,n,n+1);
		f(i,n){
			Id.insert(i,i) = 1.0;
		}
	}
	void Diag(CCoorMatrix<double> &I,CCoorMatrix<double> &A,int &n){
		I.new_dim(n, n, n*2);
		double d;
		f(i,n){
			//cout<<i<<endl;
			d = A(i,i);
			if(d==0){
				cout<<i<<" : "<<n<<endl;
				assert(d!=0);
			}
			I.insert(i,i) = d;
		}
		I.internal_order();
	}
	void solveSparseLinEqSpl(CCoorMatrix<double> &B,CCoorMatrix<double> &A,sparselib::Vector < double> &b,sparselib::Vector < double> &x,int &n,double &alpha){
		
		//DPreco<double> I;
		//I.build(A);
		
		//Diag(I,A,n);
		//solve Ax=b
		//x=0 initialized
		//cout<<n<<endl;
		x=1.;
		//int iter;
		
		//bicgstab(A,b,x,I,EPS,100000,iter);
		//cg(A, b, x, I, EPS, 10000, iter) ;
		//gmres(A,b,x,I,EPS,100,10000,iter);
		//cout<<iter<<endl;
		sparselib::Vector < double> y(n);
		sparselib::Vector < double> z(n);
		double val=1;
		pl();
		while(val > EPS){
			y = A*x;
			y += b;
			z = B*y;
			//y = ((A * x) + b);
			val = sparselib::normi(x-z);
			cout<<setprecision(10)<<"VAL : "<<val<<endl;
			x=z;
		}

	}
	void solveSparseLinEq(CCoorMatrix<double> &A,sparselib::Vector < double> &b,sparselib::Vector < double> &x,int &n){
		
		//solve x=Ax+b
		//x=0 initialized
		//cout<<n<<endl;
		x=0.;
		sparselib::Vector < double> y(n);
		double val=1;
		pl();
		while(val > EPS){
			y = A*x;
			y += b;
			//y = ((A * x) + b);
			val = sparselib::normi(x-y);
			cout<<setprecision(10)<<"VAL : "<<val<<endl;
			x=y;
		}

	}
	void markStartReachable(){
		f(i,states.size()) states[i]->startReachable = false;
		states[0]->startReachable = true;
		set <int> prevlevel;
		prevlevel.insert(0);
		while(1){
			set <int> thislevel;
			for(set<int>::iterator it = prevlevel.begin();it != prevlevel.end();it++){
				f(k,states[*it]->actions.size()){
					f(j,states[*it]->actions[k]->edges.size()){
						edge * e =states[*it]->actions[k]->edges[j];
						if(!states[e->to]->startReachable){
							states[e->to]->startReachable = true;
							thislevel.insert(e->to);
						}
					}
				}
			}
			if(thislevel.empty()) break;
			prevlevel = thislevel;
		}
	}
	void markSpecialStartReachable(){
		f(i,states.size()) states[i]->startReachable = false;
		states[0]->startReachable = true;
		set <int> prevlevel;
		prevlevel.insert(0);
		while(1){
			set <int> thislevel;
			for(set<int>::iterator it = prevlevel.begin();it != prevlevel.end();it++){
				//f(k,states[*it]->actions.size()){
					int k = states[*it]->chosen;
					f(j,states[*it]->actions[k]->edges.size()){
						edge * e =states[*it]->actions[k]->edges[j];
						if(!states[e->to]->startReachable){
							states[e->to]->startReachable = true;
							thislevel.insert(e->to);
						}
					}
				//}
			}
			if(thislevel.empty()) break;
			prevlevel = thislevel;
		}
	}
	void sparselibMethod(int ctr,map <int,int> &M, map <int,int> &N ){
		CCoorMatrix<double> A;
		A.new_dim(ctr, ctr,100000);
		//cout<<350<<endl;
		sparselib::Vector < double> b(ctr);
		sparselib::Vector < double> x(ctr);	
		b=0.;
		x=0.;
		f(i,ctr){
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				if(N.find(e->to) != N.end()){
					A.insert(i,N[e->to]) = e->prob;
				}
				else if(states[e->to]->bad){
					b[i] += e->prob;
				}
			}
		}
		A.internal_order();
		solveSparseLinEq(A,b,x,ctr);
		if(DBG) cout<<"[";
		f(i,ctr){ 
			states[M[i]]->value = x[i];
			//should work!
			if(DBG) cout<<x[i]<<" ";
		}
		if(DBG) cout<<"]"<<endl;
	}
	void patRAND(CCoorMatrix<double> & Id,int ctr){
		srand((unsigned int)time(NULL));
		Id.new_dim(ctr,ctr,NNZ);
		f(i,ctr){
			Id.insert(i,i) = (rand()%2 + 1)/2.0;
		}
	}
	void solveSparseEqn(CCoorMatrix<double> &A,sparselib::Vector < double> &c,sparselib::Vector < double> &z,int &n,int ITR1,int ITR2){
		IdPreco<double> I;
		z=1.;
		int iter;
		gmres(A,c,z,I,EPS,ITR1,ITR2,iter);
		//cout<< "ITERATIONS : "<<iter<<endl;
	}
	bool testSol(CCoorMatrix<double> &ImP,sparselib::Vector < double> &z,sparselib::Vector < double> &c,sparselib::Vector < double> &x,sparselib::Vector < double> &y,sparselib::Vector < double> &r){
		sparselib::Vector < double> t1(c.size());
		sparselib::Vector < double> t2(c.size());
		t1 = ImP * z;
		t2 = ImP * t1;
		t1 = ImP * t2;
		t2 = t1 -c;
		double val = sparselib::normi(t2);
		if(DBGIO) cout<<"VAL1 : "<<val<<endl;
		if(val > EPSCHECK) return false;
		t1 = ImP*x;
		val = sparselib::normi(t1);
		if(DBGIO) cout<<"VAL2 : "<<val<<endl;
		if(val > EPSCHECK) return false;
		t1 = ImP *y;
		t2 = x + t1 -r;
		val = sparselib::normi(t2);
		if(val > EPSCHECK) return false;
		if(DBGIO) cout<<"VAL3 : "<<val<<endl;
		t1 = y + ImP*z;
		val = sparselib::normi(t1);
		if(val > EPSCHECK) return false;
		if(DBGIO) cout<<"VAL4 : "<<val<<endl;
		return true;
	}
	bool testSol(CCoorMatrix<double> &ImP,sparselib::Vector < double> &x,sparselib::Vector < double> &y,sparselib::Vector < double> &r){
		sparselib::Vector < double> t1(x.size());
		sparselib::Vector < double> t2(x.size());
		t1 = ImP*x;
		double val = sparselib::normi(t1);
		if(DBGIO) cout<<"VAL(a) : "<<val<<endl;
		if(val > EPSCHECK) return false;
		t1 = ImP *y;
		t2 = x + t1 -r;
		val = sparselib::normi(t2);
		if(DBGIO) cout<<"VAL(b) : "<<val<<endl;
		if(val > EPSCHECK) return false;
		
		return true;
	}
	bool findXY(map<int,int> & M,map<int,int> &N,int n,sparselib::Vector < double> &x,sparselib::Vector < double> &y,int MAXITER){
		CCoorMatrix<double> P;
		P.new_dim(n, n,NNZ);
		sparselib::Vector < double> r(n);
		r=0.;
		f(i,n){
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				assert(i != N[e->to]);
				P.insert(i,N[e->to]) = e->prob;
			}
			r[i] = states[M[i]]->actions[states[M[i]]->chosen]->cost;
		}
		P.internal_order();
		//prob matrix and reward vector ready
		sparselib::Vector < double> z;//[MAXITER];
		sparselib::Vector < double> t;//[MAXITER];
		x = 0.;
		y = 0.;
		//f(i,MAXITER) z[i].new_dim(n);
		z.new_dim(n);
		t.new_dim(n);
		f(i,MAXITER){
			if(i%1000 == 0) {cout<<i<<",";
			cout.flush();}
			if(i==0) z =r;
			else z = P * z;
			x += z;
			
		}
		cout<<endl;
		x /= MAXITER;
		f(i,MAXITER){
			if(i%1000 == 0) {cout<<i<<",";
			cout.flush();}
			if(i==0) z =r;
			else { t = P * z; z += t; }
			y += z;
			y -= (i+1) * x; 
		}
		cout<<endl;
		
		//y=0.;
		//f(i,MAXITER){
		//	y += (z[i] - x);
		//}
		//have the value vector and deviation vector
		//test solution
		CCoorMatrix<double> ImP;
		ImP.new_dim(n, n,NNZ);
		f(i,n){
			ImP.insert(i,i) = 1;
			double sum = 1;
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				assert(i != N[e->to]);
				ImP.insert(i,N[e->to]) = -e->prob;
				sum -= e->prob;
			}
			assert(abs(sum) < 0.01);
		}
		ImP.internal_order();
		return testSol(ImP,x,y,r);
		
		if (testSol(ImP,x,y,r)) {
			int allOK = 0;
			f(i,n){
				states[M[i]]->value = x[i];
				if((EPSCHECK+x[i]) <= 0) {
					//cout<<"x["<<i<<"] = "<<x[i]<<endl;
					allOK++;
				}
			
			}
			if(allOK!=0){
				cout<<"Arbitrary Values !"<<endl;
				return false;
			}
			return true;
		} 
		else return false;
		
	}
	bool findValues(map<int,int> & M,map<int,int> &N,int n,sparselib::Vector < double> &x,sparselib::Vector < double> &y){
		CCoorMatrix<double> ImP;
		ImP.new_dim(n, n,NNZ);
		sparselib::Vector < double> r(n);
		sparselib::Vector < double> c(n);
		sparselib::Vector < double> z(n);	
		sparselib::Vector < double> t1(n);
		sparselib::Vector < double> t2(n);
		r=0.;
		z=0.;
		c=0.;
		f(i,n){
			ImP.insert(i,i) = 1;
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				assert(i != N[e->to]);
				ImP.insert(i,N[e->to]) = -e->prob;
			}
			r[i] = states[M[i]]->actions[states[M[i]]->chosen]->cost;
		}
		c = ImP * r;
		c= -c;
		ImP.internal_order();
		if(DBG) cout<<"Started Linear Equation Solving..."<<endl;
		//pl();
		solveSparseEqn(ImP,c,z,n,1500,1500);
		//pl();
		y = ImP * z;
		f(i,y.size()) y[i] = -y[i];
		t1 = ImP *z;
		t2 = ImP * t1;
		x = t2 + r;
		if(!testSol(ImP,z,c,x,y,r)) return false;
		int allOK = 0;
		f(i,n){
			states[M[i]]->value = x[i];
			if((EPSCHECK+x[i]) <= 0) {
				//cout<<"x["<<i<<"] = "<<x[i]<<endl;
				allOK++;
			}
			
		}
		if(allOK!=0) return false;
		if(DBG) cout<<" Value of Start State = "<<setprecision(10)<<x[0]<<endl;
		return true;
	}
	bool findFirstValues(map<int,int> & M,map<int,int> &N,int &n,sparselib::Vector < double> &x,sparselib::Vector < double> &y){
		CCoorMatrix<double> ImP;
		ImP.new_dim(n, n,NNZ);
		cout<<n<<endl;
		sparselib::Vector < double> r(n);
		sparselib::Vector < double> c(n);
		sparselib::Vector < double> z(n);	
		sparselib::Vector < double> t1(n);
		sparselib::Vector < double> t2(n);
		r=0.;
		z=0.;
		c=0.;
		f(i,n){
			ImP.insert(i,i) = 1;
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				assert(i != N[e->to]);
				ImP.insert(i,N[e->to]) = -e->prob;
			}
			r[i] = states[M[i]]->actions[states[M[i]]->chosen]->cost;
		}
		c = ImP * r;
		c= -c;
		ImP.internal_order();
		if(!PROBINPUT) solveSparseEqn(ImP,c,z,n,1000,1000);
		else solveSparseEqn(ImP,c,z,n,3000,3000);
		y = ImP * z;
		f(i,y.size()) y[i] = -y[i];
		t1 = ImP *z;
		t2 = ImP * t1;
		x = t2 + r;
		
		
		//testSol(ImP,z,c,x,y,r);
		t1 = ImP * z;
		t2 = ImP * t1;
		t1 = ImP * t2;
		t2 = t1 -c;
		bool ret = true;
		double val = sparselib::normi(t2);
		//cout<<"VAL1 : "<<setprecision(10)<<val<<endl;
		if(val > EPSCHECK) ret= false;
		t1 = ImP*x;
		val = sparselib::normi(t1);
		//cout<<"VAL2 : "<<setprecision(10)<<val<<endl;
		if(val > EPSCHECK) ret= false;
		t1 = ImP *y;
		t2 = x + t1 -r;
		val = sparselib::normi(t2);
		//cout<<"VAL3 : "<<setprecision(10)<<val<<endl;
		if(val > EPSCHECK) ret= false;
		t1 = y + ImP*z;
		val = sparselib::normi(t1);
		//cout<<"VAL4 : "<<setprecision(10)<<val<<endl;
		if(val > EPSCHECK) ret= false;
		f(i,n){
			states[M[i]]->value = x[i];
			if((EPSCHECK+x[i]) <= 0) {
				//cout<<"x["<<i<<"] = "<<x[i]<<endl;
				ret= false;
			}
		}
		return ret;
		
	}   
	void setvalue(map<int,int> & M,map<int,int> &N,int n,double &alpha){
		int ctr = 3*n;
		CCoorMatrix<double> A;
		CCoorMatrix<double> B;
		A.new_dim(ctr, ctr,NNZ);
		B.new_dim(ctr, ctr,NNZ);
		//cout<<350<<endl;
		sparselib::Vector < double> b(ctr);
		sparselib::Vector < double> x(ctr);	
		b=0.;
		x=0.;
		f(i,n){
			B.insert(n+i,i) = -1;
			B.insert(2*n+i,n+i) = -1;
			B.insert(2*n+i,i) = 1;
		}
		f(i,n){
			f(j,states[M[i]]->actions[states[M[i]]->chosen]->edges.size()){
				edge * e =states[M[i]]->actions[states[M[i]]->chosen]->edges[j];
				//if( i == N[e->to]) { if(e->prob != 1.0) A.insert(i,N[e->to]) = 1- e->prob; }
				//else { if(e->prob != 0) A.insert(i,N[e->to]) = e->prob; }
				//if( n+i == N[e->to]){ if(e->prob != 1.0) A.insert(n+i,N[e->to]) = 1- e->prob;}
				//else { if(e->prob != 0) A.insert(n+i,n+N[e->to]) = e->prob;}
				//if( 2*n+i == N[e->to]) { if(e->prob != 1.0) A.insert(2*n+i,N[e->to]) = 1- e->prob;}
				//else { if(e->prob != 0) A.insert(2*n+i,2*n+N[e->to]) = e->prob; }
				A.insert(i,N[e->to]) = e->prob;
				A.insert(n+i,n+N[e->to]) = e->prob;
				A.insert(2*n+i,2*n+N[e->to]) = e->prob;
			}
			b[n+i] = states[M[i]]->actions[states[M[i]]->chosen]->cost;
			//if(b[n+i] != ((int)b[n+i])) cout<<b[n+i]<<" ";
		}
		//cout<<endl;
		A.internal_order();
		f(i,ctr){
			//assert(A.position(i,i) == NNZ);
			B.insert(i,i) = 1;
		}
		B.internal_order();
		//CCoorMatrix<double> pat;
		//patRAND(pat,ctr);
		//pat.new_dim(ctr,ctr,NNZ);
		//f(i,ctr) pat.insert(i,i) =1.0;
		//pat.internal_order();
		solveSparseLinEqSpl(B,A,b,x,ctr,alpha);
		if(DBG) cout<<"[";
		f(i,ctr){ 
			states[M[i]]->value = x[i];
			//assert(x[i]>0);
			//should work!
			if(DBG) { if(x[i] != 0) cout<<x[i]<<" "; }
		}
		if(DBG) cout<<"]"<<endl;
	}
	void setIncomingEdges(){
		f(i,states.size()){
			states[i]->incoming.clear();
		}
		f(i,states.size()){
			f(j, states[i]->actions[states[i]->chosen]->edges.size()){
				edge * e = states[i]->actions[states[i]->chosen]->edges[j];
				states[e->to]->incoming.push_back(e);
				//cout<<"("<<e->from<<","<<e->to<<") ";
				//if(e->to == *bads.begin()) cout<<"("<<e->from<<","<<e->to<<") ";
			}
		}
	
	}
	void checkRandomOutOfPreStarB(){
		bool canfind = false;
		f(i,states.size()){
			if(states[i]->badReachable){
				f(j, states[i]->actions[states[i]->chosen]->edges.size()){
					edge * e = states[i]->actions[states[i]->chosen]->edges[j];
					if(states[e->to]->badReachable == false){
					 cout<<"Can Find an outgoing edge :-/ "<<i<<" -> "<<e->to<<endl;
					 canfind = true;
					 break;
					}
				}
			}
			if(canfind) break;
		}
	}
	void checkGoodBadConflict(){
		int ct=0;
		f(i,states.size()){
			if(states[i]->goodReachable && states[i]->badReachable) ct++;
		}
		cout<<"Good Bad Conflicts = "<<ct<<endl;
	}
	bool checkGoodBadConflict(int i){
		if(states[i]->goodReachable && states[i]->badReachable) return true;//cout<<"Can Reach both Good and Bad States From State : "<<i<<endl;
		return false;
	}
	void checkStartReachableGoodBad(){
		f(i,states.size()){
			if(states[i]->startReachable && states[i]->goodReachable) {
				cout<<"Found a Start-Reachable Node leading to the good area! "<<i << " : "<<setprecision(20)<<states[i]->value<<endl;
				break;
			}
		}
	}
	
	void BFSlocks(vector<int> &dist,vector<int> &cst){
		set<int> prevlevel;
		prevlevel.insert(0);
		states[0]->DFSmark = true;
		while(1){
			set<int> thislevel;
			fi(i,prevlevel){
				states[(*i)]->DFSmark = true;
				fe(it,states[(*i)]->actions[states[(*i)]->chosen]->edges){
					int id = (*it)->to;
					if(dist[id] == -1){
						dist[id] = dist[(*i)] +1;
					}
					else if(dist[id] > dist[(*i)] +1){
						dist[id] = dist[(*i)] +1;
					}
					if(cst[id] == -1){
						cst[id] = cst[(*i)] +(*it)->wt;
					}
					else if(cst[id] < cst[(*i)] +(*it)->wt){
						cst[id] = cst[(*i)] +(*it)->wt;
					}
					
					if(!states[id]->DFSmark){
						thislevel.insert(id);
					}
				}
			}
			if(thislevel.empty()) break;
			//cout<<thislevel.size()<<endl;
			prevlevel = thislevel;
		}
		return;
	
	}
	void testCycles(){
		markSpecialStartReachable();
		vector<int> dist;
		vector<int> cst;
		f(i,states.size()){ 
			states[i]->DFSmark = false;
			dist.push_back(-1);
			cst.push_back(-1);
		}
		dist[0] =0;
		cst[0]=0;
		BFSlocks(dist,cst);
		cout<<"CYCLE SIZES: ";
		double sum = 0;
		int ctr = 0;
		f(id,states.size()){
			if(states[id]->mark) continue;
			bool lastone = false;
			if(dist[id] >= 0){
			fe(it,states[id]->actions[states[id]->chosen]->edges) if((*it)->to == 0) lastone = true;
			}
			if(lastone){
				//if(dist[id] == x) idx = id;
				assert(dist[id]>=0);
				cout<<id<<":("<<cst[id]<<"/"<<(dist[id]+1)<<"),";
				sum += (cst[id]*1.0)/(dist[id]+1);
				ctr++;
			}
		}
		
		cout<<".. AVG = "<<sum/ctr<<endl;
		markStartReachable();
	}
	
	void printStrategy(string fname){
		ofstream fout(fname.c_str());
		f(i,states.size()){
			if(!states[i]->startReachable) continue;
			fout<<states[i]->iden1<<" "<<states[i]->actions[states[i]->chosen]->a1<<" "<<endl;
		}
	}
	void printDotFile(string fname){
		//setIncomingEdges();
		//setBadReachable();
		markSpecialStartReachable();
		ofstream fout(fname.c_str());
		fout<<"digraph {"<<endl;
		f(i,states.size()){
			if(!states[i]->startReachable) continue;
			f(j, states[i]->actions[states[i]->chosen]->edges.size()){
				edge * e = states[i]->actions[states[i]->chosen]->edges[j];
				fout<<e->from<<" -> "<<e->to<<"[label=\""<<e->wt<</*":"<<states[e->from]->iden1<<"("<<states[e->from]->OID1<<","<<states[e->from]->OID2<<") -> "<<states[e->to]->iden1<<"("<<states[e->to]->OID1<<","<<states[e->to]->OID2<<")"<<*/"\"];"<<endl;
				
			}
		}
		fout<<"}"<<endl;
	}

	void setRandomPolicy(map<int,int> & M,map<int,int> &N,int &n,sparselib::Vector < double> &x,sparselib::Vector < double> &y,int mode){
		int improved = 0;
		if(mode == 0){
		
		f(i,states.size()){
			if(!states[i]->startReachable) continue;
			int bestA1=states[i]->chosen,bestA2=states[i]->chosen;
			double bestS1 = x[N[i]],bestS2=x[N[i]] + y[N[i]];
			f(j,states[i]->actions.size()){
				if(j == states[i]->chosen) continue;
				double s1 = 0,s2=states[i]->actions[j]->cost;
				f(k,states[i]->actions[j]->edges.size()){
					edge * e = states[i]->actions[j]->edges[k];
					s1 += e->prob * x[N[e->to]];
					s2 += e->prob * y[N[e->to]];
				}
				if(bestS1 < s1-EPSCHECK){
					bestA1 = j;
					bestS1 = s1;
				}
				else if ( abs(bestS1 - s1) <= EPSCHECK){
					if(s2-EPSCHECK > bestS2){
						bestA2 = j;
						bestS2 = s2;
					}
				}
			}
			if(bestA1 != states[i]->chosen){
				improved++;
				//if(DBG) cout<<i<<" : (Act1) "<< states[i]->chosen << " -> " <<bestA1 << " -- "<< x[N[i]] << " -> "<< bestS1 << endl;
				states[i]->chosen = bestA1;
			}
			/*else if (bestA2 != states[i]->chosen){
				improved++;
				 cout<<i<<" : (Act2) "<< states[i]->chosen << " -> " <<bestA2 << " -- "<< x[N[i]]+y[N[i]] << " -> "<< bestS2 << endl;
				states[i]->chosen = bestA2;
			}*/
		}
		}
		
		if(improved == 0){
			f(i,states.size()){
				//if(states[i]->actions.size() ==1) continue;
				//int x = rand()%(states[i]->actions.size() -1);
				//if(x == states[i]->chosen) states[i]->chosen = states[i]->actions.size() -1;
				//else 
				states[i]->chosen = rand()%(states[i]->actions.size());
			}
			cout<<"No fake improvement possible..."<<endl;
		}
		else cout<<"fake improvement done..."<<endl;
		//testCycles();
		return;
	}
	
	void setMaps(map<int,int> & M,map<int,int> &N,int &n){
		int ctr=0,rctr=0;
		/*for(set<int>::iterator it = badReach.begin();it != badReach.end();it++){
			if(states[*it]->bad) continue;
			M[ctr] = *it; //sorted
			N[*it] = ctr;
			ctr++;
		}*/
		f(i,states.size()){
			if (states[i]->startReachable){
				M[ctr] =i;
				N[i] = ctr;
				ctr++;
			}
			else rctr++;
		}
		n= ctr;
		//cout<<"RCTR : "<<rctr<<endl;
		//M[0] -> M[ctr-1] are the start reachable states
	}
	void init(map<int,int> & M,map<int,int> &N,int &n,sparselib::Vector < double> &x,sparselib::Vector < double> &y){
		//int ctr = 0;
		int mode = 0;
		while(1){
			setRandomPolicy(M,N,n,x,y,mode);
			//if(findFirstValues(M,N,n,x,y)){
			if(findFirstValues(M,N,n,x,y)){
				break;
			}
			mode  = (mode +1)%2;
			cout<<"RESTARTING..."<<endl;
			//else cout<<ctr<<",";
			//ctr++;
		}
		//cout<<ctr<<endl;
	}
	double ValueStartState(){ //to the states marked bad
		srand((unsigned int) time(NULL));
		markStartReachable();
		map<int,int> M,N;
		int ctr;
		setMaps(M,N,ctr);
		//cout<<"CTR : "<<ctr<<endl;
		sparselib::Vector < double> x(ctr);
		sparselib::Vector < double> y(ctr);
		init(M,N,ctr,x,y);	//setRandomPolicy();
		//x and y have the desired value and deviation vectors
		//setvalue(M,N,ctr,alpha);
		//sparseMatMethod(ctr,M,N);
		//return states[0]->value;
		//init();	
		while(1){
			
			//testCycles();
			int improved = 0;
			f(i,states.size()){
				
				if(!states[i]->startReachable) continue;
				int bestA1=states[i]->chosen,bestA2=states[i]->chosen;
				double bestS1 = x[N[i]],bestS2=x[N[i]] + y[N[i]];
				f(j,states[i]->actions.size()){
					if(j == states[i]->chosen) continue;
					double s1 = 0,s2=states[i]->actions[j]->cost;
					f(k,states[i]->actions[j]->edges.size()){
						edge * e = states[i]->actions[j]->edges[k];
						s1 += e->prob * x[N[e->to]];
						s2 += e->prob * y[N[e->to]];
					}
					if(bestS1 < s1-EPSCHECK){
						bestA1 = j;
						bestS1 = s1;
					}
					else if ( abs(bestS1 - s1) <= EPSCHECK){
						if(s2-EPSCHECK > bestS2){
							bestA2 = j;
							bestS2 = s2;
						}
					}
				}
				if(bestA1 != states[i]->chosen){
					improved++;
					states[i]->chosen = bestA1;
				}
				else if (bestA2 != states[i]->chosen){
					improved++;
					states[i]->chosen = bestA2;
				}
			}
			
			if(improved==0){
				
			 	return states[0]->value;
			}
			//cout<<" IMPROVED = "<<improved<<endl;
			cout<<" Start Value = "<<setprecision(10)<<states[0]->value<<endl;
			//pl();
			if (!findValues(M,N,ctr,x,y)){
				pl();
				cout<<"RESTARTING..."<<endl;
				init(M,N,ctr,x,y);
			}
			//pl();
		}
		
	}
};
int main(int argc,char *argv[]){
	if(argc != 3) { 
		cout<<"Invalid Arguments!"<<endl;
		return 1;
	}
	cout<<argv[1]<<endl;
	string fname = argv[1]; //the first argument
	string oname = argv[2];
	MDP myMDP(fname,1);
	if(!myMDP.valid) {
		cout<<"Invalid MDP Input!"<<endl;
		return 1;
	}
	cout<<"Starting Policy Iteration"<<endl;	
	double x = myMDP.ValueStartState();
	cout<< "Value of Starting State = "<<x<<endl;
	//myMDP.printDotFile("testdataout/graph"+toSTR(ij+1)+".dot");
	/*if(DBGP1){
		int inp;
		cout<<"MDP Debug Mode :"<<endl;
		while(cin>>inp){
			myMDP.states[inp]->print();
		}
	}*/
	myMDP.printStrategy(oname);
	
}
