
#include <stdlib.h>
#include<iostream>
#define f(i,n) for(int i=0;i<n;i++)
using namespace std;

int p2(int n){
	int m=1;
	f(i,n){
		m = m*2;
	}
	return m;
}
int main(int argc, char** argv){
	int numst,n;
	if (argc>1) {
	  n = atoi(argv[1]);
	} else {
	  cin>>n;
	}
	//cout << "Number of clients " << n << endl;
	double p[n];
	f(i,n){
	  if (argc>i+2) {
	    //p[i] = atof(argv[i+2]);
	    p[i]=atoi(argv[i+2])/10.0;
	    //cout << p[i] << endl;
	  } else {
		cin>>p[i];
	  }
	}
	int p2n=p2(n);
	numst = p2n;
	double q[p2n];
	int ctr=0;
	f(ctr,p2n){
		q[ctr]=1;
		int t = ctr;
		f(j,n){
			if(t%2 == 0) q[ctr]*=(1-p[n-j-1]);
			else q[ctr]*=p[n-j-1];
			t=t/2;
		}
	}
	f(i,numst){
		cout<<i<<" ";
		f(j,p2n){
			cout<<q[j];
			if(j!=p2n-1)cout<<" ";
		}
		if(i!=numst-1)cout<<endl;
	}
}
