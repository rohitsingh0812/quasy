package quasy;
import java.io.*;
import java.util.*;

public class GaussianElimination {
    private static final double EPSILON = 1e-10;

    
    public double abs(double a) {
    	if(a > 0) return a;
    	if(a < 0) return (-a);
    	return 0.0;
    }
    public void printM(double[][] A,double b[],int N) {
    	for(int i=0;i < N;i++){
    		double SUM = 0.0;
    		for(int j=0;j < N;j++){
    			SUM = SUM + A[i][j];
    			System.out.print(A[i][j]);
    			System.out.print(" ");
    		}
    		if(SUM != 1.0) System.out.print( "ERROR! ");
    		System.out.print(b[i]);
    		System.out.print(" ");
    		System.out.println();
    	}
    }
    // Gaussian elimination with partial pivoting
    public double[] lsolve(double[][] A, double[] b) {
        int N  = b.length;

        for (int p = 0; p < N; p++) {

            // find pivot row and swap
            int max = p;
            for (int i = p + 1; i < N; i++) {
                if (Math.abs(A[i][p]) > Math.abs(A[max][p])) {
                    max = i;
                }
            }
            double[] temp = A[p]; A[p] = A[max]; A[max] = temp;
            double   t    = b[p]; b[p] = b[max]; b[max] = t;

            // singular or nearly singular
            if (Math.abs(A[p][p]) <= EPSILON) {
                //throw new RuntimeException("Matrix is singular or nearly singular");
            }
	    else{
            // pivot within A and b
            for (int i = p + 1; i < N; i++) {
                double alpha = A[i][p] / A[p][p];
                b[i] -= alpha * b[p];
                for (int j = p; j < N; j++) {
                    A[i][j] -= alpha * A[p][j];
                }
            }
            }
        }
	
	//printM(A,b,N);
	//System.out.print("hello");
	
	
        // back substitution
        double[] x = new double[N];
        for (int i = N - 1; i >= 0; i--) {
            double sum = 0.0;
            for (int j = i + 1; j < N; j++) {
                sum += A[i][j] * x[j];
            }
            if(abs(A[i][i]) <= EPSILON && abs(b[i]) > EPSILON ){
            	throw new RuntimeException("No Solution!");
            }
            else if(abs(A[i][i]) <= EPSILON){
            	x[i] = 0;
            }
            else {
            	x[i] = (b[i] - sum) / A[i][i];
            }
        }
        return x;
    }
    public double delta(int i,int j) {
    	if(i==j) return 1;
    	else return 0;
    }
    public double[] Solve(double[][] P,double r[],int n) {
    	
    	double[][] A = new double[3*n][3*n];
    	int N = 3*n;
    	double[] b = new double[N];
    	for(int i=0;i < n;i++){
    		b[i] = 0;
    		for(int j=0;j < n;j++){
    			A[i][j] = delta(i,j) - P[i][j];
    		}
    		for(int j=n;j < N;j++){
    			A[i][j] = 0;
    		}
    	}
    	for(int i=n;i < 2*n;i++){
    		b[i] = r[i-n];
    		for(int j=0;j < n;j++){
    			A[i][j] = delta(i-n,j);
    		}
    		for(int j=n;j < 2*n;j++){
    			A[i][j] = delta(i-n,j-n) - P[i-n][j-n];
    		}
    		for(int j=2*n;j < N;j++){
    			A[i][j] = 0;
    		}
    	}
    	for(int i=2*n;i < N;i++){
    		b[i] = 0;
    		for(int j=0;j < n;j++){
    			A[i][j] = 0;
    		}
    		for(int j=n;j < 2*n;j++){
    			A[i][j] = delta(i-2*n,j-n);
    		}
    		for(int j=2*n;j < N;j++){
    			A[i][j] = delta(i-2*n,j-2*n) - P[i-2*n][j-2*n];
    		}
    	}
        //printM(P,r,n);
    	//printM(A,b,N);
    	double[] x = lsolve(A,b);
    	/*for (int i = 0; i < n; i++) {
            System.out.println(x[i]);
        }*/
        return x;
    }
    // sample client
    public void main(String[] args) {
        int n;
        // value n in 1 line followed by n +1 lines (n lines for matrix P and next line for vector b)
        BufferedReader inp = new BufferedReader(new InputStreamReader(System.in));
        try{
        String txt = inp.readLine();
        n = Integer.parseInt(txt);
        //System.out.println(n);
        double[][] P = new double[n][n];
        double[] r = new double[n];
        for(int i=0;i<n;i++){
        	txt = inp.readLine();
        	StringTokenizer st = new StringTokenizer(txt);
        	for(int j=0;j<n;j++){
        		P[i][j] = Double.parseDouble((st.nextElement()).toString());
        		
        	}
        }
        txt = inp.readLine();
        StringTokenizer st = new StringTokenizer(txt);
        for(int j=0;j<n;j++){
        	r[j] = Double.parseDouble((st.nextElement()).toString());
        }
        /*double[][] P = { { 0, 0.5,  0.5 },
                         { 0.2, 0.3, 0.5 },
                         { 0.2, 0.4, 0.4 }
                       };
        double[] r = { 1,2,3 };*/
        //printM(P,r,n);
        Solve(P,r,n);
	}
	catch(Exception e){
	}

        // print results
        

    }

}

