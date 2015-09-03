#include "mpi.h"
#include <cstdlib>
#include <iostream>

extern "C" {
  void sl_init_(int* ictxt, int* nprow, int* npcol);
  void blacs_gridinfo_(int* ictxt, int* nprow, int* npcol, int* myrow, int* mycol);
  void descinit_(int* desc, int* m, int* n, int* mb, int* nb, int* rsrc, int* csrc, int* ictxt, int* mxllda, int* info);
  void pdgesv_(int* n, int* nrhs, double* A, int* iA, int* jA, int* descA, int *iPiv, double *B, int* iB, int *jB, int *descB, int* info);
  void pdgemm_(char *, char*, int*, int*, int*, int*, double *, int*, int *, int *, double*, int *, int *, int*, int *, double *, int*, int *, int*);
}

using namespace std;

void initMatrix(double *A, int *descA, double *B, int *descB)
{
  const double s = 19.0;
  const double c = 3.0;
  const double a = 1.0;
  const double l = 12.0;
  const double p = 16.0;
  const double k = 11.0;

  int ictxt = descA[1];
  int mxlldA = descA[8];
  int nprow, npcol, myrow, mycol;
  blacs_gridinfo_(&ictxt, &nprow, &npcol, &myrow, &mycol);

  if (myrow == 0 && mycol == 0) {
    A[0] = s;
    A[1] = -s;
    A[2] = -s;
    A[3] = -s;
    A[4] = -s;
    A[0+mxlldA] = c;
    A[1+mxlldA] = c;
    A[2+mxlldA] = -c;
    A[3+mxlldA] = -c;
    A[4+mxlldA] = -c;
    A[0+2*mxlldA] = a;
    A[1+2*mxlldA] = a;
    A[2+2*mxlldA] = a;
    A[3+2*mxlldA] = a;
    A[4+2*mxlldA] = -a;
    A[0+3*mxlldA] = c;
    A[1+3*mxlldA] = c;
    A[2+3*mxlldA] = c;
    A[3+3*mxlldA] = c;
    A[4+3*mxlldA] = -c;
    B[0] = 0.0;
    B[1] = 0.0;
    B[2] = 0.0;
    B[3] = 0.0;
    B[4] = 0.0;
  } else if (myrow == 0 && mycol == 1) {
    A[0] = a;
    A[1] = a;
    A[2] = -a;
    A[3] = -a;
    A[4] = -a;
    A[0+mxlldA] = l;
    A[1+mxlldA] = l;
    A[2+mxlldA] = -l;
    A[3+mxlldA] = -l;
    A[4+mxlldA] = -l;
    A[0+2*mxlldA] = k;
    A[1+2*mxlldA] = k;
    A[2+2*mxlldA] = k;
    A[3+2*mxlldA] = k;
    A[4+2*mxlldA] = k;
  } else if (myrow == 0 && mycol == 2) {
    A[0] = a;
    A[1] = a;
    A[2] = a;
    A[3] = -a;
    A[4] = -a;
    A[0+mxlldA] = p;
    A[1+mxlldA] = p;
    A[2+mxlldA] = p;
    A[3+mxlldA] = p;
    A[4+mxlldA] = -p;
  } else if (myrow == 1 && mycol == 0) {
    A[0] = -s;
    A[1] = -s;
    A[2] = -s;
    A[3] = -s;
    A[0+mxlldA] = -c;
    A[1+mxlldA] = -c;
    A[2+mxlldA] = -c;
    A[3+mxlldA] = c;
    A[0+2*mxlldA] = a;
    A[1+2*mxlldA] = a;
    A[2+2*mxlldA] = a;
    A[3+2*mxlldA] = -a;
    A[0+3*mxlldA] = c;
    A[1+3*mxlldA] = c;
    A[2+3*mxlldA] = c;
    A[3+3*mxlldA] = c;
    B[0] = 1.0;
    B[1] = 0.0;
    B[2] = 0.0;
    B[3] = 0.0;
  } else if (myrow == 1 && mycol == 1) {
    A[0] = a;
    A[1] = -a;
    A[2] = -a;
    A[3] = -a;
    A[0+mxlldA] = l;
    A[1+mxlldA] = l;
    A[2+mxlldA] = -l;
    A[3+mxlldA] = -l;
    A[0+2*mxlldA] = k;
    A[1+2*mxlldA] = k;
    A[2+2*mxlldA] = k;
    A[3+2*mxlldA] = k;
  } if (myrow == 1 && mycol == 2) {
    A[0] = a;
    A[1] = a;
    A[2] = -a;
    A[3] = -a;
    A[0+mxlldA] = p;
    A[1+mxlldA] = p;
    A[2+mxlldA] = -p;
    A[3+mxlldA] = -p;
  }
}

int main(int argc, char** argv)
{
  int one = 1, mone = -1;  // constants that need to be passed by reference
  int info; // output variable

  // initialize MPI
  int rank, size;
  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  // initialize the process grid
  int ictxt, nprow = 2, npcol = 3, myrow, mycol;
  sl_init_(&ictxt, &nprow, &npcol);
  blacs_gridinfo_(&ictxt, &nprow, &npcol, &myrow, &mycol);

  cout << "I am process " << rank << "/" << size
    << ", my process row/column is " << myrow << "/" << mycol << endl;

  // define matrix A
  int m = 9, n = 9;  // global dimensions of A (9 x 9 matrix)
  int mb = 2, nb = 2; // block dimensions (2 x 2 blocks)
  int rsrc = 0, csrc = 0; // process row / column of which the first row/column of matrix A is distributed
  int locrA = 5, loccA = 4; // local number of rows / columns of matrix A
  int lldA = 5; // local leading dimension of A (same as locrA);

  int *descA = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(descA, &m, &n, &mb, &nb, &rsrc, &csrc, &ictxt, &lldA, &info);
  double *A = new double[lldA  * loccA];
  double *A0 = new double[lldA  * loccA];

  // define vector B
  int nrhs = 1; // number of right-hand side vectors (= number of columns in B)
  int nbrhs = 1; // block dimension
  int lldB = 5; // local leading dimension of B

  int *descB = new int[9];
  descinit_(descB, &n, &nrhs, &nb, &nbrhs, &rsrc, &csrc, &ictxt, &lldB, &info);
  double *B = new double[lldB];
  double *B0 = new double[lldB];

  initMatrix(A, descA, B, descB);
  initMatrix(A0, descA, B0, descB);

  int *iPiv = new int[locrA + nb];
  pdgesv_(&n, &nrhs, A, &one, &one, descA, iPiv, B, &one, &one, descB, &info);

  char trans = 'N';
  pdgemm_(&trans, &trans, &n, &one, &n, &one, A0, &one, &one, descA, B, &one, &one, descB, &mone, B0, &one, &one, descB);

  // these numbers should be very small or zero
  if (mycol == 0) {
    if (myrow == 0) {
      for (int i = 0; i < 5; i++) {
        cout << B0[i] << endl;
      }
    }
    else if (myrow == 1) {
      for (int i = 0; i < 4; i++) {
        cout << B0[i] << endl;
      }
    }
  }

  // clean up
  MPI_Finalize();

  delete [] descA;
  delete [] descB;
  delete [] A;
  delete [] B;
  delete [] A0;
  delete [] B0;

  // bye
  return EXIT_SUCCESS;
}
