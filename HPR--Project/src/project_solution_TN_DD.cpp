#include "mpi.h"
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <ctime>

// Define macros for the colums of the matrices
#define X_COLS 2
#define Y_COLS 1
#define Z_COLS 10000

// Define error and distribution values
#define SIGMA_E 10.0
#define SIGMA_S 30.0
#define ERR_DEV ((SIGMA_E*SIGMA_E)/(SIGMA_S*SIGMA_S))

// Add numberints and numberdoubles for Scalapack so these can be referenced
int zero = 0; double d_zero = 0.0;
int one = 1; double d_one = 1.0;
int mone = -1; double d_mone = -1.0;

// Add the Scalapack transposed and normal chars for the matrices
char trans = 'T';
char normal = 'N';

// Define the external methods from the libs
extern "C" {
  void sl_init_(int* ictxt, int* nprow, int* npcol);
  void blacs_gridinfo_(int* ictxt, int* nprow, int* npcol, int* myrow, int* mycol);
  void descinit_(int* desc, int* m, int* n, int* mb, int* nb, int* rsrc, int* csrc, int* ictxt, int* mxllda, int* info);
  void pdgesv_(int* n, int* nrhs, double* A, int* iA, int* jA, int* descA, int *iPiv, double *B, int* iB, int *jB, int *descB, int* info);
  void pdgemv_(char*, int * M, int * N, double * ALPHA, double * A, int * IA, int * JA, int * DESCA, double * X, int * IX, int * JX, int * DESCX, int * INCX, double * BETA, double * Y, int * IY, int * JY, int * DESCY, int * INCY);
  void pdgemm_(char *, char*, int*, int*, int*, double *, double *, int*, int *, int *, double*, int *, int *, int*, double *, double *, int*, int *, int*);
  void pdlaset_(char*, int*, int*, double*, double*, double*, int*, int*, int*);
  void dgesd2d_(int *, int *, int *, double*, int *, int *, int *);
  void dgerv2d_(int *, int *, int *, double*, int *, int *, int *);
  int numroc_(int*, int*, int*, int*, int*);
}

// Define the std namespace
using namespace std;

/*********************************
 * Fill the X matrix
 * We read a line at a time and prepend a one as shown in the example code
 ********************************/
int fill_X(double** X, string file_name)
{
  // Define number of lines
  int lines = 0;

  // Create an ifstream for the input file
  ifstream file(file_name.c_str());

  // Make sure the file is open for reading
  if(file.is_open())
  {
    // Get the first line containing the number of lines
    string line;
    getline(file, line);
    lines = atoi(line.c_str());

    // Allocate the array with the given size: number of lines * 2 for the ones
    *X = new double[lines*2];

    // Read the rest of the file into an array
    for(int i = 0; i < lines; i++)
    {
      // Get the next line
      getline(file, line);
      // Prepend a 1
      (*X)[i] = 1.0;
      // Read the number and save it in x
      (*X)[i + lines] = atoi(line.c_str());
    }

    // Close the stream
    file.close();
  }

  // Return the number of lines so we can use it later on
  return lines;
}

/*********************************
 * Fill the Y vector
 * We read a line at a time and put the content of that line in the vector
 ********************************/
int fill_Y(double** Y, string file_name)
{
  // Define a variable for the number of lines
  int lines = 0;

  // Create an ifstream
  ifstream file(file_name.c_str());

  // Make sure the file is open before reading
  if(file.is_open())
  {
    // Get the first line containing the number of lines
    string line;
    getline(file, line);
    // Save the number of lines
    lines = atoi(line.c_str());

    // Allocate the vector with the given size
    *Y = new double[lines];

    // Read the rest of the file into an array
    for(int i = 0; i < lines; i++)
    {
      // Get the next line
      getline(file, line);
      // Put it in Y
      (*Y)[i] = atoi(line.c_str());
    }

    // Close the stream
    file.close();
  }

  // Return the number of lines so we can use it later on if needed
  return lines;
}

/*********************************
 * Scatter a matrix to all processors
 * This is a generic functions which takes the parameters needed to distribute the matrix
 * Distributes using dgesd2d and dgerv2d
 ********************************/
void scatter_matrix(int ictxt, double* from, double* to, int m, int n, int mb, int nb, int locr, int locc, int lld, int nprocs, int nprow, int npcol, int mycol, int myrow, bool root)
{
  // Define variables
  int sendr = 0, sendc = 0, recvr = 0, recvc = 0;

  // Iterate over the number of rows by the size of a block
  for(int row = 0; row < m; row += mb, sendr = (sendr+1) % nprow)
  {
    sendc = 0;

    // Number of rows to be sent
    int nr = mb;
    // If there are less rows left than there are rows in a block; adjust the number of rows to be sent
    if(m - row < mb)
      nr = m - row;

    // Iterate over the number of cols
    for(int col = 0; col < n; col += nb, sendc = (sendc+1) % npcol)
    {
      // Number of cols to be sent
      int nc = nb;
      // If there are less cols left than there are cols in a block; adjust the number of cols to be sent
      if(n - col < nb)
        nc = n - col;

      // The root sends the part of the matrix
      if(root) {
        // Send an nr-by-nc submatrix to the process (sendc, sendr) located at from+m*col+row
        dgesd2d_(&ictxt, &nr, &nc, from+m*col+row, &m, &sendr, &sendc);
      }

      // Is it destined for me? Yes? Yes! Receive it! Take it all!
      if(myrow == sendr && mycol == sendc)
      {
        // Receive an nr-by-nc submatrix from the root (sendc = 0, sendr = 0) and put it located at to+locr+recvc+recvr
        dgerv2d_(&ictxt, &nr, &nc, to+locr*recvc+recvr, &lld, &zero, &zero);
        // Increment the recvc as needed
        recvc = (recvc + nc) % locc;
      }
    }

    // Increment the recvr as needed
    if (myrow == sendr)
      recvr = (recvr + nr) % locr;
  }
}

/*********************************
 * Gather a matrix from all processors
 * This is a generic functions which takes the parameters needed to gather the matrix
 * Gathers using dgesd2d and dgerv2d
 ********************************/
void gather_matrix(int ictxt, double* from, double* to, int m, int n, int mb, int nb, int locr, int locc, int lld, int nprocs, int nprow, int npcol, int mycol, int myrow, bool root)
{
  // Define variables
  int sendr = 0, sendc = 0, recvr = 0, recvc = 0;

  // Iterate over the number of rows by the size of a block
  for (int row = 0; row < m; row += mb, sendr = (sendr+1) % nprow)
  {
    sendc = 0;

    // Number of rows to be sent
    int nr = mb;
    // If there are less rows left than there are rows in a block; adjust the number of rows to be sent
    if (m - row < mb)
      nr = m - row;

    // Iterate over the number of cols
    for (int col = 0; col < n; col += nb, sendc = (sendc+1) % npcol)
    {
      // Number of cols to be sent
      int nc = nb;
      // If there are less cols left than there are cols in a block; adjust the number of cols to be sent
      if (n - col < nb)
        nc = n - col;

      // Is it my turn to send? Yes? Yes! Sent it! Send it all!
      if (myrow == sendr && mycol == sendc) {
        // Send an nr-by-nc submatrix to the process (sendc, sendr) located at from+m*col+row
        dgesd2d_(&ictxt, &nr, &nc, from+locr*recvc+recvr, &lld, &zero, &zero);
        // Increment the recvc as needed
        recvc = (recvc+nc) % locc;
      }

      // The root receives the part of the matrix
      if (root) {
        // Receive an nr-by-nc submatrix from the root (sendc = 0, sendr = 0) and put it located at to+locr+recvc+recvr
        dgerv2d_(&ictxt, &nr, &nc, to+m*col+row, &m, &sendr, &sendc);
      }
    }

    // Increment the sendr as needed
    if (myrow == sendr)
      recvr = (recvr + nr) % locr;
  }
}

// AUXILARY FUNCTIONS
/*********************************
 * Print matrix
 * A helpfunction to print a column-major matrix
 ********************************/
void print_matrix(double* matrix, int rows, int cols)
{
    for (int row = 0; row < rows; row++) {
      for (int col = 0; col < cols; col++) {
        cout << matrix[col*rows+row] << "\t";
      }
      if(cols > 0)
        cout << endl;
    }
}

double prevTime;
/*********************************
 * Starts a chrono
 ********************************/
void startChrono()
{
  prevTime = MPI_Wtime();
}

/*********************************
 * Stops a chrono
 ********************************/
double stopChrono()
{
  double currTime = MPI_Wtime();
  return currTime - prevTime;
}

/*********************************
 * Main
 * Takes 3 arguments: the path to X, Y and Z respectively
 ********************************/
int main(int argc, char** argv)
{

  // First things first: init MPI
  int rank, size;
  bool root; int iroot = 0;
  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  // Reserve a bool for the root proces
  root = (rank == 0);

  /********************
   * 0. Define variables used all-around
   ********************/
  // Data matrices
  double* X; int size_X;
  double* Y; int size_Y;
  double* Z; int size_Z;

  // Scalapack output variable
  int info;

  /********************
   * 2. Set up a process grid
   ********************/
  // Init the grid
  int ictxt, nprocs = 64, nprow = 8, npcol = 8, myrow, mycol;
  sl_init_(&ictxt, &nprow, &npcol);
  blacs_gridinfo_(&ictxt, &nprow, &npcol, &myrow, &mycol);

  /********************
   * 1. Read all data from X and Y
   * 3. Distribute, using a block cyclic distribution, the data across the process grid
   ********************/

  // A. READ AND DISTRIBUTE X

  if(root)
    size_X = fill_X(&X, argv[1]);

  // Send the number of rows to all processes
  MPI_Bcast(&size_X, 1, MPI_INT, iroot, MPI_COMM_WORLD);

  // Describe X
  int mX = size_X, nX = X_COLS;  // global dimensions (size_X x X_COLS matrix)
  int mbX = 2, nbX = 2; // block dimensions
  int rsrcX = 0, csrcX = 0; // process row / column of which the first row/column is distributed
  int locrX = numroc_(&mX, &mbX, &myrow, &zero, &nprow); // local number of rows
  int loccX = numroc_(&nX, &nbX, &mycol, &zero, &npcol); // local number of columns
  int lldX = locrX; // local leading dimension;
  int globsrX = 1; // start row index in the global matrix
  int globscX = 1; // start col index in the global matrix

  int *descX = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(descX, &mX, &nX, &mbX, &nbX, &rsrcX, &csrcX, &ictxt, &lldX, &info);

  // Allocate space for the local part of X
  double* locX = new double[locrX * loccX]();

  // Scatter X!
  scatter_matrix(
      ictxt,
      X, locX,
      mX, nX, mbX, nbX,
      locrX, loccX, lldX,
      nprocs, nprow, npcol,
      mycol, myrow,
      root);

  // X can be cleaned now!
  if(root)
    delete[] X;

  // B. READ AND DISTRIBUTE Y

  if(root)
    size_Y = fill_Y(&Y, argv[2]);

  // Send the number of rows to all processes
  MPI_Bcast(&size_Y, 1, MPI_INT, iroot, MPI_COMM_WORLD);

  // Describe Y
  int mY = size_Y, nY = Y_COLS;  // global dimensions (size_Y x Y_COLS matrix)
  int mbY = 2, nbY = 1; // block dimensions
  int rsrcY = 0, csrcY = 0; // process row / column of which the first row/column is distributed
  int locrY = numroc_(&mY, &mbY, &myrow, &zero, &nprow); // local number of rows
  int loccY = numroc_(&nY, &nbY, &mycol, &zero, &npcol); // local number of columns
  int lldY = locrY; // local leading dimension;
  int globsrY = 1; // start row index in the global matrix
  int globscY = 1; // start col index in the global matrix

  int *descY = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(descY, &mY, &nY, &mbY, &nbY, &rsrcY, &csrcY, &ictxt, &lldY, &info);

  // Allocate space for the local part of Y
  double* locY = new double[locrY * loccY]();


  // Scatter Y!
  scatter_matrix(
      ictxt,
      Y, locY,
      mY, nY, mbY, nbY,
      locrY, loccY, lldY,
      nprocs, nprow, npcol,
      mycol, myrow,
      root);

  // Y can be cleaned now!
  if(root)
    delete[] Y;

  /***************
   * C. Distribute Z
   *
   * This is a special case: Z is too large to save in
   * one proces and then distribute it to all other processes.
   * So we only keep a tiny part of Z and overwrite it with the
   * next lines the following iteration
   *
   * We follow the following approach:
   * i.   Read the amount of lines a blockheight is high
   * ii.  Perform the calculations on those lines
   * iii. Store them in the local smart part of Z
   * iv.  Distribute that small part of Z
   ***************/
  // Define the size of Z
  size_Z = 0;

  // Create an ifstream
  ifstream file(argv[3]);

  // The root reads the size of Z from the first line of the file
  if(root) {
    // Make sure the file is open
    if(file.is_open())
    {
      // Get the first line containing the number of lines
      string line;
      getline(file, line);
      // Store the size of Z
      size_Z = atoi(line.c_str());
    }
  }

  // Distribute the size so all processors can use this
  MPI_Bcast(&size_Z, 1, MPI_INT, iroot, MPI_COMM_WORLD);

  // Describe Z
  int mZ = size_Z, nZ = Z_COLS;  // global dimensions (size_Z x Z_COLS matrix)
  int mbZ = 2, nbZ = 2; // block dimensions
  int rsrcZ = 0, csrcZ = 0; // process row / column of which the first row/column is distributed
  int locrZ = numroc_(&mZ, &mbZ, &myrow, &zero, &nprow); // local number of rows
  int loccZ = numroc_(&nZ, &nbZ, &mycol, &zero, &npcol); // local number of columns
  int lldZ = locrZ; // local leading dimension;
  int globsrZ = 1; // start row index in the global matrix
  int globscZ = 1; // start col index in the global matrix

  int *descZ = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(
      descZ,
      &mZ, &nZ, &mbZ, &nbZ,
      &rsrcZ, &csrcZ,
      &ictxt, &lldZ, &info);

  // Allocate space for the local part of Z
  double* locZ = new double[locrZ * loccZ]();

  // Scatter Z while reading it!
  // Z is our temporary read buffer here
  string line;

  /* Perform the reading and the scattering as described above
   * This actually is a mix of scatter_matrix and a fill function */

  // Initiate the variables
  int sendr = 0, sendc = 0, recvr = 0, recvc = 0;

  // Iterate over the number of rows by the size of a block
  for(int row = 0; row < mZ; row += mbZ, sendr = (sendr+1) % nprow)
  {
    sendc = 0;

    // Number of row to be sent
    int nr = mbZ;
    // If there are less rows left than there are rows in a block; adjust the number of rows to be sent
    if(mZ - row < mbZ)
      nr = mZ - row;

    // Allocate space for the local temporary part of Z
    if(root)
      Z = new double[mbZ * Z_COLS]();

    // Let the root process read blockheight lines
    if(root)
    {
      // Read a few lines
      for(int i = 0; i < nr; i++)
      {
        // Get the line from the file
        getline(file, line);

        // Create a stringstream for each line
        stringstream s(line);
        string z1, z2;

        // Read z1 and z2
        s >> z1 >> z2;

        // We only have 2 columns at max and 1 at min in Z, so we have 2x 0.5 or 1x 1
        if (z2.empty())
        {
          Z[(atoi(z1.c_str()) - 1) * mbZ + i] = 1.0;
        }
        else
        {
          Z[(atoi(z1.c_str()) - 1) * mbZ + i] = 0.5;
          Z[(atoi(z2.c_str()) - 1) * mbZ + i] = 0.5;
        }
      }
    }

    // We now have the blockheight lines, now we just need to scatter them

    // Iterate over the columns
    for(int col = 0; col < nZ; col += nbZ, sendc = (sendc+1) % npcol)
    {
      // Number of cols to be sent
      int nc = nbZ;
      // If there are less cols left than there are cols in a block; adjust the number of cols to be sent
      if(nZ - col < nbZ)
        nc = nZ - col;

      // The root sends the part of the matrix
      if(root) {
        // Send an nr-by-nc submatrix to the process (sendc, sendr) located at from+m*col
        dgesd2d_(&ictxt, &nr, &nc, Z+mbZ*col, &mbZ, &sendr, &sendc);
      }

      // Is it destined for us? Yes? Yes! Receive it! Take it all!
      if(myrow == sendr && mycol == sendc)
      {
        // Receive an nr-by-nc submatrix from the root (sendc = 0, sendr = 0) and put it located at to+locr+recvc+recvr
        dgerv2d_(&ictxt, &nr, &nc, locZ+locrZ*recvc+recvr, &lldZ, &zero, &zero);
        // Increment the recvc as needed
        recvc = (recvc + nc) % loccZ;
      }
    }

    // Increment the recvr as needed
    if (myrow == sendr)
      recvr = (recvr + nr) % locrZ;

    // Z local can be cleaned now; leave no pointers behind!
    if(root)
      delete[] Z;
  }

  // Close the file
  if(root)
    file.close();

  /********************
   * 4. Calculate the ZTZ matrix
   * 5. Construct the mixed model equations
   *
   * This is the part which calculates the left big block
   * which contains of ZTZ, XTZ, ZTX and ZTZ
   *
   * This big matrix is (wrongly, sorry) called ZTZ
   * but I noticed this too late :(
   *
   * We first describe the big ZTZ matrix and fill
   * the part belonging to the real ZTZ with the
   * error value times the identity matrix
   *
   * We then describe and calculate the other parts from ZTZ
   * and fill them directly into the ZTZ matrix
   *
   * After this is done, we describe the solutions vector
   *
   * And we also describe the right hand side of the system
   * by defining the vector and multiplying the correct
   * matrices with the y vector
   ********************/

  if(root)
    startChrono();

  // A. prefil locZTZ with the ID matrix

  // Describe ZTZ
  int mZTZ = X_COLS + Z_COLS, nZTZ = X_COLS + Z_COLS;  // global dimensions
  int mbZTZ = 2, nbZTZ = 2; // block dimensions
  int rsrcZTZ = 0, csrcZTZ = 0; // process row / column of which the first row/column is distributed
  int locrZTZ = numroc_(&mZTZ, &mbZTZ, &myrow, &zero, &nprow); // local number of rows
  int loccZTZ = numroc_(&nZTZ, &nbZTZ, &mycol, &zero, &npcol); // local number of columns
  int lldZTZ = locrZTZ; // local leading dimension;

  int *descZTZ = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(
      descZTZ,
      &mZTZ, &nZTZ, &mbZTZ, &nbZTZ,
      &rsrcZTZ, &csrcZTZ,
      &ictxt, &lldZTZ, &info);

  // Allocate space for the local ZTZ matrix
  double* locZTZ = new double[locrZTZ * loccZTZ]();

  // Initialize the locZTZ part of ZTZ with the identitymatrix
  char uplo = 'U'; // This is just a speed improvement so we only fill in half the matrix with 0
  double diagonals = ERR_DEV; // The diagonals get the error dev coefficient
  int globsrDIA = 1 + X_COLS; // start row index in the global matrix
  int globscDIA = 1 + X_COLS; // start col index in the global matrix

  // Use pdlaset to fill in above said ID matrix
  pdlaset_(
      &uplo,
      &nZ, &nZ,
      &d_zero, &diagonals,
      locZTZ, &globsrDIA, &globscDIA, descZTZ);

  // B. multiply XTX and put it in its corner

  int globsrXTX = 1; // start row index in the global matrix
  int globscXTX = 1; // start col index in the global matrix
  // Put XTX in its corner
  pdgemm_(
      &trans, &normal, // Trans A and B
      &nX, &nX, &mX, // GLOBAL rows of X, GLOBAL cols of X and GLOBAL colums of X
      &d_one, // Alpha coeff
      locX, &globsrX, &globscX, descX, // A, A global row index, A global col index and descr A
      locX, &globsrX, &globscX, descX, // B, B global row index, B global col index and descr B
      &d_zero, // Beta coeff
      locZTZ, &globsrXTX, &globscXTX, descZTZ // C, C global row index, C global col index and descr C
      );

  // C. multiply XTZ and put it in its corner

  int globsrXTZ = 1; // start row index in the global matrix
  int globscXTZ = 1 + X_COLS; // start col index in the global matrix
  // Put XTZ in its corner
  pdgemm_(
      &trans, &normal, // Trans A and B
      &nX, &nZ, &mX, // GLOBAL rows of X, GLOBAL cols of Z and GLOBAL colums of A
      &d_one, // Alpha coeff
      locX, &globsrX, &globscX, descX, // A, A global row index, A global col index and descr A
      locZ, &globsrZ, &globscZ, descZ, // B, B global row index, B global col index and descr B
      &d_zero, // Beta coeff
      locZTZ, &globsrXTZ, &globscXTZ, descZTZ // C, C global row index, C global col index and descr C
      );

  // D. multiply ZTX and put it in its corner

  int globsrZTX = 1 + X_COLS; // start row index in the global matrix
  int globscZTX = 1; // start col index in the global matrix
  // Put ZTX in its corner
  pdgemm_(
      &trans, &normal, // Trans A and B
      &nZ, &nX, &mX, // GLOBAL rows of C, GLOBAL cols of C and GLOBAL colums of A
      &d_one, // Alpha coeff
      locZ, &globsrZ, &globscZ, descZ, // A, A global row index, A global col index and descr A
      locX, &globsrX, &globscX, descX, // B, B global row index, B global col index and descr B
      &d_zero, // Beta coeff
      locZTZ, &globsrZTX, &globscZTX, descZTZ // C, C global row index, C global col index and descr C
      );

  // E. multiply ZTZ and put it in its corner

  // Put ZTZ in its corner
  int globsrZTZ = 1 + X_COLS; // start row index in the global matrix
  int globscZTZ = 1 + X_COLS; // start col index in the global matrix
  pdgemm_(
      &trans, &normal, // Trans A and B
      &nZ, &nZ, &mZ, // GLOBAL rows of C, GLOBAL cols of C and GLOBAL colums of A
      &d_one, // Alpha coeff
      locZ, &globsrZ, &globscZ, descZ, // A, A global row index, A global col index and descr A
      locZ, &globsrZ, &globscZ, descZ, // B, B global row index, B global col index and descr B
      &d_one, // Beta coeff
      locZTZ, &globsrZTZ, &globscZTZ, descZTZ // C, C global row index, C global col index and descr C
      );


  // F. describe B, the solution vector

  // Describe B
  int mB = X_COLS + Z_COLS, nB = 1;  // global dimensions
  int mbB = 2, nbB = 1; // block dimensions
  int rsrcB = 0, csrcB = 0; // process row / column of which the first row/column is distributed
  int locrB = numroc_(&mB, &mbB, &myrow, &zero, &nprow); // local number of rows
  int loccB = numroc_(&nB, &nbB, &mycol, &zero, &npcol); // local number of columns
  int lldB = locrB; // local leading dimension;

  int *descB = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(
      descB,
      &mB, &nB, &mbB, &nbB,
      &rsrcB, &csrcB,
      &ictxt, &lldB, &info);

  // Allocate space for the local ZTZ matrix
  double* locB = new double[locrB * loccB]();


  // G. Calculate XTY and put them in B

  // Put XTY in its corner
  int globsrXTY = 1; // start row index in the global matrix
  int globscXTY = 1; // start col index in the global matrix
  pdgemv_(
      &trans, // Trans A
      &mX, &nX,
      &d_one, // Alpha coeff
      locX, &globsrX, &globscX, descX, // A, A global row index, A global col index and descr A
      locY, &globsrY, &globscY, descY, &one, // B, B global row index, B global col index and descr B
      &d_zero, // Beta coeff
      locB, &globsrXTY, &globscXTY, descB, &one // C, C global row index, C global col index and descr C
      );

  // H. Calculate ZTY and put them in B

  // Put ZTY in its corner
  int globsrZTY = 1 + X_COLS; // start row index in the global matrix
  int globscZTY = 1; // start col index in the global matrix
  pdgemv_(
      &trans, // Trans A
      &mZ, &nZ,
      &d_one, // Alpha coeff
      locZ, &globsrZ, &globscZ, descZ, // A, A global row index, A global col index and descr A
      locY, &globsrY, &globscY, descY, &one, // B, B global row index, B global col index and descr B
      &d_zero, // Beta coeff
      locB, &globsrZTY, &globscZTY, descB, &one // C, C global row index, C global col index and descr C
      );


  /********************
   * 6. Solve the mixed model equations
   ********************/
  int *iPiv = new int[locrZTZ + mbB];
  pdgesv_(
      &mB, &nB,
      locZTZ, &one, &one, descZTZ,
      iPiv,
      locB, &one, &one, descB,
      &info
      );

  // We don't need no ZTZ anymore
  delete[] locZTZ; delete[] descZTZ;
  // iPiv can be cleaned too!
  delete[] iPiv;

  /********************
   * 7. Evaluate your solution (check the values of the B vector, and calculate the correlation between the predicted y values ( ̂) and y)
   ********************/
  // A. Get B

  // Gather it back! Zuruck! Zuruck!
  double* locB2;
  if (root)
     locB2 = new double[mB * nB]();

  gather_matrix(
      ictxt,
      locB, locB2,
      mB, nB, mbB, nbB,
      locrB, loccB, lldB,
      nprocs, nprow, npcol,
      mycol, myrow,
      root);

  // Print the YHat
  if (rank == 0) {
    cout << "B:" << endl;
    print_matrix(locB2, mB, nB);
    cout << endl;
  }

  // B. Calculate and get YHat

  // Describe YHat
  int mYHAT = size_Y, nYHAT = Y_COLS;  // global dimensions (size_Y x Y_COLS matrix)
  int mbYHAT = 2, nbYHAT = 1; // block dimensions
  int rsrcYHAT = 0, csrcYHAT = 0; // process row / column of which the first row/column is distributed
  int locrYHAT = numroc_(&mYHAT, &mbYHAT, &myrow, &zero, &nprow); // local number of rows
  int loccYHAT = numroc_(&nYHAT, &nbYHAT, &mycol, &zero, &npcol); // local number of columns
  int lldYHAT = locrYHAT; // local leading dimension;
  int globsrYHAT = 1; // start row index in the global matrix
  int globscYHAT = 1; // start col index in the global matrix

  int *descYHAT = new int[9]; // matrix descriptor which will hold the above arguments
  descinit_(descYHAT, &mYHAT, &nYHAT, &mbYHAT, &nbYHAT, &rsrcYHAT, &csrcYHAT, &ictxt, &lldYHAT, &info);

  // Allocate space for the local YHat vector
  double* locYHAT = new double[locrYHAT * loccYHAT]();

  // Do the calculation
  pdgemv_(
      &normal, // Trans A
      &mX, &nX,
      &d_one, // Alpha coeff
      locX, &one, &one, descX, // A, A global row index, A global col index and descr A
      locB, &one, &one, descY, &one, // YHAT, YHAT global row index, YHAT global col index and descr YHAT
      &d_zero, // YHATHATeta coeff
      locYHAT, &one, &one, descYHAT, &one // C, C global row index, C global col index and descr C
      );

  int three = 3;
  pdgemv_(
      &normal, // Trans A
      &mZ, &nZ,
      &d_one, // Alpha coeff
      locZ, &one, &one, descZ, // A, A global row index, A global col index and descr A
      locB, &three, &one, descY, &one, // YHAT, YHAT global row index, YHAT global col index and descr YHAT
      &d_one, // YHATHATeta coeff
      locYHAT, &one, &one, descYHAT, &one // C, C global row index, C global col index and descr C
      );

  // We can clean a lot now!
  delete[] locX; delete[] descX;
  delete[] locY; delete[] descY;
  delete[] locZ; delete[] descZ;

  // Gather it back! YHATuruck! YHATuruck!
  double* locYHAT2;
  if (root)
     locYHAT2 = new double[mYHAT * nYHAT]();

  gather_matrix(
      ictxt,
      locYHAT, locYHAT2,
      mYHAT, nYHAT, mbYHAT, nbYHAT,
      locrYHAT, loccYHAT, lldYHAT,
      nprocs, nprow, npcol,
      mycol, myrow,
      root);

  // Print the YHat
  if (rank == 0) {
    cout << "YHat:" << endl;
    print_matrix(locYHAT2, mYHAT, nYHAT);
  }

  // We can clean everything that's left over!
  delete[] locB; delete[] descB;
  delete[] locYHAT; delete[] descYHAT;
  if(root)
    delete[] locYHAT2;

  /********************
   * 8. Assess the speed-up as a function of the number of processes used (on Decatty).
   ********************/

  if(root)
    stopChrono();

  /********************
   * Z. Let's clean up
   ********************/
  MPI_Finalize();

  return EXIT_SUCCESS;
}
