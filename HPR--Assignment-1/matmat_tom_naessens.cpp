// Name: Tom Naessens
// Nr:   01002991

/***************************************************************************
 *   Copyright (C) 2012-2013 Jan Fostier (jan.fostier@intec.ugent.be)      *
 *                                                                         *
 *   This program is free software; you can redistribute it and/or modify  *
 *   it under the terms of the GNU General Public License as published by  *
 *   the Free Software Foundation; either version 2 of the License, or     *
 *   (at your option) any later version.                                   *
 *                                                                         *
 *   This program is distributed in the hope that it will be useful,       *
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
 *   GNU General Public License for more details.                          *
 *                                                                         *
 *   You should have received a copy of the GNU General Public License     *
 *   along with this program; if not, write to the                         *
 *   Free Software Foundation, Inc.,                                       *
 *   59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.             *
 ***************************************************************************/

#include <cstdlib>
#include <iostream>
#include <ctime>
#include <cstring>
#include <cmath>

#define BLOCK_SIZE 64

using namespace std;

// ==========================================================================
// FUNCTION PROTOTYPE
// ==========================================================================

// double generalized matrix-matrix product C = alpha * A * B + beta * C (BLAS)
extern "C" void dgemm_(const char *transA,   // 'N' for normal product, 'T' for transpose of A
    const char *transB,   // 'N' for normal product, 'T' for transpose of A
    const int *m,         // number of rows of A and C
    const int *n,         // number of columns of A and B
    const int *k,         // number of colums of A, number of rows of B
    const double *alpha,  // scalar value
    const double *A,      // pointer to the first element of A
    const int *LDA,       // leading dimension of A
    const double *B,      // pointer to the first element of B
    const int *LDB,       // leading dimension of B
    const double *beta,   // scalar value
    double *C,            // pointer to the first element of C
    const int *LDC);      // leading dimension of C

// ==========================================================================
// TIMING ROUTINES
// ==========================================================================

double prevTime;

void startChrono()
{
  prevTime = double(clock()) / CLOCKS_PER_SEC;
}

double stopChrono()
{
  double currTime = double(clock()) / CLOCKS_PER_SEC;
  return currTime - prevTime;
}

// ==========================================================================
// MATRIX-VECTOR PRODUCT IMPLEMENTATIONS
// ==========================================================================

/* I defined MIN as a macro here to limit the amount of function calls */
#define MIN(X,Y) ((X) < (Y) ? (X) : (Y))

/* size_t min(size_t a, size_t b) { */
/*   return a < b ? a : b; */
/* } */

/**
 * Perform a matrix-matrix multiplication C = A*B using a strided memory access implementation
 * @param C Pointer to the first element of the m by n matrix C, stored in column major format (output)
 * @param A Pointer to the first element of the m by p matrix A, stored in column major format
 * @param B Pointer to the first element of the p by n matrix B, stored in column major format
 * @param m Number of rows of C and A
 * @param n Number of columns of C and B
 * @param p Number of columns of A, number of rows of B
 */
void matmatStrided(double *C, const double *A, const double *B, int m, int n, int p)
{
  memset(C, 0, m * n * sizeof(double));

  for (size_t i = 0; i < m; i++)
    for (size_t j = 0; j < n; j++) {
      double temp = 0;
      for (size_t k = 0; k < p; k++)
        temp += A[k*m + i] * B[j*p + k];
      C[j*m + i] = temp;
    }
}

/**
 * Perform a matrix-matrix multiplication C = A*B using a linear memory access implementation
 * @param C Pointer to the first element of the m by n matrix C, stored in column major format (output)
 * @param A Pointer to the first element of the m by p matrix A, stored in column major format
 * @param B Pointer to the first element of the p by n matrix B, stored in column major format
 * @param m Number of rows of C and A
 * @param n Number of columns of C and B
 * @param p Number of columns of A, number of rows of B
 */
void matmatLinear(double *C, const double *A, const double *B, int m, int n, int p)
{
  memset(C, 0, m * n * sizeof(double));

  for (size_t j = 0; j < n; j++) {
    for (size_t k = 0; k < p; k++) {
      for (size_t i = 0; i < m; i++) {
        C[j*m + i] += A[k*m + i] * B[j*p + k];
      }
    }
  }
}

/**
 * Perform a matrix-matrix multiplication C = A*B using the BLAS
 * @param C Pointer to the first element of the m by n matrix C, stored in column major format (output)
 * @param A Pointer to the first element of the m by p matrix A, stored in column major format
 * @param B Pointer to the first element of the p by n matrix B, stored in column major format
 * @param m Number of rows of C and A
 * @param n Number of columns of C and B
 * @param p Number of columns of A, number of rows of B
 */
void matmatBLAS(double *C, const double *A, const double *B, int m, int n, int p)
{
  const char transA = 'N', transB = 'N';
  const double alpha = 1.0, beta = 0.0;

  dgemm_(&transA, &transB, &m, &n, &p, &alpha, A, &m, B, &p, &beta, C, &m);
}

/**
 * Perform a matrix-matrix multiplication C = A*B using a blocked implementation (temporal locality)
 * @param C Pointer to the first element of the m by n matrix C, stored in column major format (output)
 * @param A Pointer to the first element of the m by p matrix A, stored in column major format
 * @param B Pointer to the first element of the p by n matrix B, stored in column major format
 * @param m Number of rows of C and A
 * @param n Number of columns of C and B
 * @param p Number of columns of A, number of rows of B
 */
void matmatBlocked(double *C, const double *A, const double *B, int m, int n, int p)
{
  memset(C, 0, m * n * sizeof(double));

  /* Loop over the blocks */
  for(size_t x = 0; x < n; x += BLOCK_SIZE) {
    for(size_t y = 0; y < m; y += BLOCK_SIZE) {

      for (size_t j = 0; j < n; j++) {

        /* Use the MIN function here for edge cases! */
        for (size_t k = y; k < MIN(m, y+BLOCK_SIZE); k++) {
          double temp = B[j*p + k]; /* This element doesn't change anymore so we can save it in a register */
          for (size_t i = x; i < MIN(n, x+BLOCK_SIZE); i++) {
            C[j*m + i] += A[k*m + i] * temp;
          }
        }

      }

    }
  }

}

int main(int argc, char* argv[])
{
  const size_t numExp = 1;
  const size_t m = 2000, n = 2000, p = 2000;

  double *C = new double[m*n];
  double *A = new double[m*p];
  double *B = new double[p*n];

  // fill in the elements of A
  for (size_t i = 0; i < m*p; i++)
    A[i] = i;

  // fill in the elements of B
  for (size_t i = 0; i < p*n; i++)
    B[i] = i;

  double flops = 2 * numExp * m * n * p;

  startChrono();
  for (size_t i = 0; i < numExp; i++)
    matmatStrided(C, A, B, m, n, p);
  cout << "FLOPS/s for a non-contiguous access matrix-matrix multiplication: " << flops / stopChrono() << endl;

  startChrono();
  for (size_t i = 0; i < numExp; i++)
    matmatLinear(C, A, B, m, n, p);
  cout << "FLOPS/s for a contiguous access matrix-matrix multiplication: " << flops / stopChrono() << endl;

  startChrono();
  for (size_t i = 0; i < numExp; i++)
    matmatBLAS(C, A, B, m, n, p);
  cout << "FLOPS/s for a BLAS matrix-matrix multiplication: " << flops / stopChrono() << endl;

  startChrono();
  for (size_t i = 0; i < numExp; i++)
    matmatBlocked(C, A, B, m, n, p);
  cout << "FLOPS/s for a blocked matrix-matrix multiplication: " << flops / stopChrono() << endl;

  delete [] A;
  delete [] B;
  delete [] C;

  exit(EXIT_SUCCESS);
}
