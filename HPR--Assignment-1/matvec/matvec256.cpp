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

using namespace std;

// ==========================================================================
// FUNCTION PROTOTYPE
// ==========================================================================

// double generalized matrix-vector product y = alpha * Ax + beta * y (BLAS)
extern "C" void dgemv_(const char *trans,    // 'N' for normal product, 'T' for transpose of A
		       const int *m,         // number of rows of A
		       const int *n,         // number of columns of A
		       const double *alpha,  // scalar value
		       const double *A,      // pointer to the first element of A
		       const int *LDA,       // leading dimension of A
		       const double *x,      // pointer to the first element of x
		       const int *incx,      // increment of x
		       const double *beta,   // scalar value
		       double *y,            // pointer to the first element of y
		       const int *incy);     // increment of y

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

/**
 * Perform a matrix-vector multiplication y = Ax using strided memory access
 * @param A Pointer to the first element of the m by n matrix A, stored in column major format
 * @param x Pointer to the first element of vector x (size n)
 * @param y Pointer to the first element of vector y (size m) (output)
 * @param m Number of rows in A, size of vector y
 * @param n Number of columns in A, size of vector x
 */
void matvecStrided(const double *A, const double *x, double *y, int m, int n)
{
	for (size_t i = 0; i < m; i++) {
		double temp = 0;
		for (size_t j = 0; j < n; j++)
			temp += A[j*m + i] * x[j];
		y[i] = temp;
	}
}

/**
 * Perform a matrix-vector multiplication y = Ax using linear memory access
 * @param A Pointer to the first element of the m by n matrix A, stored in column major format
 * @param x Pointer to the first element of vector x (size n)
 * @param y Pointer to the first element of vector y (size m) (output)
 * @param m Number of rows in A, size of vector y
 * @param n Number of columns in A, size of vector x
 */
void matvecLinear(const double *A, const double *x, double *y, int m, int n)
{
	memset(y, 0, m * sizeof(double));

	for (size_t j = 0; j < n; j++)
		for (size_t i = 0; i < m; i++)
			y[i] += A[j*m + i] * x[j];
}

/**
 * Perform a matrix-vector multiplication y = Ax using the BLAS
 * @param A Pointer to the first element of the m by n matrix A, stored in column major format
 * @param x Pointer to the first element of vector x (size n)
 * @param y Pointer to the first element of vector y (size m) (output)
 * @param m Number of rows in A, size of vector y
 * @param n Number of columns in A, size of vector x
 */
void matvecBLAS(const double *A, const double *x, double *y, int m, int n)
{
	const int inc = 1;
	const double alpha = 1.0;
	const double beta = 0.0;
	char trans = 'N';

	dgemv_(&trans, &m, &n, &alpha, A, &m, x, &inc, &beta, y, &inc);
}

int main(int argc, char* argv[])
{
	// input parameters
	const size_t numExp = 1000;  // number of repeats
	const size_t m = 256, n = 256;  // matrix dimensions

	double flops = m * n * 2 * numExp;

	double *A = new double[m*n];
	double *y = new double[m];
	double *x = new double[n];

	// fill in the elements of x
	for (size_t i = 0; i < n; i++)
		x[i] = i;

	// fill in the elements of A -> A(i,j) = i * j
	// column-major format
	for (size_t j = 0; j < n; j++)
		for (size_t i = 0; i < m; i++)
			A[j*m + i] = i * j;

        startChrono();
	for (size_t i = 0; i < numExp; i++)
		matvecStrided(A, x, y, m, n);
	cout << "Flops/s for a " << m << " x " << n << " strided memory access matrix-vector multiplication: " << flops / stopChrono() << endl;

	/* startChrono(); */
        /* for (size_t i = 0; i < numExp; i++) */
                /* matvecLinear(A, x, y, m, n); */
	/* cout << "Flops/s for a " << m << " x " << n << " linear memory access matrix-vector multiplication: " << flops / stopChrono() << endl; */

	/* startChrono(); */
	/* for (size_t i = 0; i < numExp; i++) */
	/* 	matvecBLAS(A, x, y, m, n); */
	/* cout << "Flops/s for a " << m << " x " << n << " BLAS-based matrix-vector multiplication: " << flops / stopChrono() << endl; */

	delete [] A;
	delete [] y;
	delete [] x;

	exit(EXIT_SUCCESS);
}
