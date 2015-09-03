/***************************************************************************
 *   Copyright (C) 2012, 2013 Jan Fostier (jan.fostier@intec.ugent.be)     *
 *   Based upon ideas by Georg Hager and Gerhard Wellein                   *
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

using namespace std;

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

void vectorTriad(double * __restrict a, 
                 const double * __restrict b, 
                 const double * __restrict c, 
                 const double * __restrict d,
	         size_t N)
{
	a = (double*)__builtin_assume_aligned(a, 32);
	b = (double*)__builtin_assume_aligned(b, 32);
	c = (double*)__builtin_assume_aligned(c, 32);
	d = (double*)__builtin_assume_aligned(d, 32);

        for (size_t i = 0; i < N; i++)
		a[i] = b[i] + c[i] * d[i];
}

int main(int argc, char* argv[])
{
	const size_t numExp = 22;
	size_t N = 1;
	size_t nIter = 256 << numExp;

	double *a, *b, *c, *d;
	
	// allocate aligned memory
	posix_memalign(((void**)(&a)), 32, (N << numExp) * sizeof(double));
	posix_memalign(((void**)(&b)), 32, (N << numExp) * sizeof(double));
	posix_memalign(((void**)(&c)), 32, (N << numExp) * sizeof(double));
	posix_memalign(((void**)(&d)), 32, (N << numExp) * sizeof(double));
	
	for (size_t i = 0; i < N << numExp; i++)
		a[i] = b[i] = c[i] = d[i] = i;

	for (size_t i = 0; i < numExp; i++) {
		startChrono();
		for (size_t n = 0; n < nIter; n++) {
			vectorTriad(a, b, c, d, N);

			if (a == NULL)  // this is never true!
				cout << endl;
		}
		double elapsed = stopChrono();

		cout << "Time for vector triad with size: " << N << ": " << elapsed << "s" << endl;

		N *= 2;
		nIter /= 2;
	}

	free(a);
	free(b);
	free(c);
	free(d);

	exit(EXIT_SUCCESS);
}
