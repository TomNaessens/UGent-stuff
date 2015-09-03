/* 
 * File:   BWT.c
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#include <stdlib.h>
#include <stdio.h>
#include "BWT.h"

unsigned char *original;
unsigned int inputsize;

bwt_transformation* encode(unsigned int blocksize, unsigned char *input)
{

	bwt_transformation* transformation =
		  (bwt_transformation*) malloc(sizeof (bwt_transformation));
	unsigned int *indexes =
		  (unsigned int*) malloc(sizeof (unsigned int) * blocksize);
	transformation->result =
		  (unsigned char*) malloc(sizeof (unsigned char) * blocksize);

	register unsigned int i;

	/* Global vars: we want to use this in our compare_cylic_string function */
	original = input;
	inputsize = blocksize;

	for (i = 0; i < blocksize; i++)
	{
		indexes[i] = blocksize - i - 1;
	}

	/* Sort the indexes with our own compare function */
	qsort(indexes, blocksize, sizeof (unsigned int), compare_cylic_string);

	/** 
	 * We init the start_index as 0, to solve the blocksize = 1 bug, where the index would not
	 * get assigned and returned garbage
	 */
	transformation->start_index = 0;

	transformation->blocksize = blocksize;

	for (i = 0; i < blocksize; i++)
	{
		transformation->result[i] = input[(indexes[i] + blocksize - 1) % blocksize];

		if (indexes[i] == 1) // 1, niet 0, want in de laatste kolom staat het eerste karakter op rij 1
		{
			transformation->start_index = i;
		}
	}

	free(indexes);

	return transformation;

}

int compare_cylic_string(const void *a, const void *b)
{

	unsigned int i1 = *((const unsigned int*) a);
	unsigned int i2 = *((const unsigned int*) b);

	unsigned int start_index = i1;

	while (original[i1 % inputsize] == original[i2 % inputsize])
	{
		i1++;
		i2++;

		if (start_index == i1 % inputsize)
		{
			return 0;
		}
	}

	return original[i1 % inputsize] - original[i2 % inputsize];

}

unsigned char* decode(unsigned int start_index, unsigned int blocksize, unsigned char *input)
{
	unsigned int *indexes =
		  (unsigned int*) malloc(sizeof (unsigned int) * blocksize);
	unsigned char *result =
		  (unsigned char*) malloc(sizeof (unsigned char) * blocksize);
	unsigned int index;
	register unsigned int i;

	/* Global vars: we want to use this in our compare_char function */
	original = input;

	for (i = 0; i < blocksize; i++)
	{
		indexes[i] = i;
	}

	qsort(indexes, blocksize, sizeof (unsigned int), compare_char);

	/**
	 * Getting the original text back
	 */
	index = start_index;
	for (int i = 0; i < blocksize; i++)
	{
		result[i] = input[index];
		index = indexes[index];
	}

	free(indexes);
	free(input);

	return result;

}

int compare_char(const void *a, const void *b)
{

	unsigned int i1 = *((const unsigned int*) a);
	unsigned int i2 = *((const unsigned int*) b);
	
	return original[i1] - original[i2];
}