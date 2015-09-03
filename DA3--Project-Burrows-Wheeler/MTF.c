/* 
 * File:   mtf.c
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#include <stdlib.h>
#include <stdio.h>
#include "BWT.h"
#include "MTF.h"

void mtf_encode(bwt_transformation *bwt_transformed_block, unsigned int factor)
{
	unsigned int i;
	unsigned int new_index;
	unsigned char* alphabet = init_alphabet();
	unsigned int blocksize = bwt_transformed_block->blocksize;
	unsigned char *to_encode = bwt_transformed_block->result;

	for (i = 0; i < blocksize; i++)
	{

		int k;
		unsigned char buffer;
		unsigned int j = 0;

		/* We search the character in the list */
		while (to_encode[i] != alphabet[j])
		{
			j++;
		}

		/* Save it for future use */
		buffer = alphabet[j];

		if (factor == 0)
		{
			new_index = 0;
		}
		else
		{
			new_index = j / factor;
		}

		/* Shift the list */
		for (k = j; k > new_index; k--)
		{
			alphabet[k] = alphabet[k - 1];
		}

		/* And overwrite the one in the front */
		alphabet[new_index] = buffer;

		to_encode[i] = j;

	}

	free(alphabet);

}

void mtf_decode(unsigned char *mtf_encoded, unsigned int blocksize, unsigned int factor)
{
	unsigned char* alphabet = init_alphabet();
	unsigned int i;
	unsigned int j;
	unsigned int new_index;
	unsigned char buffer;

	for (i = 0; i < blocksize; i++)
	{
		buffer = alphabet[mtf_encoded[i]];

		if(factor) {
			new_index = mtf_encoded[i] / factor;
		} else {
			new_index = 0;
		}
		
		/* Shift the list */
		for (j = mtf_encoded[i]; j > new_index; j--)
		{
			alphabet[j] = alphabet[j - 1];
		}

		alphabet[new_index] = buffer;
		mtf_encoded[i] = buffer;
	}

	free(alphabet);
}

unsigned char* init_alphabet()
{

	unsigned char *alphabet = (unsigned char*) malloc(256 * sizeof (unsigned char));
	unsigned int i;

	/* Initialisation of the alphabet */
	for (i = 0; i < 256; i++)
	{
		alphabet[i] = i;
	}

	return alphabet;

}