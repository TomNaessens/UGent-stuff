/* 
 * File:   main.c
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#define MAGIC 8

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "BWT.h"
#include "MTF.h"
#include "Huffman.h"
#include "IO.h"

/*
 * 
 */
int main(int argc, char** argv)
{
	if (argc == 1)
	{
		fprintf(stderr, "Please provide the needed arguments.\n");
		return 1;
	}

	/* Decode! */
	if (strcmp(argv[1], "decodeer") == 0)
	{
		unsigned char algorithm_number;

		unsigned int *start_index = (unsigned int*) malloc(sizeof (unsigned int));

		unsigned int *frequency_table;
		unsigned int number_of_huffman_bytes;
		unsigned char *huffman_bytes = NULL;
		unsigned char number_flush_bits;

		algorithm_number = read_algorithm_number();

		if (algorithm_number == 1 || algorithm_number == 3)
		{
			while (read_start_index(start_index))
			{
				/* Read everything! */
				frequency_table = (unsigned int*) calloc(256, sizeof (unsigned int));
				read_frequency_table(frequency_table);

				number_of_huffman_bytes = read_number_of_huffman_bytes();

				huffman_bytes = (unsigned char*)
					  malloc(number_of_huffman_bytes * sizeof (unsigned char));
				read_huffman_bytes(huffman_bytes, number_of_huffman_bytes);
				number_flush_bits = read_number_flush_bits();

				/* Decode it */
				unsigned char* mtf_encoded = NULL;
				unsigned int* blocksize = (unsigned int*) malloc(sizeof (unsigned int));
				unsigned char* result = NULL;
				*blocksize = 0;

				mtf_encoded = huffman_decode(frequency_table, number_of_huffman_bytes, huffman_bytes, blocksize, number_flush_bits);

				if (algorithm_number == 3)
				{
					mtf_decode(mtf_encoded, *blocksize, MAGIC);
				}
				else
				{
					mtf_decode(mtf_encoded, *blocksize, 0);
				}

				result = decode(*start_index, *blocksize, mtf_encoded);

				/* Print it */
				write_bytes(result, *blocksize);

				/* And clean it up. */
				free(result);
				free(huffman_bytes);
				free(frequency_table);
				free(blocksize);
			}

			free(start_index);

		}
		else
		{
			fprintf(stderr, "Algorithm not implemented!\n");
			return 1;
		}

	}

		/* Encode! */
	else if (strcmp(argv[1], "encodeer") == 0)
	{
		if (argc == 4)
		{
			unsigned int bytes_read;
			unsigned int blocksize = atoi(argv[3]) * 1000;
			unsigned char algorithm_number = atoi(argv[2]);
			unsigned char *buffer = (unsigned char*) malloc(blocksize * sizeof (unsigned char));

			/* File header */
			write_algorithm_number(algorithm_number);

			while (bytes_read = fread(buffer, sizeof (unsigned char), blocksize, stdin))
			{
				bwt_transformation *bwt_transformed_block;

				bwt_transformed_block = encode(bytes_read, buffer);

				if (algorithm_number == 1 || algorithm_number == 3)
				{
					write_start_index(bwt_transformed_block->start_index);
					if (algorithm_number == 3)
					{
						mtf_encode(bwt_transformed_block, MAGIC);
					}
					else
					{
						mtf_encode(bwt_transformed_block, 0);
					}
					huffman_encode(bwt_transformed_block->result, bwt_transformed_block->blocksize);

				}
				else
				{
					fprintf(stderr, "Algorithm not implemented!\n");
					return 1;
				}

				free(bwt_transformed_block->result);
				free(bwt_transformed_block);
			}

			free(buffer);

		}
		else
		{
			fprintf(stderr, "Wrong number of arguments.\n");
			return 1;
		}
	}
	else
	{
		fprintf(stderr, "Wrong arguments!\n");
		return 1;
	}

	return (EXIT_SUCCESS);
}