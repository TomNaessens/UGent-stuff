/* 
 * File:   IO.c
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#include <stdio.h>
#include <stdlib.h>

#include "IO.h"

/* Write functions */
void write_algorithm_number(unsigned char algorithm_number)
{
	fwrite(&algorithm_number, sizeof (unsigned char), 1, stdout);
}

void write_start_index(unsigned int start_index)
{
	fwrite(&start_index, sizeof (unsigned int), 1, stdout);
}

void write_frequency_table(unsigned int* frequency_table)
{
	fwrite(frequency_table, sizeof (unsigned int), 256, stdout);
}

void write_number_of_huffman_bytes(unsigned int bytes_written)
{
	fwrite(&bytes_written, sizeof (unsigned int), 1, stdout);
}

void write_bytes(unsigned char* bytes, unsigned int bytes_written)
{
	fwrite(bytes, sizeof (unsigned char), bytes_written, stdout);
}

void write_number_of_flush_bits(unsigned char number_flush_bits)
{
	fwrite(&number_flush_bits, sizeof (unsigned char), 1, stdout);
}

/* Read functions */
unsigned char read_algorithm_number()
{
	unsigned char algorithm_number;
	fread(&algorithm_number, sizeof (unsigned char), 1, stdin);
	return algorithm_number;
}

unsigned int read_start_index(unsigned int *start_index)
{
	unsigned int bytes_read;
	bytes_read = fread(start_index, sizeof (unsigned int), 1, stdin);
	return bytes_read;
}

unsigned int read_number_of_huffman_bytes()
{
	unsigned int huffman_bytes;
	fread(&huffman_bytes, sizeof (unsigned int), 1, stdin);
	return huffman_bytes;
}

void read_frequency_table(unsigned int *frequency_table)
{
	fread(frequency_table, sizeof (unsigned int), 256, stdin);
}

void read_huffman_bytes(unsigned char *huffman_bytes, unsigned int number_of_huffman_bytes)
{
	fread(huffman_bytes, sizeof (unsigned char), number_of_huffman_bytes, stdin);
}

unsigned char read_number_flush_bits()
{
	unsigned char number_flush_bits;
	fread(&number_flush_bits, sizeof (unsigned char), 1, stdin);
	return number_flush_bits;
}