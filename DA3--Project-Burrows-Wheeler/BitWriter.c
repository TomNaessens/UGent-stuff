/* 
 * File:   BitWriter.c
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#include <stdio.h>
#include <stdlib.h>

#include "IO.h"
#include "BitWriter.h"

unsigned char current_bit = 0;
unsigned char byte = 0;
unsigned int array_size = 10;
unsigned char* to_write = NULL;
unsigned int bytes_written = 0;

void add_bit(unsigned char bit)
{
	if (bit)
	{
		byte = byte | (1 << 7 - current_bit);
	}

	current_bit++;

	if (current_bit == 8)
	{
		if(bytes_written == 0) {
			to_write = (unsigned char*) malloc(array_size * sizeof(unsigned char));
		}
		
		bytes_written++;
		
		if (bytes_written > array_size)
		{
			array_size *= 2;
			to_write = (unsigned char*) realloc(to_write, array_size * sizeof (unsigned char));
		}

		to_write[bytes_written - 1] = byte;

		current_bit = 0;
		byte = 0;
	}
}

void fill_bit(void)
{
	unsigned char number_flush_bits = 0;
	while (current_bit != 0)
	{
		number_flush_bits++;
		add_bit(0);
	}

	write_number_of_huffman_bytes(bytes_written);
	write_bytes(to_write, bytes_written);
	write_number_of_flush_bits(number_flush_bits);

	bytes_written = 0;
	free(to_write);
	to_write = NULL;
}