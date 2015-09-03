/* 
 * File:   IO.h
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#ifndef IO_H
#define IO_H

/* Write methods */
void write_algorithm_number(unsigned char algorithm_number);

void write_start_index(unsigned int start_index);

void write_frequency_table(unsigned int *frequency_table);
void write_number_of_huffman_bytes(unsigned int bits_written);
void write_bytes(unsigned char* bytes, unsigned int bytes_written);
void write_number_of_flush_bits(unsigned char number_flush_bits);

/* Read methods */
unsigned char read_algorithm_number();

unsigned int read_start_index(unsigned int *start_index);

void read_frequency_table(unsigned int *frequency_table);
unsigned int read_number_of_huffman_bytes();
void read_huffman_bytes(unsigned char *huffman_bytes, unsigned int number_of_huffman_bytes);
unsigned char read_number_flush_bits();

#endif /*IO_H*/

