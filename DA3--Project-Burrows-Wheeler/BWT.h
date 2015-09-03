/* 
 * File:   BWT.h
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#ifndef BWT_H
#define BWT_H

typedef struct bwt_transformation {
	unsigned int start_index;
	unsigned int blocksize;
	unsigned char *result;
} bwt_transformation;

bwt_transformation* encode(unsigned int blocksize, unsigned char *original);
int compare_cylic_string(const void *a, const void *b);


unsigned char* decode(unsigned int start_index, unsigned int blocksize, unsigned char *input);
int compare_char(const void *a, const void *b);

#endif /*BWT_H*/

