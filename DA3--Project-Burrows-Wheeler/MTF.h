/* 
 * File:   MTF.h
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#ifndef MTF_H
#define MTF_H

void mtf_encode(bwt_transformation *bwt_transformed_block, unsigned int factor);
void mtf_decode(unsigned char *mtf_encoded, unsigned int blocksize, unsigned int factor);
unsigned char* init_alphabet();

#endif /*MTF_H*/

