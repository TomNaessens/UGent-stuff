/* 
 * File:   Huffman.h
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#ifndef HUFFMAN_H
#define HUFFMAN_H

typedef struct node {
	unsigned int freq;
	unsigned char letter;
	struct node *left;
	struct node *right;
} node;

typedef struct code_entry {
	unsigned int* code;
	unsigned char depth;
} code_entry;

void huffman_encode(unsigned char *mtf_transformation, unsigned int size);
unsigned char* huffman_decode(unsigned int *frequency_table, unsigned int number_of_huffman_bytes,
	  unsigned char *huffman_bytes, unsigned int *blocksize, unsigned char number_flush_bits);
void create_frequency_table(unsigned int *frequency_table, unsigned char *mtf_transformation, unsigned int blocksize);
node* create_huffman_tree(node** node_table, int huffman_size);
int compare_node(const void *a, const void *b);
node* combine_nodes(node* left, node* right);
void generate_codes(node* node, unsigned int *current_code, unsigned char depth, code_entry *code_table);
void free_tree(node* root);
void make_into_bits(unsigned int val, unsigned char bits);
#endif /*HUFFMAN_H*/

