/* 
 * File:   Huffman.c
 * Author: Tom Naessens 
 *	     Tom.Naessens@UGent.be
 *         3de Bachelor Informatica
 *         Universiteit Gent
 * 
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <string.h>

#include "IO.h"
#include "Huffman.h"
#include "BitWriter.h"

void huffman_encode(unsigned char *mtf_transformation, unsigned int blocksize)
{
	unsigned int i = 0;
	unsigned int j = 0;
	unsigned int *frequency_table = (unsigned int*) calloc(256, sizeof (unsigned int));

	unsigned int huffman_size = 0;
	node **node_table = NULL;

	node *root = NULL;
	unsigned int* base_code = (unsigned int*) calloc(8, sizeof (unsigned int));
	code_entry *code_table = NULL;

	/* Create the frequency table */
	create_frequency_table(frequency_table, mtf_transformation, blocksize);

	/* Nodes is what we want! */

	/* how much do we need? */
	for (i = 0; i < 256; i++)
	{
		if (frequency_table[i])
			j++;
	}
	node_table = (node**) malloc(sizeof (node*) * j);

	for (i = 0; i < 256; i++)
	{
		if (frequency_table[i]) /* But we don't want any zero nodes */
		{
			/* Create the node */
			node* new_node = (node*) malloc(sizeof (node));
			new_node->freq = frequency_table[i];
			new_node->letter = i;
			new_node->left = NULL;
			new_node->right = NULL;

			/* Add it */
			huffman_size++;
			node_table[huffman_size - 1] = new_node;
		}
	}

	/* Write the FT to a file */
	write_frequency_table(frequency_table);

	/* Create the Huffman tree */
	root = create_huffman_tree(node_table, huffman_size);

	/* Iterate the Huffman tree and define the bits for the frequency table */
	code_table = (code_entry*) calloc(256, sizeof (code_entry));
	generate_codes(root, base_code, 0, code_table);


	/* iterate the array, look the bits up and print them bitwise */
	for (i = 0; i < blocksize; i++)
	{
		for (int j = 0; j < code_table[mtf_transformation[i]].depth / 32 + 1; j++)
		{
			make_into_bits(code_table[mtf_transformation[i]].code[j], code_table[mtf_transformation[i]].depth);
		}

	}

	fill_bit(); /* We want to fill the last bit with zeroes so it will be printed too! */

	/***********/
	/* Cleanup */
	/***********/

	free_tree(root);

	for (i = 0; i < 256; i++)
	{
		free(code_table[i].code);
	}
	free(code_table);

	free(node_table);


	free(frequency_table);

}

unsigned char* huffman_decode(unsigned int *frequency_table, unsigned int number_of_huffman_bytes,
	  unsigned char *huffman_bytes, unsigned int *blocksize, unsigned char number_flush_bits)
{
	unsigned int i;
	unsigned int j = 0;
	unsigned int array_size = 10;
	unsigned int huffman_size = 0;
	node *root = NULL;
	node **node_table = NULL;
	unsigned char* mtf_encoded = (unsigned char*) malloc(array_size * sizeof (unsigned char));

	/* Create the tree again: how much do we need? */
	for (i = 0; i < 256; i++)
	{
		if (frequency_table[i])
			j++;
	}
	node_table = (node**) malloc(sizeof (node*) * j);

	/* Node table */
	for (i = 0; i < 256; i++)
	{
		if (frequency_table[i]) /* But we don't want any zero nodes */
		{
			/* Create the node */
			node* new_node = (node*) malloc(sizeof (node));
			new_node->freq = frequency_table[i];
			new_node->letter = i;
			new_node->left = NULL;
			new_node->right = NULL;

			/* Add it */
			huffman_size++;
			node_table[huffman_size - 1] = new_node;
		}
	}

	/* Fold the table */
	root = create_huffman_tree(node_table, huffman_size);

	/* Iterate the the Huffman byte array */

	node* current_node = root;

	for (i = 0; i < number_of_huffman_bytes; i++)
	{
		unsigned char j = 0;
		unsigned char max = 8;


		if (i == number_of_huffman_bytes - 1)
		{
			max = 8 - number_flush_bits;
		}

		for (j = 0; j < max; j++)
		{

			int bit = (huffman_bytes[i] & (1 << 7 - j)) >> 7 - j;

			if (bit == 0)
			{ //0: ga naar links
				current_node = current_node->left;
			}
			else
			{ // 1: ga naar rechts
				current_node = current_node->right;
			}

			if (current_node->left == NULL & current_node->right == NULL)
			{
				(*blocksize)++;
				if (*blocksize > array_size)
				{
					array_size *= 2;
					mtf_encoded = (unsigned char*) realloc(mtf_encoded, array_size * sizeof (unsigned char));
				}

				mtf_encoded[*blocksize - 1] = current_node->letter;
				current_node = root;
			}

		}
	}

	mtf_encoded = (unsigned char*) realloc(mtf_encoded, *blocksize * sizeof (unsigned char));

	/* Clean it up */
	free_tree(root);
	free(node_table);

	return mtf_encoded;
}

void make_into_bits(unsigned int val, unsigned char bits)
{
	for (int i = 0; i < bits; i++)
	{
		add_bit((val & (1 << 31 - i)) >> 31 - i);
	}
}

void create_frequency_table(unsigned int *frequency_table, unsigned char *mtf_transformation, unsigned int blocksize)
{
	unsigned int i;
	for (i = 0; i < blocksize; i++)
	{
		frequency_table[mtf_transformation[i]]++;
	}
}

node* create_huffman_tree(node** node_table, int huffman_size)
{
	int i;
	while (huffman_size > 1)
	{
		qsort(node_table, huffman_size, sizeof (node*), compare_node);

		node_table[huffman_size - 2] = combine_nodes(node_table[huffman_size - 2], node_table[huffman_size - 1]);

		huffman_size--;
	}
	return node_table[0];
}

int compare_node(const void *a, const void *b)
{
	node **node1 = (node **) a;
	node **node2 = (node **) b;

	return (*node1)->freq < (*node2)->freq;
}

node* combine_nodes(node* left, node* right)
{
	node* parent = (node*) malloc(sizeof (node));

	parent->freq = left->freq + right->freq;
	parent->letter = 0;
	parent->left = left;
	parent->right = right;

	return parent;
}

void generate_codes(node* node, unsigned int *current_code, unsigned char depth, code_entry *code_table)
{
	/* We actually don't have to check for the right part because if the left is NULL, the 
	 * right automatically is too. I wrote it here for clarification, but it won't matter in 
	 * performance due to short-circuiting.
	 */
	if (node->left == NULL && node->right == NULL)
	{
		/* We reached a leaf, add it to the code_table! */
		code_entry entry;
		entry.code = current_code;
		entry.depth = depth;

		code_table[node->letter] = entry;
	}
	else
	{
		/* We reached an inner node, split up! */
		unsigned int *left_code = (unsigned int*) malloc(8 * sizeof (unsigned int));
		memcpy(left_code, current_code, 8 * sizeof (unsigned int));

		generate_codes(node->left, left_code, depth + 1, code_table);

		unsigned int *right_code = (unsigned int*) malloc(8 * sizeof (unsigned int));
		memcpy(right_code, current_code, 8 * sizeof (unsigned int));

		/* We need to add the one here, because we go right */
		right_code[depth / 32] = right_code[depth / 32] | 1 << (31 - depth % 32);

		generate_codes(node->right, right_code, depth + 1, code_table);

		free(current_code);
	}
}

void free_tree(node* root)
{
	if (root->left != NULL && root->right != NULL)
	{
		free_tree(root->left);
		free_tree(root->right);
	}
	free(root);

}