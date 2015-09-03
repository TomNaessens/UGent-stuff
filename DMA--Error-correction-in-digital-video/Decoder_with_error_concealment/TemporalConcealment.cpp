#include "TemporalConcealer.h"

#include <iostream>
#include <stdlib.h>

Macroblock* get_shifted_mb(Frame* frame, Frame* referenceFrame, Macroblock* mb, MotionVector* mv)
{
	// If the motion compensated MB lies outside the frame, return NULL
	if( 0 > mb->getXPos()*MACRO_WIDTH + mv->x 
		|| mb->getXPos()*MACRO_WIDTH + MACRO_WIDTH  + mv->x >= frame->getWidth()*16
        || 0 > mb->getYPos()*MACRO_WIDTH + mv->y
		|| mb->getYPos()*MACRO_WIDTH + MACRO_WIDTH  + mv->y >= frame->getHeight()*16)
	{
		return NULL;
	} 

	// Create a new macroblock with the old information
	Macroblock* new_macroblock = new Macroblock(mb->getMBNum(), mb->getXPos(), mb->getYPos());
	new_macroblock->mv = *mv;

	// Loop over the macroblock
	for(int x = 0; x < MACRO_WIDTH; x++)
	{
		for(int y = 0; y < MACRO_HEIGHT; y++)
		{
			// Get the absolute x and y values corresponding with the motion compensated pixels in the old frame
			int x_in_frame = mb->getXPos() * MACRO_WIDTH + x + mv->x;
			int y_in_frame = mb->getYPos() * MACRO_HEIGHT + y + mv->y;

			// Get the corresponding macroblock from the reference frame
			Macroblock* reference_block = referenceFrame->getMacroblock(y_in_frame/16 * frame->getWidth() + x_in_frame/16);

			// Put the luma, cr and br in the new macroblock 
			new_macroblock->luma[x][y] = reference_block->luma[x_in_frame % MACRO_WIDTH][y_in_frame % MACRO_HEIGHT];
			if(!(x_in_frame % 2) && !(y_in_frame % 2))
			{
				new_macroblock->cb[x/2][y/2] = reference_block->cb[(x_in_frame % 16) / 2][(y_in_frame % 16) / 2];
				new_macroblock->cr[x/2][y/2] = reference_block->cr[(x_in_frame % 16) / 2][(y_in_frame % 16) / 2];
			}
		}
	}

	return new_macroblock;
}

int calc_bounding_match_error(Frame* frame, Macroblock* mb) {
	int width = frame->getWidth();
	int height = frame->getHeight();

	// Checking for edges
	bool is_top = (mb->getMBNum()   / width == 0);
	bool is_left = (mb->getMBNum()  % width == 0);
	bool is_right = (mb->getMBNum() % width == width-1);
	bool is_bot = (mb->getMBNum()   / width == height-1);

	int error = 0;
	
	if(!is_top)
	{
		for(int i = 0; i < MACRO_WIDTH; i++)
		{
			Macroblock* mb_above = frame->getMacroblock(mb->getMBNum() - frame->getWidth());
			error += abs(mb_above->luma[15][i] - mb->luma[0][i]);
		}
	}

	
	if(!is_left)
	{		
		for(int i = 0; i < MACRO_HEIGHT; i++)
		{
			Macroblock* mb_left = frame->getMacroblock(mb->getMBNum() - 1);
			error += abs(mb_left->luma[i][15] - mb->luma[i][0]);
		}
	}

	
	if(!is_right)
	{		
		for(int i = 0; i < MACRO_HEIGHT; i++)
		{
			Macroblock* mb_below = frame->getMacroblock(mb->getMBNum() + 1);
			error += abs(mb_below->luma[i][0] - mb->luma[i][15]);
		}
	}

	
	if(!is_bot)
	{		
		for(int i = 0; i < MACRO_WIDTH; i++)
		{
			Macroblock* mb_below = frame->getMacroblock(mb->getMBNum() + frame->getWidth());
			error += abs(mb_below->luma[0][i] - mb->luma[15][i]);
		}
	}

	return error;
}

/**
 * Deep copies the data from the source macroblock to the
 * destination macroblock
 */
void copy_mb(Macroblock* source, Macroblock* destination) 
{
	// Loop over the pixels
	for(int x = 0; x < MACRO_WIDTH; x++)
	{
		for(int y = 0 ; y < MACRO_HEIGHT; y++)
		{
			// Copy the luma
			destination->luma[y][x] = source->luma[y][x];

			// If x and y are even, copy the cb and cr too
			if(!(x % 2) && !(y % 2)){
				destination->cb[y/2][x/2] = source->cb[y/2][x/2];
				destination->cr[y/2][x/2] = source->cr[y/2][x/2];
			}
		}
	}
}