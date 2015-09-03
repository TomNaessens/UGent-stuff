#include "ErrorConcealer.h"
#include <stdio.h>
#include <iostream>

#include <vector>
#include <stdlib.h>
#include <math.h>
#include <limits.h>
#include "SpatialConcealer.h"
#include "TemporalConcealer.h"


ErrorConcealer::ErrorConcealer(short conceal_method)
{
	this->conceal_method = conceal_method;
}

ErrorConcealer::~ErrorConcealer(void)
{

}

void ErrorConcealer::concealErrors(Frame *frame, Frame *referenceFrame)
{
	switch(conceal_method){
	case 0:
		conceal_spatial_1(frame);
		break;
	case 1:
		conceal_spatial_2(frame);
		break;
	case 2:
		conceal_spatial_3(frame);
		break;
	case 3:
		conceal_temporal_1(frame, referenceFrame);
		break;
	case 4:
		conceal_temporal_2(frame, referenceFrame);
		break;
	case 5:
		conceal_temporal_3(frame, referenceFrame);
		break;
	default:
		printf("\nWARNING: NO ERROR CONCEALMENT PERFORMED! (conceal_method %d unknown)\n\n",conceal_method);
	}
}




	
void ErrorConcealer::conceal_spatial_1(Frame *frame)
	{
		int width = frame->getWidth();
		int height = frame->getHeight();

		// run through all macroblocks
		for(int i=0; i < width*height; i++) {

			Macroblock* mb = frame->getMacroblock(i);

			// check if macroblock is missing

			if(mb->isMissing()) {

				// checking for edges
				bool is_top = (i/width == 0);
				bool is_left = (i%width == 0);
				bool is_bot = (i/width == height-1);
				bool is_right = (i%width == width-1);

				Macroblock* mb_top = NULL;
				Macroblock* mb_left = NULL;
				Macroblock* mb_bot = NULL;
				Macroblock* mb_right = NULL;

				if( !is_top ){
					mb_top = frame->getMacroblock(i-width);
				}
				if( !is_right ){
					mb_right = frame->getMacroblock(i+1);
				}
				if( !is_left ){
					mb_left = frame->getMacroblock(i-1);
				}
				if( !is_bot ){
					mb_bot = frame->getMacroblock(i+width);
				}

				// run through all pixels (luma)

				for(int j=0; j < MACRO_WIDTH; j++) {
					for(int k=0; k < MACRO_HEIGHT; k++) {

						int denominator_luma =0, nominator_luma=0;

						if(mb_top != NULL ){
							nominator_luma += (MACRO_HEIGHT+1-k) * mb_top->luma[MACRO_HEIGHT-1][j];
							denominator_luma += (MACRO_HEIGHT+1-k);
						}
						if(mb_left != NULL){
							nominator_luma += (MACRO_WIDTH+1-j) * mb_left->luma[k][MACRO_WIDTH-1];
							denominator_luma += (MACRO_WIDTH+1-j);
						}
						if(mb_bot != NULL){
							nominator_luma += (k+1) * mb_bot->luma[1][j];
							denominator_luma += (k+1);
						}
						if(mb_right != NULL){
							nominator_luma += (j+1) * mb_right->luma[1][j];
							denominator_luma += (j+1);
						}

						mb->luma[k][j] = nominator_luma/denominator_luma;

					}
				}

				// run through all pixels (cb and cr)
				for(int j=0; j < MACRO_WIDTH/2; j++) {
					for(int k=0; k < MACRO_HEIGHT/2; k++) {

						int denominator_cb =0, nominator_cb=0;
						int denominator_cr =0, nominator_cr=0;

						if(mb_top != NULL ){
							nominator_cb += (MACRO_HEIGHT+1-k) * mb_top->cb[MACRO_HEIGHT/2-1][j];
							denominator_cb += (MACRO_HEIGHT+1-k);

							nominator_cr += (MACRO_HEIGHT+1-k) * mb_top->cr[MACRO_HEIGHT/2-1][j];
							denominator_cr += (MACRO_HEIGHT+1-k);
						}
						if(mb_left != NULL){
							nominator_cb += (MACRO_WIDTH+1-j) * mb_left->cb[k][MACRO_WIDTH/2-1];
							denominator_cb += (MACRO_WIDTH+1-j);

							nominator_cr += (MACRO_WIDTH+1-j) * mb_left->cr[k][MACRO_WIDTH/2-1];
							denominator_cr += (MACRO_WIDTH+1-j);
						}
						if(mb_bot != NULL){
							nominator_cb += (k+1) * mb_bot->cb[1][j];
							denominator_cb += (k+1);

							nominator_cr += (k+1) * mb_bot->cr[1][j];
							denominator_cr += (k+1);
						}
						if(mb_right != NULL){
							nominator_cb += (j+1) * mb_right->cb[1][j];
							denominator_cb += (j+1);

							nominator_cr += (j+1) * mb_right->cr[1][j];
							denominator_cr += (j+1);
						}

						mb->cb[k][j] = nominator_cb/denominator_cb;
						mb->cr[k][j] = nominator_cr/denominator_cr;

					}
				}

				mb->setConcealed();

			}

		}
	}

	void ErrorConcealer::conceal_spatial_2(Frame *frame)
	{
		int width = frame->getWidth();
		int height = frame->getHeight();

		// run through all macroblocks
		for(int i=0; i < width*height; i++) {

			Macroblock* mb = frame->getMacroblock(i);

			// check if macroblock is missing, if so then reconstruct it
			if(mb->isMissing()) {
				spatial_reference_blocks* ref_blocks = getSpatialReferenceBlocks(frame, i);
				spatialRectonstruct(mb, ref_blocks);
				delete(ref_blocks);

				mb->setConcealed();
			}
		}
	}

	void ErrorConcealer::conceal_spatial_3(Frame *frame)
	{
		int width = frame->getWidth();
		int height = frame->getHeight();

		// run through all macroblocks
		for(int i=0; i < width*height; i++) {
			Macroblock* mb = frame->getMacroblock(i);

			if(mb->isMissing()) {
				// Determening the most plausible edge direction of the surrounding macroblocks
				edge_angle ea = calcEdgeAngle(frame, i);
				if(ea.concisiveness > 20){
					spatial_reference_blocks_full* ref_blocks = getSpatialReferenceBlocksFull(frame, i);
					angularReconstruction(frame, i, ref_blocks, ea);
					delete(ref_blocks);
				}
				else{
					spatial_reference_blocks* ref_blocks = getSpatialReferenceBlocks(frame, i);
					spatialRectonstruct(mb, ref_blocks);
					delete(ref_blocks);
				}

				mb->setConcealed();
			}
		}
	}

	/**
	 * This method is straightforward: If a block is missing, copy the block
	 * from the previous frame.
	 */
	void ErrorConcealer::conceal_temporal_1(Frame *frame, Frame *referenceFrame)
	{
		// Loop over all the macroblocks in the frame
		for(int i=0; i < frame->getNumMB(); i++)
		{

			// Get a pointer to the MB
			Macroblock* mb = frame->getMacroblock(i);

			// Let the pointer point to the matching MB from the previous frame
			if(mb->isMissing())
			{
				// Deep copy the block from source to destination
				copy_mb(referenceFrame->getMacroblock(i), frame->getMacroblock(i));
				mb->setConcealed();
			}
		}
	}

	void ErrorConcealer::conceal_temporal_2(Frame *frame, Frame *referenceFrame)
	{
		// To be completed. Add explanatory notes in English.
		int width = frame->getWidth();
		int height = frame->getHeight();

		for(int i=0; i<frame->getNumMB(); i++)
		{
			Macroblock* mb = frame->getMacroblock(i);

			if(mb->isMissing())
			{
				if(frame->is_p_frame())
				{
					
					// Checking for edges
					bool is_top = (i/width == 0);
					bool is_left = (i%width == 0);
					bool is_right = (i%width == width-1);
					bool is_bot = (i/width == height-1);

					/**
					 * Get the motion vectors from the surrounding macroblocks.
					 * If the block lays at the edge of frame, set it to null
					 */					
					std::vector<Macroblock*> blocks; 
					
					if(!is_top) 
					{
						blocks.push_back(frame->getMacroblock(i - width));
					}
					if(!is_left) 
					{
						blocks.push_back(frame->getMacroblock(i - 1));
					}
					if(!is_left) 
					{
						blocks.push_back(frame->getMacroblock(i + 1));
					}
					if(!is_bot) 
					{
						blocks.push_back(frame->getMacroblock(i + width));
					}

					int error = INT_MAX;

					for(std::vector<int>::size_type i = 0; i != blocks.size(); i++) {
						Macroblock* new_mb = get_shifted_mb(frame, referenceFrame, mb, &blocks[i]->mv);

						if(new_mb)
						{
							int new_error = calc_bounding_match_error(frame, new_mb);
							if(new_error < error)
							{
								error = new_error;
								copy_mb(new_mb, mb);
							}

							delete(new_mb);
						}
					}

					if(error == INT_MAX)
					{
						copy_mb(referenceFrame->getMacroblock(i), frame->getMacroblock(i));
					}
					mb->setConcealed();
					
				}
				else
				{
					/**
					 * If the macroblock lost belongs to an intra-coded frame,
					 * no motion vectors are available. In this case, use zero
					 * motion temporal construction can be applied, so we use the
					 * method from conceal_temporal_1 and create a deep copy of 
					 * the macroblok
					 */
					copy_mb(referenceFrame->getMacroblock(i), frame->getMacroblock(i));
				}
			}
		}
	}

	/**
	 * This method is an extension of the previous method:
	 * We no longer can assume the surrounding macroblocks are available so we
	 * run spiral-wise around the missing macroblock, finding a number of other
	 * non-missing blocks. These blocks get compared and the MV with the least
	 * error is chosen.
	 */
	void ErrorConcealer::conceal_temporal_3(Frame *frame, Frame *referenceFrame)
	{
			// To be completed. Add explanatory notes in English.
		int width = frame->getWidth();
		int height = frame->getHeight();

		for(int i=0; i<frame->getNumMB(); i++)
		{
			Macroblock* mb = frame->getMacroblock(i);

			if(mb->isMissing())
			{
				if(frame->is_p_frame())
				{
					
					// Checking for edges
					bool is_top = (i/width == 0);
					bool is_left = (i%width == 0);
					bool is_right = (i%width == width-1);
					bool is_bot = (i/width == height-1);

					/**
					 * Get the motion vectors from the surrounding macroblocks.
					 * If the block lays at the edge of frame, set it to null
					 */					
					std::vector<Macroblock*> blocks; 
					
					int x,y,dx,dy;
					x = y = dx =0;
					int X = mb->getXPos();
					int Y = mb->getYPos();
					int t = std::max(X,Y);
					dx = 0;
					dy = -1;
					while(blocks.size() < 10) {
						//if ((-X/2 <= x) && (x <= X/2) && (-Y/2 <= y) && (y <= Y/2)) {
						if(Y+y >= 0 && X+x >= 0 && X+x < frame->getWidth() && Y+y < frame->getHeight()) {
							Macroblock* block = frame->getMacroblock(MACRO_HEIGHT*(Y+y)+(X+x));
							if(!block->isMissing()) {
								blocks.push_back(block);
							}
						}
						if( (x == y) || ((x < 0) && (x == -y)) || ((x > 0) && (x == 1-y))){
							t = dx;
							dx = -dy;
							dy = t;
						}
						x += dx;
						y += dy;
						//std::cout << x << " " << y << "\n";
					}

					// Create another macroblock that has the average of all the MV's
					// The positions don't matter here, only the motion vector does
					int avg_x = 0;
					int avg_y = 0;
					Macroblock* average_block = new Macroblock(0, 0, 0);
					
					for(std::vector<int>::size_type i = 0; i != blocks.size(); i++) {
						avg_x += blocks[i]->mv.x;
						avg_y += blocks[i]->mv.y;
					}
					avg_x /= blocks.size();
					avg_y /= blocks.size();
					average_block->mv.x = avg_x;
					average_block->mv.y = avg_y;

					blocks.push_back(average_block);

					// And another block which is the previous block!
					Macroblock* mv_zero_block = new Macroblock(0, 0, 0);
					mv_zero_block->mv.x = 0;
					mv_zero_block->mv.y = 0;

					int error = INT_MAX;

					for(std::vector<int>::size_type i = 0; i != blocks.size(); i++) {
						Macroblock* new_mb = get_shifted_mb(frame, referenceFrame, mb, &blocks[i]->mv);

						if(new_mb)
						{
							int new_error = calc_bounding_match_error(frame, new_mb);
							if(new_error < error)
							{
								error = new_error;
								copy_mb(new_mb, mb);
							}

							delete(new_mb);
						}
					}

					// Delete the average block!
					delete(average_block);

					// Delete the block with mv 0!
					delete(mv_zero_block);

					if(error == INT_MAX)
					{
						copy_mb(referenceFrame->getMacroblock(i), frame->getMacroblock(i));
					}
					mb->setConcealed();
					
				}
				else
				{
					/**
					 * If the macroblock lost belongs to an intra-coded frame,
					 * no motion vectors are available. In this case, use zero
					 * motion temporal construction can be applied, so we use the
					 * method from conceal_temporal_1 and create a deep copy of 
					 * the macroblok
					 */
					copy_mb(referenceFrame->getMacroblock(i), frame->getMacroblock(i));
				}
			}
		}
	}