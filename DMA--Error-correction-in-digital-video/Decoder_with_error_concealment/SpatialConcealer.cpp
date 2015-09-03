#include "SpatialConcealer.h"
#include <stdio.h>

/*
Determening the angle of the edge and information about it, using the top, left, right and bottom adjacent macroblocks.
@return Angle of the edge. returns -1 if ref block is missing, returns -2 if no edge was found.
*/
edge_angle calcEdgeAngle(Frame* frame, int blocknumber){
	Macroblock* refmb = NULL;
	int refnumber;
	int width = frame->getWidth();
	int height = frame->getHeight();
	//Angle mode consensus modes[k] represents angle 22.5*k with k [0,7]
	double modes[8] = {0,0,0,0,0,0,0,0};

	// We will be using Sobel operator masks to determine the angles of the edges in adjacent blocks
	// Whenever an "angle" of an edge is determined, we add a weighted amount to the modes array

	//top block
	refnumber = blocknumber - width;
	if(refnumber >= 0)
		refmb = frame->getMacroblock(refnumber);
	if(refmb){
		if(!refmb->isMissing()){
			for(int i = 1; i < 15; i++){
				// Can be derived from convolution with sobeloperator
				float gx = -2*refmb->luma[14][i-1]+2*refmb->luma[14][i+1]-1*refmb->luma[13][i-1]-1*refmb->luma[15][i-1]+refmb->luma[13][i+1]+refmb->luma[15][i+1];
				float gy = 1*refmb->luma[13][i-1]+2*refmb->luma[13][i-1]+1*refmb->luma[13][i+1]-1*refmb->luma[15][i-1]-refmb->luma[13][i+1]-2*refmb->luma[15][i];
				if(gx == 0)
					gx = 0.00000001;
				double angle = atan2(gy,gx)*180.0/PI;
				if(angle<0)
					angle +=180;

				modes[(int)floor((angle/22.5))] += sqrt(gx*gx + gy*gy);	
			}
		}	
	}
	refmb = NULL;

	// Left block
	refnumber = blocknumber - 1;
	if(refnumber >= 0 && refnumber%width != width-1)
		refmb = frame->getMacroblock(refnumber);
	if(refmb){
		if(!refmb->isMissing()){
			for(int i = 1; i < 15; i++){
				// Can be derived from convolution with sobeloperator
				float gx = -2*refmb->luma[i][13]+2*refmb->luma[i][15]-1*refmb->luma[i-1][13]-1*refmb->luma[i+1][13]+refmb->luma[i+1][15]+refmb->luma[i-1][15];
				float gy = 1*refmb->luma[i-1][13]+2*refmb->luma[i-1][14]+1*refmb->luma[i-1][15]-1*refmb->luma[i+1][13]-refmb->luma[i+1][15]-2*refmb->luma[i-1][14];
				if(gx == 0)
					gx = 0.00000001;
				double angle = atan2(gy,gx)*180.0/PI;
				if(angle<0)
					angle +=180;

				modes[(int)floor((angle/22.5))] += sqrt(gx*gx + gy*gy);	
			}
		}
	}
	refmb = NULL;

	// right block
	refnumber = blocknumber + 1;
	if(refnumber/height < height && refnumber%width != 0)
		refmb = frame->getMacroblock(refnumber);
	if(refmb){
		if(!refmb->isMissing()){
			for(int i = 1; i < 15; i++){
				// Can be derived from convolution with sobeloperator
				float gx = -2*refmb->luma[i][0]+2*refmb->luma[i][2]-1*refmb->luma[i-1][0]-1*refmb->luma[i+1][0]+refmb->luma[i+1][2]+refmb->luma[i-1][2];
				float gy = 1*refmb->luma[i-1][0]+2*refmb->luma[i-1][1]+1*refmb->luma[i-1][2]-1*refmb->luma[i+1][0]-refmb->luma[i+1][2]-2*refmb->luma[i-1][1];
				if(gx == 0)
					gx = 0.00000001;
				double angle = atan2(gy,gx)*180.0/PI;
				if(angle<0)
					angle +=180;

				modes[(int)floor((angle/22.5))] += sqrt(gx*gx + gy*gy);	
			}
		}
	}
	refmb = NULL;

	//bottom block
	refnumber = blocknumber + width;
	if(refnumber/height < height)
		refmb = frame->getMacroblock(refnumber);
	if(refmb){
		if(!refmb->isMissing()){
			for(int i = 1; i < 15; i++){
				// Can be derived from convolution with sobeloperator
				float gx = -2*refmb->luma[1][i-1]+2*refmb->luma[1][i+1]-1*refmb->luma[0][i-1]-1*refmb->luma[2][i-1]+refmb->luma[0][i+1]+refmb->luma[2][i+1];
				float gy = 1*refmb->luma[0][i-1]+2*refmb->luma[0][i-1]+1*refmb->luma[0][i+1]-1*refmb->luma[2][i-1]-refmb->luma[0][i+1]-2*refmb->luma[2][i];
				if(gx == 0)
					gx = 0.00000001;
				double angle = atan2(gy,gx)*180.0/PI;
				if(angle<0)
					angle +=180;

				modes[(int)floor((angle/22.5))] += sqrt(gx*gx + gy*gy);	
			}
		}	
	}

	// Determine which edge direction is most plausible!
	int anglemultiplier = -1;
	int highest = -1;
	for(int i  = 0; i<8; i++){
		if(modes[i] > highest){
			highest = modes[i];
			anglemultiplier = i;
		}
	}

	edge_angle ea;
	ea.angle = 22.5*anglemultiplier;
	ea.concisiveness = modes[anglemultiplier];
	return ea;
}

spatial_reference_blocks_full* getSpatialReferenceBlocksFull(Frame* frame, int  blocknumber){
	int width = frame->getWidth();
	int height = frame->getHeight();
	int tmp_b_number = 0;

	spatial_reference_blocks_full *returnblocks = new spatial_reference_blocks_full;

	// init
	returnblocks->blocknumber = blocknumber;
	returnblocks->bot.distance=0;
	returnblocks->bot.mb=NULL;
	returnblocks->top.distance=0;
	returnblocks->top.mb=NULL;
	returnblocks->left.distance=0;
	returnblocks->left.mb=NULL;
	returnblocks->right.distance=0;
	returnblocks->right.mb=NULL;
	returnblocks->left_b.distance = 0;
	returnblocks->left_b.mb=NULL;
	returnblocks->left_t.distance = 0;
	returnblocks->left_t.mb=NULL;
	returnblocks->right_b.distance = 0;
	returnblocks->right_b.mb=NULL;
	returnblocks->right_t.distance = 0;
	returnblocks->right_t.mb=NULL;

	if(blocknumber / width != 0){
		// left top
		tmp_b_number = blocknumber - width - 1;
		if(tmp_b_number >= 0 && tmp_b_number%width != width - 1)
			returnblocks->left_t.mb = frame->getMacroblock(tmp_b_number);

		//top
		tmp_b_number = blocknumber - width;
		returnblocks->top.mb = frame->getMacroblock(tmp_b_number);

		// right top
		tmp_b_number = blocknumber - width + 1;
		if(tmp_b_number%width !=0)
			returnblocks->right_t.mb = frame->getMacroblock(tmp_b_number);
	}
	// left
	tmp_b_number = blocknumber - 1;
	if(tmp_b_number % width != width - 1 && tmp_b_number >= 0)
		returnblocks->left.mb = frame->getMacroblock(tmp_b_number);

	// right
	tmp_b_number = blocknumber + 1;
	if(tmp_b_number % width != 0)
		returnblocks->right.mb = frame->getMacroblock(tmp_b_number);

	if(blocknumber / width != height - 1){
		// left bottom
		tmp_b_number =  blocknumber + width - 1;
		if(tmp_b_number+1 % width != 0)
			returnblocks->left_b.mb = frame->getMacroblock(tmp_b_number);

		// bottom
		tmp_b_number = blocknumber + width;
		returnblocks->bot.mb = frame->getMacroblock(tmp_b_number);

		// right bottom
		tmp_b_number = blocknumber + width + 1;
		if(tmp_b_number-1 % width != width - 1)
			returnblocks->right_b.mb = frame->getMacroblock(tmp_b_number);
	}

	return returnblocks;
}

spatial_reference_blocks* getSpatialReferenceBlocks(Frame* frame, int blocknumber){
	int width = frame->getWidth();
	int height = frame->getHeight();

	spatial_reference_blocks* returnblocks = new spatial_reference_blocks;

	// init
	returnblocks->blocknumber = blocknumber;
	returnblocks->bot.distance=0;
	returnblocks->top.distance=0;
	returnblocks->left.distance=0;
	returnblocks->right.distance=0;

	bool blockcheck;

	// Searching for top block
	int j = 1;
	do {
		// Edgecheck
		blockcheck = (blocknumber/width-j == -1);

		if(!blockcheck && !frame->getMacroblock(blocknumber-j*width)->isMissing()){
			returnblocks->top.mb = frame->getMacroblock(blocknumber-j*width);
			returnblocks->top.distance = j;
			break;
		}

		if(blockcheck){
			returnblocks->top.mb = NULL;
			break;
		}
		j++;
	} while(!blockcheck);

	// Searching for bottom block
	j = 1;
	do {
		// Edgecheck
		blockcheck = (blocknumber/width+j == height);

		if(!blockcheck && !frame->getMacroblock(blocknumber+j*width)->isMissing()){
			returnblocks->bot.mb = frame->getMacroblock(blocknumber+j*width);
			returnblocks->bot.distance = j;
			break;
		}

		if(blockcheck){
			returnblocks->bot.mb = NULL;
			break;
		}
		j++;
	} while(!blockcheck);

	// Searching for left block
	j = 1;
	do {
		// Edgecheck
		blockcheck = (blocknumber%width-j == -1);

		if(!blockcheck && !frame->getMacroblock(blocknumber-j)->isMissing()){
			returnblocks->left.mb = frame->getMacroblock(blocknumber-j);
			returnblocks->left.distance = j;
			break;
		}

		if(blockcheck){
			returnblocks->left.mb = NULL;
			break;
		}
		j++;
	} while(!blockcheck);

	// Searching for right block
	do {
		// Edgecheck
		blockcheck = (blocknumber%width+j == width);

		if(!blockcheck && !frame->getMacroblock(blocknumber+j)->isMissing()){
			returnblocks->right.mb = frame->getMacroblock(blocknumber+j);
			returnblocks->right.distance = j;
			break;
		}

		if(blockcheck){
			returnblocks->right.mb = NULL;
			break;
		}
		j++;
	} while(!blockcheck);

	return returnblocks;
}

macroblock_with_edge* fill_edge_luma(spatial_reference_blocks_full* ref_blocks){
	macroblock_with_edge* edge_block = new macroblock_with_edge;

	// luma
	for (int i = 0; i < EDGE_WIDTH; i++){
		for (int j = 0; j < EDGE_WIDTH; j++){
			int x_offspring = MACRO_WIDTH - EDGE_WIDTH;
			int y_offspring = MACRO_HEIGHT - EDGE_WIDTH;
			//top left egde
			if(ref_blocks->left_t.mb != NULL)
				edge_block->luma[i][j] = ref_blocks->left_t.mb->luma[x_offspring + i][y_offspring + j];
			else
				edge_block->luma[i][j] = -1;

			//top right edge
			if(ref_blocks->right_t.mb != NULL)
				edge_block->luma[EDGE_WIDTH + MACRO_WIDTH + i][j] = ref_blocks->right_t.mb->luma[i][y_offspring + j];
			else
				edge_block->luma[EDGE_WIDTH + MACRO_WIDTH + i][j] = -1;

			// bot left edge
			if(ref_blocks->left_b.mb != NULL)
				edge_block->luma[i][EDGE_WIDTH + MACRO_HEIGHT + j] = ref_blocks->left_b.mb->luma[x_offspring + i][j];
			else
				edge_block->luma[i][EDGE_WIDTH + MACRO_HEIGHT + j] = -1;

			// bot right edge
			if(ref_blocks->right_b.mb != NULL)
				edge_block->luma[EDGE_WIDTH + MACRO_WIDTH + i][EDGE_WIDTH + MACRO_HEIGHT + j] = ref_blocks->right_b.mb->luma[i][j];
			else
				edge_block->luma[EDGE_WIDTH + MACRO_WIDTH + i][EDGE_WIDTH + MACRO_HEIGHT + j] = -1;
		}
	}

	for (int i = 0; i < MACRO_WIDTH; i++){
		for (int j = 0; j < EDGE_WIDTH; j++){
			int x_offspring = MACRO_WIDTH - EDGE_WIDTH;
			int y_offspring = MACRO_HEIGHT - EDGE_WIDTH;
			// top edge
			if(ref_blocks->top.mb != NULL)
				edge_block->luma[i + EDGE_WIDTH][j] = ref_blocks->top.mb->luma[i][y_offspring + j];
			else
				edge_block->luma[i + EDGE_WIDTH][j] = -1;

			// bot edge
			if(ref_blocks->bot.mb != NULL)
				edge_block->luma[i + EDGE_WIDTH][MACRO_HEIGHT + EDGE_WIDTH + j] = ref_blocks->bot.mb->luma[i][j];
			else
				edge_block->luma[i + EDGE_WIDTH][MACRO_HEIGHT + EDGE_WIDTH + j] = -1;

			// left edge
			if(ref_blocks->left.mb != NULL)
				edge_block->luma[j][EDGE_WIDTH + i] = ref_blocks->left.mb->luma[x_offspring + j][i];
			else
				edge_block->luma[j][EDGE_WIDTH + i] = -1;

			// right edge
			if(ref_blocks->right.mb != NULL)
				edge_block->luma[EDGE_WIDTH + MACRO_WIDTH + j][EDGE_WIDTH + i] = ref_blocks->right.mb->luma[j][i];
			else
				edge_block->luma[EDGE_WIDTH + MACRO_WIDTH + j][EDGE_WIDTH + i] = -1;
		}
	}

	// cb and cr
	for (int i = 0; i < EDGE_WIDTH/2; i++){
		for (int j = 0; j < EDGE_WIDTH/2; j++){
			int x_offspring = (MACRO_WIDTH - EDGE_WIDTH)/2;
			int y_offspring = (MACRO_HEIGHT - EDGE_WIDTH)/2;
			//top left egde

			if(ref_blocks->left_t.mb != NULL){
				edge_block->cb[i][j] = ref_blocks->left_t.mb->cb[x_offspring + i][y_offspring + j];
				edge_block->cr[i][j] = ref_blocks->left_t.mb->cr[x_offspring + i][y_offspring + j];
			}else{
				edge_block->cb[i][j] = -1;
				edge_block->cr[i][j] = -1;
			}
			//top right edge
			if(ref_blocks->right_t.mb != NULL){
				edge_block->cb[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][j] = ref_blocks->right_t.mb->cb[i][y_offspring + j];
				edge_block->cr[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][j] = ref_blocks->right_t.mb->cr[i][y_offspring + j];
			}else{
				edge_block->cb[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][j] = -1;
				edge_block->cr[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][j] = -1;
			}

			// bot left edge
			if(ref_blocks->left_b.mb != NULL){
				edge_block->cb[i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = ref_blocks->left_b.mb->cb[x_offspring + i][j];
				edge_block->cr[i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = ref_blocks->left_b.mb->cr[x_offspring + i][j];
			}else{
				edge_block->cb[i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = -1;
				edge_block->cr[i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = -1;
			}

			// bot right edge
			if(ref_blocks->right_b.mb != NULL){
				edge_block->cb[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = ref_blocks->right_b.mb->cb[i][j];
				edge_block->cr[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = ref_blocks->right_b.mb->cr[i][j];
			}else{
				edge_block->cb[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = -1;
				edge_block->cr[(EDGE_WIDTH + MACRO_WIDTH)/2 + i][(EDGE_WIDTH + MACRO_HEIGHT)/2 + j] = -1;
			}
		}
	}

	for (int i = 0; i < MACRO_WIDTH/2; i++){
		for (int j = 0; j < EDGE_WIDTH/2; j++){
			int x_offspring = (MACRO_WIDTH - EDGE_WIDTH)/2;
			int y_offspring = (MACRO_HEIGHT - EDGE_WIDTH)/2;
			// top edge
			if(ref_blocks->top.mb != NULL){
				edge_block->cb[i + EDGE_WIDTH/2][j] = ref_blocks->top.mb->cb[i][y_offspring + j];
				edge_block->cr[i + EDGE_WIDTH/2][j] = ref_blocks->top.mb->cr[i][y_offspring + j];
			}else{
				edge_block->cb[i + EDGE_WIDTH/2][j] = -1;
				edge_block->cr[i + EDGE_WIDTH/2][j] = -1;
			}

			// bot edge
			if(ref_blocks->bot.mb != NULL){
				edge_block->cb[i + EDGE_WIDTH/2][(MACRO_HEIGHT + EDGE_WIDTH)/2 + j] = ref_blocks->bot.mb->cb[i][j];
				edge_block->cr[i + EDGE_WIDTH/2][(MACRO_HEIGHT + EDGE_WIDTH)/2 + j] = ref_blocks->bot.mb->cr[i][j];
			}else{
				edge_block->cb[i + EDGE_WIDTH/2][(MACRO_HEIGHT + EDGE_WIDTH)/2 + j] = -1;
				edge_block->cr[i + EDGE_WIDTH/2][(MACRO_HEIGHT + EDGE_WIDTH)/2 + j] = -1;
			}

			// left edge
			if(ref_blocks->left.mb != NULL){
				edge_block->cb[j][EDGE_WIDTH/2 + i] = ref_blocks->left.mb->cb[x_offspring + j][i];
				edge_block->cr[j][EDGE_WIDTH/2 + i] = ref_blocks->left.mb->cr[x_offspring + j][i];
			}else{
				edge_block->cb[j][EDGE_WIDTH/2 + i] = -1;
				edge_block->cr[j][EDGE_WIDTH/2 + i] = -1;
			}

			// right edge
			if(ref_blocks->right.mb != NULL){
				edge_block->cb[(EDGE_WIDTH + MACRO_WIDTH)/2 + j][EDGE_WIDTH/2 + i] = ref_blocks->right.mb->cb[j][i];
				edge_block->cr[(EDGE_WIDTH + MACRO_WIDTH)/2 + j][EDGE_WIDTH/2 + i] = ref_blocks->right.mb->cr[j][i];
			}else{
				edge_block->cb[(EDGE_WIDTH + MACRO_WIDTH)/2 + j][EDGE_WIDTH/2 + i] = -1;
				edge_block->cr[(EDGE_WIDTH + MACRO_WIDTH)/2 + j][EDGE_WIDTH/2 + i] = -1;
			}
		}
	}

	return edge_block;

}

void angularReconstruction(Frame* frame, int blocknumber, spatial_reference_blocks_full* ref_blocks, edge_angle ea){
	// use image from "an improved method of detecting edge direction for spetial error concealment" to reconstruct mb using ea
	
	macroblock_with_edge* edge_block = fill_edge_luma(ref_blocks);
	int direction = (int) (ea.angle/22.5);
	// luma
	if(ea.angle == 0 || ea.angle == 1)
		horizontalReconstruction(edge_block, direction);

	else if(ea.angle == 2)
		antidiagonaReconstruction(edge_block, direction);

	else if(ea.angle == 3 || ea.angle == 4 || ea.angle == 5)
		verticalRecontruction(edge_block, direction);

	else if(ea.angle == 6 || ea.angle == 7)
		diagonalReconstruction(edge_block, direction);
	
	

	Macroblock* mb = frame->getMacroblock(blocknumber);

	for(int i=0; i<MACRO_WIDTH; i++){
		for(int j=0; j<MACRO_HEIGHT; j++){
			mb->luma[i][j] = edge_block->luma[EDGE_WIDTH + i][EDGE_WIDTH + j];
		}
	}

	for(int i=0; i<MACRO_WIDTH/2; i++){
		for(int j=0; j<MACRO_HEIGHT/2; j++){
			mb->cb[i][j] = edge_block->cb[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j];
			mb->cr[i][j] = edge_block->cr[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j];
		}
	}

	delete(edge_block);
}

void horizontalReconstruction(macroblock_with_edge* edge_block, int direction){

	for(int i = 0; i<MACRO_WIDTH/2; i++){
		for(int j = 0; j<MACRO_HEIGHT; j++){
			edge_block->luma[EDGE_WIDTH + i][EDGE_WIDTH + j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + i, EDGE_WIDTH + j, direction+8);
			edge_block->luma[EDGE_WIDTH + (MACRO_WIDTH-1) - i][EDGE_WIDTH + j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + (MACRO_WIDTH-1) - i, EDGE_WIDTH + j, direction);
		}
	}
	
	for(int i = 0; i<MACRO_WIDTH/4; i++){
		for(int j = 0; j<MACRO_HEIGHT/2; j++){
			edge_block->cb[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2 + i, EDGE_WIDTH/2 + j, direction+8);
			edge_block->cb[EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i, EDGE_WIDTH/2 + j, direction);
			
			edge_block->cr[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2 + i, EDGE_WIDTH/2 + j, direction+8);
			edge_block->cr[EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i, EDGE_WIDTH/2 + j, direction);
		}
	}
}

void verticalRecontruction(macroblock_with_edge* edge_block, int direction){
	for(int i = 0; i<MACRO_WIDTH; i++){
		for(int j = 0; j<MACRO_HEIGHT/2; j++){
			edge_block->luma[EDGE_WIDTH + i][EDGE_WIDTH + j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + i, EDGE_WIDTH + j, direction);
			edge_block->luma[EDGE_WIDTH + i][EDGE_WIDTH + (MACRO_HEIGHT-1) - j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + i, EDGE_WIDTH + (MACRO_HEIGHT-1) - j, direction+8);
		}
	}
	for(int i = 0; i<MACRO_WIDTH/2; i++){
		for(int j = 0; j<MACRO_HEIGHT/4; j++){
			edge_block->cb[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2 + i, EDGE_WIDTH/2 + j, direction);
			edge_block->cb[EDGE_WIDTH/2 + i][EDGE_WIDTH/2+ (MACRO_HEIGHT/2-1) - j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2+ i, EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j, direction+8);
			
			edge_block->cr[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2 + i, EDGE_WIDTH/2 + j, direction);
			edge_block->cr[EDGE_WIDTH/2 + i][EDGE_WIDTH/2+ (MACRO_HEIGHT/2-1) - j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2+ i, EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j, direction+8);
		}
	}
}

void diagonalReconstruction(macroblock_with_edge* edge_block, int direction){
	for(int j = 0; j<MACRO_HEIGHT; j++){
		for(int i = 0; i<=j; i++){
			edge_block->luma[EDGE_WIDTH + i][EDGE_WIDTH + j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + i, EDGE_WIDTH + j, direction);
			edge_block->luma[EDGE_WIDTH + (MACRO_WIDTH-1) - i][EDGE_WIDTH + (MACRO_HEIGHT-1) - j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + (MACRO_WIDTH-1) - i, EDGE_WIDTH + (MACRO_HEIGHT-1) - j, direction+8);
		}
	}

	for(int j = 0; j<MACRO_HEIGHT/2; j++){
		for(int i = 0; i<=j; i++){
			edge_block->cb[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2 + i, EDGE_WIDTH/2 + j, direction);
			edge_block->cb[EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i][EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i, EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j, direction+8);
			
			edge_block->cr[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2 + i, EDGE_WIDTH/2 + j, direction);
			edge_block->cr[EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i][EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i, EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j, direction+8);
		}
	}
}

void antidiagonaReconstruction(macroblock_with_edge* edge_block, int direction){
	for(int j = 0; j<MACRO_HEIGHT; j++){
		for(int i = MACRO_WIDTH-1; i>=j; i--){
			edge_block->luma[EDGE_WIDTH + (MACRO_WIDTH-1) - i][EDGE_WIDTH + j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + (MACRO_WIDTH-1) - i, EDGE_WIDTH + j, direction);
			edge_block->luma[EDGE_WIDTH + i][EDGE_WIDTH + (MACRO_HEIGHT-1) - j] = getAngularReconstructionValueLuma(edge_block, EDGE_WIDTH + i, EDGE_WIDTH + (MACRO_HEIGHT-1) - j, direction+8);
		}
	}
	for(int j = 0; j<MACRO_HEIGHT/2; j++){
		for(int i = MACRO_WIDTH/2-1; i>=j; i--){
			edge_block->cb[EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i, EDGE_WIDTH/2 + j, direction);
			edge_block->cb[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j] = getAngularReconstructionValueCb(edge_block, EDGE_WIDTH/2+ i, EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j, direction+8);
			
			edge_block->cr[EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i][EDGE_WIDTH/2 + j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2 + (MACRO_WIDTH/2-1) - i, EDGE_WIDTH/2 + j, direction);
			edge_block->cr[EDGE_WIDTH/2 + i][EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j] = getAngularReconstructionValueCr(edge_block, EDGE_WIDTH/2+ i, EDGE_WIDTH/2 + (MACRO_HEIGHT/2-1) - j, direction+8);
		}
	}
}

int getAngularReconstructionValueLuma(macroblock_with_edge* edge_block, int x, int y, int direction){
	
	switch (direction){
	case 0: // 0 degree
		return (2 * edge_block->luma[x + 2][y] + edge_block->luma[x + 4][y]) / 3;
	case 1: // 22.5 degree
		return (2 * edge_block->luma[x + 2][y - 1] + edge_block->luma[x + 4][y - 2]) / 3;
	case 2: // 45 degree
		return (2 * edge_block->luma[x + 2][y - 2] + edge_block->luma[x + 4][y - 4]) / 3;
	case 3: // 67.5 degree
		return (2 * edge_block->luma[x + 1][y - 2] + edge_block->luma[x + 2][y - 4]) / 3;
	case 4: // 90 degree
		return (2 * edge_block->luma[x][y - 2] + edge_block->luma[x][y - 4]) / 3;
	case 5: // 12.5 degree
		return (2 * edge_block->luma[x - 1][y - 2] + edge_block->luma[x - 2][y - 4]) / 3;
	case 6: // 135 degree
		return (2 * edge_block->luma[x - 2][y - 2] + edge_block->luma[x - 4][y - 4]) / 3;
	case 7: // 157.5 degree
		return (2 * edge_block->luma[x - 2][y - 1] + edge_block->luma[x - 4][y - 2]) / 3;
	case 8: // 180 degree
		return (2 * edge_block->luma[x - 2][y] + edge_block->luma[x - 4][y]) / 3;
	case 9: // 202.5 degree
		return (2 * edge_block->luma[x - 2][y + 1] + edge_block->luma[x - 4][y + 2]) / 3;
	case 10: // 225 degree
		return (2 * edge_block->luma[x - 2][y + 2] + edge_block->luma[x - 4][y + 4]) / 3;
	case 11: // 247.5 degree
		return (2 * edge_block->luma[x - 1][y + 2] + edge_block->luma[x - 2][y + 4]) / 3;
	case 12: // 270 degree
		return (2 * edge_block->luma[x][y + 2] + edge_block->luma[x][y + 4]) / 3;
	case 13: // 292.5 degree
		return (2 * edge_block->luma[x + 1][y + 2] + edge_block->luma[x + 2][y + 4]) / 3;
	case 14: // 315 degree
		return (2 * edge_block->luma[x + 2][y + 2] + edge_block->luma[x + 4][y + 4]) / 3;
	case 15: // 337.5 degree
		return (2 * edge_block->luma[x + 2][y + 1] + edge_block->luma[x + 4][y + 2]) / 3;
	}
}


int getAngularReconstructionValueCb(macroblock_with_edge* edge_block, int x, int y, int direction){
	switch (direction){
	case 0: // 0 degree
		return (2 * edge_block->cb[x + 1][y] + edge_block->cb[x + 2][y]) / 3;
	case 1: // 22.5 degree
		return (2 * edge_block->cb[x + 1][y] + edge_block->cb[x + 2][y - 1]) / 3;
	case 2: // 45 degree
		return (2 * edge_block->cb[x + 1][y - 1] + edge_block->cb[x + 2][y - 2]) / 3;
	case 3: // 67.5 degree
		return (2 * edge_block->cb[x][y - 1] + edge_block->cb[x + 1][y - 2]) / 3;
	case 4: // 90 degree
		return (2 * edge_block->cb[x][y - 1] + edge_block->cb[x][y - 2]) / 3;
	case 5: // 12.5 degree
		return (2 * edge_block->cb[x][y - 1] + edge_block->cb[x - 1][y - 2]) / 3;
	case 6: // 135 degree
		return (2 * edge_block->cb[x - 1][y - 1] + edge_block->cb[x - 2][y - 2]) / 3;
	case 7: // 157.5 degree
		return (2 * edge_block->cb[x - 1][y] + edge_block->cb[x - 2][y - 1]) / 3;
	case 8: // 180 degree
		return (2 * edge_block->cb[x - 1][y] + edge_block->cb[x - 2][y]) / 3;
	case 9: // 202.5 degree
		return (2 * edge_block->cb[x - 1][y] + edge_block->cb[x - 2][y + 1]) / 3;
	case 10: // 225 degree
		return (2 * edge_block->cb[x - 1][y + 1] + edge_block->cb[x - 2][y + 2]) / 3;
	case 11: // 247.5 degree
		return (2 * edge_block->cb[x][y + 1] + edge_block->cb[x - 1][y + 2]) / 3;
	case 12: // 270 degree
		return (2 * edge_block->cb[x][y + 1] + edge_block->cb[x][y + 2]) / 3;
	case 13: // 292.5 degree
		return (2 * edge_block->cb[x][y + 1] + edge_block->cb[x + 1][y + 2]) / 3;
	case 14: // 315 degree
		return (2 * edge_block->cb[x + 1][y + 1] + edge_block->cb[x + 2][y + 2]) / 3;
	case 15: // 337.5 degree
		return (2 * edge_block->cb[x + 1][y] + edge_block->cb[x + 2][y + 1]) / 3;
	}
}
int getAngularReconstructionValueCr(macroblock_with_edge* edge_block, int x, int y, int direction){
	switch (direction){
	case 0: // 0 degree
		return (2 * edge_block->cr[x + 1][y] + edge_block->cr[x + 2][y]) / 3;
	case 1: // 22.5 degree
		return (2 * edge_block->cr[x + 1][y] + edge_block->cr[x + 2][y - 1]) / 3;
	case 2: // 45 degree
		return (2 * edge_block->cr[x + 1][y - 1] + edge_block->cr[x + 2][y - 2]) / 3;
	case 3: // 67.5 degree
		return (2 * edge_block->cr[x][y - 1] + edge_block->cr[x + 1][y - 2]) / 3;
	case 4: // 90 degree
		return (2 * edge_block->cr[x][y - 1] + edge_block->cr[x][y - 2]) / 3;
	case 5: // 12.5 degree
		return (2 * edge_block->cr[x][y - 1] + edge_block->cr[x - 1][y - 2]) / 3;
	case 6: // 135 degree
		return (2 * edge_block->cr[x - 1][y - 1] + edge_block->cr[x - 2][y - 2]) / 3;
	case 7: // 157.5 degree
		return (2 * edge_block->cr[x - 1][y] + edge_block->cr[x - 2][y - 1]) / 3;
	case 8: // 180 degree
		return (2 * edge_block->cr[x - 1][y] + edge_block->cr[x - 2][y]) / 3;
	case 9: // 202.5 degree
		return (2 * edge_block->cr[x - 1][y] + edge_block->cr[x - 2][y + 1]) / 3;
	case 10: // 225 degree
		return (2 * edge_block->cr[x - 1][y + 1] + edge_block->cr[x - 2][y + 2]) / 3;
	case 11: // 247.5 degree
		return (2 * edge_block->cr[x][y + 1] + edge_block->cr[x - 1][y + 2]) / 3;
	case 12: // 270 degree
		return (2 * edge_block->cr[x][y + 1] + edge_block->cr[x][y + 2]) / 3;
	case 13: // 292.5 degree
		return (2 * edge_block->cr[x][y + 1] + edge_block->cr[x + 1][y + 2]) / 3;
	case 14: // 315 degree
		return (2 * edge_block->cr[x + 1][y + 1] + edge_block->cr[x + 2][y + 2]) / 3;
	case 15: // 337.5 degree
		return (2 * edge_block->cr[x + 1][y] + edge_block->cr[x + 2][y + 1]) / 3;
	}
}

void spatialRectonstruct(Macroblock* mb, spatial_reference_blocks* ref_blocks){
	// run through all luma (luma)
	for(int j=0; j < MACRO_WIDTH; j++) {
		for(int k=0; k < MACRO_HEIGHT; k++) {
			int denominator_luma =0, nominator_luma=0;

			if(ref_blocks->top.distance >0){
				nominator_luma += (MACRO_HEIGHT+1-k) * ref_blocks->top.mb->luma[MACRO_HEIGHT-1][j];
				denominator_luma += (MACRO_HEIGHT+1-k);
			}
			if(ref_blocks->left.distance > 0){
				nominator_luma += (MACRO_WIDTH+1-j) * ref_blocks->left.mb->luma[k][MACRO_WIDTH-1];
				denominator_luma += (MACRO_WIDTH+1-j);
			}
			if(ref_blocks->bot.distance > 0){
				nominator_luma += (k+1) * ref_blocks->bot.mb->luma[1][j];
				denominator_luma += (k+1);
			}
			if(ref_blocks->right.distance > 0){
				nominator_luma += (j+1) * ref_blocks->right.mb->luma[1][j];
				denominator_luma += (j+1);
			}

			if (denominator_luma) 
			{
			mb->luma[k][j] = nominator_luma/denominator_luma;
			}

		}
	}

	// run through all luma (cb and cr)
	for(int j=0; j < MACRO_WIDTH/2; j++) {
		for(int k=0; k < MACRO_HEIGHT/2; k++) {

			int denominator_cb =0, nominator_cb=0;
			int denominator_cr =0, nominator_cr=0;

			if(ref_blocks->top.distance > 0){
				nominator_cb += (MACRO_HEIGHT+1-k) * ref_blocks->top.mb->cb[MACRO_HEIGHT/2-1][j];
				denominator_cb += (MACRO_HEIGHT+1-k);

				nominator_cr += (MACRO_HEIGHT+1-k) * ref_blocks->top.mb->cr[MACRO_HEIGHT/2-1][j];
				denominator_cr += (MACRO_HEIGHT+1-k);
			}
			if(ref_blocks->left.distance > 0){
				nominator_cb += (MACRO_WIDTH+1-j) * ref_blocks->left.mb->cb[k][MACRO_WIDTH/2-1];
				denominator_cb += (MACRO_WIDTH+1-j);

				nominator_cr += (MACRO_WIDTH+1-j) * ref_blocks->left.mb->cr[k][MACRO_WIDTH/2-1];
				denominator_cr += (MACRO_WIDTH+1-j);
			}
			if(ref_blocks->bot.distance > 0){
				nominator_cb += (k+1) * ref_blocks->bot.mb->cb[1][j];
				denominator_cb += (k+1);

				nominator_cr += (k+1) * ref_blocks->bot.mb->cr[1][j];
				denominator_cr += (k+1);
			}
			if(ref_blocks->right.distance > 0){
				nominator_cb += (j+1) * ref_blocks->right.mb->cb[1][j];
				denominator_cb += (j+1);

				nominator_cr += (j+1) * ref_blocks->right.mb->cr[1][j];
				denominator_cr += (j+1);
			}

			if(denominator_cb && denominator_cr) 
			{
			    mb->cb[k][j] = nominator_cb/denominator_cb;
			    mb->cr[k][j] = nominator_cr/denominator_cr;
			}
		}
	}
}