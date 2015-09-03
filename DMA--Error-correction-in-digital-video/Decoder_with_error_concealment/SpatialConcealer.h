#ifndef SPATIALCEALER_H
#define SPATIALCEALER_H

#include "Frame.h"
#include <math.h> 


#define MACRO_WIDTH 16
#define MACRO_HEIGHT 16
#define EDGE_WIDTH 4
#define MAX_DISTANCE 2
#define PI 3.14159265
#define PLANE_THRESHOLD 50



/*
Datastructure to hold reference macroblocks when doing errorconcealement.
mb: a reference to the macroblock
distance: how many blocks is the macroblock away from the block that needs orrorconcealment. 
Distance will never be greater then MAX_DISTANCE, if too many blocks are missing, distance is 0 meaning it won't be used for interpolation. 
*/
struct spatial_reference_block{
	Macroblock* mb;
	char distance;
};

struct spatial_reference_blocks{
	int blocknumber;
	spatial_reference_block left;
	spatial_reference_block top;
	spatial_reference_block right;
	spatial_reference_block bot;
};

struct spatial_reference_blocks_full{
	int blocknumber;
	spatial_reference_block left_t;
	spatial_reference_block left_b;
	spatial_reference_block right_t;
	spatial_reference_block right_b;
	spatial_reference_block left;
	spatial_reference_block top;
	spatial_reference_block right;
	spatial_reference_block bot;

};

struct edge_angle{
	double angle;
	int concisiveness;
};

struct macroblock_with_edge{
	pixel luma[MACRO_WIDTH + 2 * EDGE_WIDTH][MACRO_HEIGHT + 2 * EDGE_WIDTH];
	pixel cr[MACRO_WIDTH/2 + EDGE_WIDTH][MACRO_HEIGHT/2 + EDGE_WIDTH];
	pixel cb[MACRO_WIDTH/2 + EDGE_WIDTH][MACRO_HEIGHT/2 + EDGE_WIDTH];
};

/*

@return Angle of the edge. returns -1 if ref block is missing, returns -2 if no edge was found.
*/
edge_angle calcEdgeAngle(Frame* frame, int blocknumber);

/*
This method will return, if accesible and possible, 4 macroblocks from around the given block. 
A block will be the closest block in a certain direction that is not missing 
AND is within the maximum DEFINED distance
*/
spatial_reference_blocks* getSpatialReferenceBlocks(Frame* frame, int blocknumber);
spatial_reference_blocks_full* getSpatialReferenceBlocksFull(Frame* frame, int  blocknumber);

void spatialRectonstruct(Macroblock* targetmb, spatial_reference_blocks* ref_blocks);

void angularReconstruction(Frame* frame, int blocknumber, spatial_reference_blocks_full* ref_blocks, edge_angle ea);

macroblock_with_edge* fill_edge_pixels(spatial_reference_blocks_full* ref_blocks);


int getAngularReconstructionValueLuma(macroblock_with_edge* edge_block, int x, int y, int direction);
int getAngularReconstructionValueCb(macroblock_with_edge* edge_block, int x, int y, int direction);
int getAngularReconstructionValueCr(macroblock_with_edge* edge_block, int x, int y, int direction);

void horizontalReconstruction(macroblock_with_edge* edge_block, int direction);
void verticalRecontruction(macroblock_with_edge* edge_block, int direction);
void diagonalReconstruction(macroblock_with_edge* edge_block, int direction);
void antidiagonaReconstruction(macroblock_with_edge* edge_block, int direction);
#endif