#ifndef TEMPORALCONCEALER_H
#define TEMPORALCONCEALER_H

#define MACRO_WIDTH 16
#define MACRO_HEIGHT 16

#include "Frame.h"

int checkMotionVector(Frame* frame, Frame* ref, int index, MotionVector* mv);

int calc_bounding_match_error(Frame* frame, Macroblock* mb);
Macroblock* get_shifted_mb(Frame* frame, Frame* ref, Macroblock* mb, MotionVector* mv);
void copy_mb(Macroblock* source, Macroblock* dest);

#endif TEMPORALCONCEALER_H