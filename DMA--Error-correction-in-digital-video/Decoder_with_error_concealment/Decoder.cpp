#include "Decoder.h"

#include "BitFileInput.h"
#include "YUVFileOutput.h"

#include "EntropyDecoder.h"
#include "IQuantiser.h"
#include "IDCTTransform.h"
#include "IMotionCompensator.h"
#include "ErrorSimulator.h"
#include "ErrorConcealer.h"
#include "Clipper.h"


int Decoder::Decode(char *inputfile, char *outputfile, char *error_pattern, short conceal_method)
{
	BitFileInput in(inputfile);
	YUVFileOutput out(outputfile);

	EntropyDecoder entropy_decoder(&in);
	
	ErrorSimulator error_simulator(error_pattern);
	ErrorConcealer error_concealer(conceal_method);

	int width = entropy_decoder.DecodeUInt();
	int height = entropy_decoder.DecodeUInt();

	int qp = entropy_decoder.DecodeUInt();
	int i_interval = entropy_decoder.DecodeUInt();

	printf("File:\t%s\nWidth:\t%d\nHeight:\t%d\nQP:\t%d\nI-interval:\t%d\n\n", inputfile, width, height, qp, i_interval);

	IQuantiser iqt;
	IDCTTransform idct;
	IMotionCompensator imc;

	Frame* frame = new Frame(width, height);
	int count = 0;
	while (entropy_decoder.hasMore())
	{
		bool p_frame = (count % i_interval != 0);
		frame->set_p_frame(p_frame);
		
		printf("Decoding frame #%d (%s)\n", count++, p_frame?"P":"I");
		int num_mbs = frame->getNumMB();
		for (int current_mb = 0; current_mb < num_mbs; current_mb++)
		{
			Macroblock *mb = frame->getMacroblock(current_mb);
			entropy_decoder.ReadMB(mb, p_frame, true, true, true, qp);

			iqt.IQuantise(mb, qp);
			idct.ITransform(mb);
			if(p_frame)
				imc.iMotionCompensate(mb);

			Clipper::Clip(mb);
		}

		error_simulator.simulateErrors(frame);
		error_concealer.concealErrors(frame, imc.getReferenceFrame());
		out.outputFrame(frame);

		delete imc.getReferenceFrame();
		imc.setReferenceFrame(frame);
		frame = new Frame(width, height);
	}

	return 0;
}
#include <iostream>
#include <ctime>

int main(int argc, char* argv[])
{
	Decoder dec;

	if (argc != 5)
	{
		printf("\nUSAGE: decoder_with_error_concealment.exe <inputfile> <outputfile> <error_pattern> <conceal_method>\n\n");
		return 1;
	}

	/**
	 * This is an easy way to calculate the the decoding speed:
	 * We save the time before and after the full process. We
	 * know we also count the pure decoding part with this, but 
	 * this isn't a problem as this is just a constant. If we have
	 * our full decoding time, we can divide it by the number of frames
	 * and then by the number of macroblocks to obtain a result that can
	 * be compared throughout videos of different lengths and size.
	 */
	clock_t Start = clock();
	std::cout << "Timer started" << "\n";
	dec.Decode(argv[1], argv[2], argv[3], atoi(argv[4]));
	std::cout << "Time elapsed: " << clock() - Start << "\n";

	return 0;
}
