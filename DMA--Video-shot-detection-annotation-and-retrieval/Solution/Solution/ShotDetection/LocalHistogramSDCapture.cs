/****************************************************************************
While the underlying libraries are covered by LGPL, this sample is released 
as public domain.  It is distributed in the hope that it will be useful, but 
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY 
or FITNESS FOR A PARTICULAR PURPOSE.  
*****************************************************************************/

using System;
using System.Drawing;
using System.Drawing.Imaging;
using System.Collections;
using System.Runtime.InteropServices;
using System.Diagnostics;
using System.Threading;

using DirectShowLib;
using Solution.Data;

/* 
 * Example of good parameters:
 * treshold: 3
 * binsize: 32
*/

namespace Solution.ShotDetection
{
    /// <summary> Summary description for MainForm. </summary>
    internal class LocalHistogramSDCapture : Capture, ISampleGrabberCB
    {
        #region Member variables

        private int frameSurface;
        private int treshold;
        private int bins;
        private int binsize;
        private int regionsize;
        private int numberofblocks;
        private int numberofblocksx;
        private int numberofblocksy;
        private int blockheight;
        private int blockwidth;
        private int[][,] prevBlockHistogram;

        #endregion

        /// <summary> File name to scan</summary>
        public LocalHistogramSDCapture(string FileName, int treshold, int bins, int regionsize)
            : base(FileName)
        {
            this.frameSurface = m_videoWidth * m_videoHeight;
            this.treshold = treshold;
            this.regionsize = regionsize;

            if (regionsize > 0)
            {
                double a = (regionsize * 1.0) / this.frameSurface;
                this.blockwidth = (int)(Math.Sqrt(a) * m_videoWidth);
                this.blockheight = (int)(Math.Sqrt(a) * m_videoHeight);

                this.numberofblocksx = (int)Math.Ceiling((m_videoWidth * 1.0 / this.blockwidth));
                this.numberofblocksy = (int)Math.Ceiling((m_videoHeight * 1.0 / this.blockheight));
                this.numberofblocks = this.numberofblocksx * this.numberofblocksy;
            }
            else
            {
                this.numberofblocksx = 3;
                this.numberofblocksy = 3;
                this.numberofblocks = this.numberofblocksx * this.numberofblocksy;

                this.blockwidth = (int)Math.Ceiling(m_videoWidth / (double)numberofblocksx);
                this.blockheight = (int)Math.Ceiling(m_videoHeight / (double)numberofblocksy);
            }

            if (256 % bins == 0)
            {
                this.bins = bins;
                this.binsize = 256 / bins;
            }
            else
            {
                this.bins = 256;
                this.binsize = 1;
            }
        }

        /// <summary> sample callback, NOT USED. </summary>
        int ISampleGrabberCB.SampleCB( double SampleTime, IMediaSample pSample )
        {
            Marshal.ReleaseComObject(pSample);
            return 0;
        }

        /// <summary> buffer callback, COULD BE FROM FOREIGN THREAD. </summary>
        unsafe int ISampleGrabberCB.BufferCB(double SampleTime, IntPtr pBuffer, int BufferLen)
        {
            // Always call base.Prepare in the start!
            base.Prepare(pBuffer);

            byte* buffer = (byte*)pBuffer.ToPointer();
            int[][,] curBlockHistogram = calclulateBlockRGBHistograms(buffer);

            // Don't do this for the first frame
            if (base.m_count != 0)
            {
                int[] difference = calculateBlockHistogramDifference(curBlockHistogram, this.prevBlockHistogram);

                if (difference[0] > this.treshold && difference[1] > this.treshold && difference[2] > this.treshold)
                {
                    base.shotDetected(pBuffer);
                }   
            }

            this.prevBlockHistogram = curBlockHistogram;

            // Always call base.Finish in the end!
            base.Finish(pBuffer, BufferLen);

            return 0;
        }


        private int[] calculateBlockHistogramDifference(int[][,] curBlockHistogram, int[][,] prevBlockHistogram)
        {
            int[,] differenceblocks = new int[3, this.numberofblocks];
            int[] difference = new int[3];

            for (int i = 0; i < 3; i++)
            {
                for (int k = 0; k < this.numberofblocks; k++)
                {
                    for (int j = 0; j < this.bins; j++)
                    {
                        differenceblocks[i,k] += Math.Abs(curBlockHistogram[k][i, j] - prevBlockHistogram[k][i, j]);
                    }
                    difference[i] += differenceblocks[i, k];
                }
                // NORMALISATIE
                difference[i] = (int)(((double)difference[i] * 100.0) / (1.0 * this.frameSurface * this.numberofblocks));
            }

            return difference;
        }



        private unsafe int[][,] calclulateBlockRGBHistograms(byte* buffer)
        {
            int[][,] histograms = new int[this.numberofblocks][,];

            for (int i = 0; i < this.numberofblocks; i++)
            {
                histograms[i] = new int[3, this.bins];
                histograms[i] = calculateRGBHistogram(buffer, i);
            }

            return histograms;
        }

        unsafe private int[,] calculateRGBHistogram(byte* current, int blocknumber)
        {
            int[,] rgbhistogram = new int[3, this.bins];
            int upperx, lowerx, uppery, lowery;

            // Determine X boundries
            lowerx = (blocknumber % this.numberofblocksx)*this.blockwidth;
            if (blocknumber % this.numberofblocksx != this.numberofblocksx - 1)
                upperx = ((blocknumber % this.numberofblocksx) + 1) * this.blockwidth;
            else
                upperx = this.m_videoWidth;

            // Determine Y boundries
            lowery = (blocknumber / this.numberofblocksx) * this.blockheight;
            if (blocknumber / this.numberofblocksx != this.numberofblocksy - 1)
                uppery = ((blocknumber / this.numberofblocksx) + 1) * this.blockheight;
            else
                uppery = this.m_videoHeight;
        

            for (int y = lowery; y < uppery; y++)
            {
                for (int x = lowerx; x < upperx; x++)
                {
                    byte[] curPixel = base.getPixel(current, x, y);
                    rgbhistogram[0, curPixel[0] / this.binsize]++;
                    rgbhistogram[1, curPixel[1] / this.binsize]++;
                    rgbhistogram[2, curPixel[2] / this.binsize]++;
                }
            }

            return rgbhistogram;
        }
    }
}
