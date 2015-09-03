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
 * treshold: 80
 * binsize: 32
*/

namespace Solution.ShotDetection
{
    /// <summary> Summary description for MainForm. </summary>
    internal class GlobalHistogramSDCapture : Capture, ISampleGrabberCB
    {
        #region Member variables

        private int frameSurface;

        private int treshold;
        private int bins;
        private int binsize;
        private int[,] prevHistogram;

        #endregion

        /// <summary> File name to scan</summary>
        public GlobalHistogramSDCapture(string FileName, int treshold, int bins)
            : base(FileName)
        {
            this.treshold = treshold;
            this.frameSurface = m_videoWidth * m_videoHeight;

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
            int[,] rgbhistogram = calculateRGBHistogram(buffer);

            // Don't do this for the first frame
            if (base.m_count != 0)
            {
                int[] difference = calculateHistogramDifference(rgbhistogram, this.prevHistogram);

                if (difference[0] > this.treshold && difference[1] > this.treshold && difference[2] > this.treshold)
                {
                    base.shotDetected(pBuffer);
                }
            }

            this.prevHistogram = rgbhistogram;

            // Always call base.Finish in the end!
            base.Finish(pBuffer, BufferLen);

            return 0;
        }

        /// <summary> Calculates the difference between the current and previous global histogram, returns difference array [R,G,B]</summary>
        unsafe private int[] calculateHistogramDifference(int[,] currHistogram, int[,] prevHistogram)
        {
            int[] difference = new int[3];

            for (int i = 0; i < 3; i++)
            {
                for (int j = 0; j < this.bins; j++)
                {
                    difference[i] += Math.Abs(currHistogram[i, j] - prevHistogram[i, j]);
                }
                // NORMALISATIE
                difference[i] = (int)(((double)difference[i] * 100) / (1.0 * this.frameSurface));
                //difference[i] = (int)(((double)difference[i] * 100000.0) / (1.0 * this.frameSurface * this.bins));
            }
            
            return difference;
        }

        /// <summary> Calculates a global histogram for the current frame. Returns a 2 dim array [RedHistogram[binsize], GreenHistogram[binsize], BlueHistogram[binsize]] </summary>
        unsafe private int[,] calculateRGBHistogram(byte* current)
        {
            int[,] rgbhistogram = new int[3, this.bins];

            for (int x = 0; x < m_videoWidth; x++)
            {
                for (int y = 0; y < m_videoHeight; y++)
                {
                    byte [] curPixel = base.getPixel(current, x, y);
                    rgbhistogram[0, curPixel[0] / this.binsize]++;
                    rgbhistogram[1, curPixel[1] / this.binsize]++;
                    rgbhistogram[2, curPixel[2] / this.binsize]++;
                }
            }

            return rgbhistogram;
        }
    }
}
