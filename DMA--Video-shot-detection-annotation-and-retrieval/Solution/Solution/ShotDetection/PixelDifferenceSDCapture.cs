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
 * treshold2: 25
 * treshold3: 93
*/

namespace Solution.ShotDetection
{
    /// <summary> Summary description for MainForm. </summary>
    internal class PixelDifferenceSDCapture : Capture, ISampleGrabberCB
    {
        #region Member variables

        private int threshold2;
        private double threshold3;

        #endregion

        /// <summary> File name to scan</summary>
        public PixelDifferenceSDCapture(string FileName, int threshold2, double threshold3) : base(FileName)
        {
            this.threshold2 = threshold2;
            this.threshold3 = threshold3;
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

            // Don't do this for the first frame
            if (base.m_count != 0)
            {
                byte* buffer = (byte*)pBuffer.ToPointer();

                double difference = calculatePixelWiseDifference(prevBuffer, buffer);

                if (difference > threshold3)
                {
                    base.shotDetected(pBuffer);
                }
            }

            // Always call base.Finish in the end!
            base.Finish(pBuffer, BufferLen);

            return 0;
        }

        unsafe private double calculatePixelWiseDifference(byte[] prev, byte* current)
        {
           double sum = 0;

           // Run over all the pixels
           for (int y = 0; y < m_videoHeight; y++)
           {
               for (int x = 0; x < m_videoWidth; x++) 
               {
                   byte[] prevPixel;
                   fixed (byte* prevPtr = &prev[0])
                   {
                       prevPixel = base.getPixel(prevPtr, x, y);
                   }
                   byte[] currPixel = base.getPixel(current, x, y);

                   sum += isSignificantDifference(prevPixel, currPixel);
                }
            }

            //normalize sum
           return sum / (m_videoWidth * m_videoHeight);
        }

        private int isSignificantDifference(byte[] prevPixel, byte[] currPixel)
        {
            int sum = 0;

            sum += Math.Abs(currPixel[0] - prevPixel[0]);
            sum += Math.Abs(currPixel[1] - prevPixel[1]);
            sum += Math.Abs(currPixel[2] - prevPixel[2]);

            return sum > threshold2 ? 1 : 0;
        }
    }
}
