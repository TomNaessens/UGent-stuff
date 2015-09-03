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
 * treshold: 2
 * blocksize: 16
 * searchwindow: 8
*/
namespace Solution.ShotDetection
{
    /// <summary> Summary description for MainForm. </summary>
    internal class MotionEstimationSDCapture : Capture, ISampleGrabberCB
    {
        #region Member variables
        
        int treshold; 
        int blocksize; 
        int searchwindowsize;
        
        #endregion

        /// <summary> File name to scan</summary>
        public MotionEstimationSDCapture(string FileName, int treshold, int blocksize, int searchwindowsize)
            : base(FileName)
        {
            this.treshold = treshold;
            this.blocksize = blocksize;
            this.searchwindowsize = searchwindowsize;
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
            base.Prepare(pBuffer);

            // Don't do this for the first frame
            if (base.m_count != 0)
            {
                byte* buffer = (byte*)pBuffer.ToPointer();

                double motionEstimation = calculateMotionEstimation(prevBuffer, buffer);

                if (motionEstimation > treshold)
                {
                    base.shotDetected(pBuffer);
                }
            }

            // Always call base.Finish in the end!
            base.Finish(pBuffer, BufferLen);

            return 0;
        }

        unsafe private double calculateMotionEstimation(byte[] prev, byte* current)
        {
            int blockDifference = 0;

            // loop trough all blocks in frame
            for (int i = 0; i < m_videoWidth; i += blocksize)
            {
                for (int j = 0; j < m_videoHeight; j += blocksize)
                {
                    blockDifference += calculateBlockWiseDifference(prev, current, i, j);
                }
            }

            return (10.0 * blockDifference) / (m_videoHeight * m_videoWidth * 256 * 3);
        }

        unsafe private int calculateBlockWiseDifference(byte[] prev, byte* current, int block_x_start, int block_y_start)
        {
            int width_start = block_x_start - searchwindowsize;
            int width_end = block_x_start + searchwindowsize;

            int height_start = block_y_start - searchwindowsize;
            int height_end = block_y_start + searchwindowsize;

            byte[] block;
            byte[] prevBlock = getBlock(current, block_x_start, block_y_start, blocksize);

            int bestPassendDifferenct = int.MaxValue;

            //loop trough all blocks to match
            for (int i = width_start; i < width_end; i+=blocksize/2)
            {
                for (int j = height_start; j < height_end; j+=blocksize/2)
                {
                    fixed (byte* prevPtr = &prev[0])
                    {

                        block = getBlock(prevPtr, i, height_end, blocksize);

                        int res = calculateBlockDifference(prevBlock, block);

                        if (res < bestPassendDifferenct)
                        {
                            bestPassendDifferenct = res;
                        }
                    }
                }
            }
            
            return bestPassendDifferenct;
        }

        private int calculateBlockDifference(byte[] prev, byte[] current)
        {
            int sum = 0;

            for (int i = 0; i < blocksize* blocksize * 3; i++)
            {
                sum += Math.Abs(prev[i] - current[i]);
            }
            return sum;
        }


        unsafe public byte[] getBlock(byte* buffer, int x, int y, int size)
        {
            byte[] block = new byte[size * size * 3];

            // loop trough all needed pixels
            for (int i = 0; i < size; i++)
            {
                for (int j = 0; j < size; j++)
                {

                    if (x+i >= 0 && x+i < m_videoWidth &&
                        y+j >= 0 && y+j < m_videoHeight)
                    {
                        byte[] pixel = getPixel(buffer, x + i, y + j);

                        block[(j * size + i) * 3] = pixel[0];
                        block[(j * size + i) * 3 + 1] = pixel[1];
                        block[(j * size + i) * 3 + 2] = pixel[2];
                    }
                    else
                    {
                        block[(j * size + i) * 3] = 0;
                        block[(j * size + i) * 3 + 1] = 0;
                        block[(j * size + i) * 3 + 2] = 0;
                    }
                }
            }

            return block;
        } 
    }
}
