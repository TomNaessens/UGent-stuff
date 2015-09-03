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
 * soft cut: +- 20
 * hard cut: +- 0.96
*/

namespace Solution.ShotDetection
{
    /// <summary> Summary description for MainForm. </summary>
    internal class GeneralizedSDCapture : Capture, ISampleGrabberCB
    {
        #region Member variables

        private double prev2Entropy;
        private double prevEntropy;
        private double currEntropy;

        private double prev2Information;
        private double prevInformation;
        private double currInformation;

        private int[,] prevHistogram;


        private double MItreshold; // treshold for Mutual Information
        private double JEtreshold; // treshold for Joint Entropy

        private int fadestart;
        #endregion

        /// <summary> File name to scan</summary>
        public GeneralizedSDCapture(string FileName, double softTreshold, double hardTreshold)
            : base(FileName)
        {

            this.MItreshold = hardTreshold;
            this.JEtreshold = softTreshold;

            this.fadestart = -1;
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
            int[,] RBGhistogram = calculateRGBHistogram(buffer);


            // Don't do this for the first frame
            if (base.m_count != 0)
            {
                int[][,] RBGTransition = calculateRGBTransition(prevBuffer, buffer);

                //mutual information
                currInformation = calculateMutualInformation(RBGTransition, prevHistogram, RBGhistogram);
                //joint entropy
                currEntropy = calculateJointEntropy(RBGTransition);

                // hard cuts
                if (currInformation > MItreshold && currInformation - prevInformation > 0.1)
                {

                    base.shotDetected(pBuffer);
                    fadestart = -1;
                }

                else if (base.m_count >= 2)
                {
                    // soft cuts (fades)
                    if (Math.Abs((currEntropy - prevEntropy) / (prevEntropy - prev2Entropy)) > JEtreshold)
                    {
                        if (fadestart == -1)
                        {
                            fadestart = m_count;
                        }
                        else if (m_count - fadestart >= 2)
                        {
                            fadestart = -1;
                            base.shotDetected(pBuffer);
                        }
                        else
                        {
                            fadestart = -1;
                        }
                    }
                }
            }

            prev2Entropy = prevEntropy;
            prevEntropy = currEntropy;

            prev2Information = prevInformation;
            prevInformation = currInformation;

            prevHistogram = RBGhistogram;


            // Always call base.Finish in the end!
            base.Finish(pBuffer, BufferLen);

            return 0;
        }

        private double calculateJointEntropy(int[][,] RBGTransition)
        {
            double RedE = calculateEntropy(RBGTransition[0]);
            double GreE = calculateEntropy(RBGTransition[1]);
            double BluE = calculateEntropy(RBGTransition[2]);

            return RedE + GreE + BluE;
        }

        private double calculateEntropy(int[,] transition)
        {
            double entropy = 0;

            for (int i = 0; i < 256; i++)
            {
                for (int j = 0; j < 256; j++)
                {
                    if (transition[i, j] != 0)
                    {
                        entropy += transition[i, j] * Math.Log10(transition[i, j]);
                    }
                }
            }

            return -entropy;
        }

        private double calculateMutualInformation(int[][,] RBGTransition, int[,] prevHistogram, int[,] RBGhistogram)
        {
            double RedI = calculateInformation(RBGTransition, prevHistogram, RBGhistogram, 0);
            double GreI = calculateInformation(RBGTransition, prevHistogram, RBGhistogram, 1);
            double BluI = calculateInformation(RBGTransition, prevHistogram, RBGhistogram, 2);

            return (RedI + GreI + BluI) / (3*m_videoHeight*m_videoWidth * Math.Log10(m_videoWidth*m_videoHeight));
        }


        private double calculateInformation(int[][,] Transition, int[,] prevHistogram, int[,] currHistogram, int comp)
        {
            double information = 0;

            for (int i = 0; i < 256; i++)
            {
                for (int j = 0; j < 256; j++)
                {
                    if (Transition[comp][i, j] != 0)
                    {
                        information += Transition[comp][i, j] * (Math.Log10(Transition[comp][i, j]) - Math.Log10(prevHistogram[comp,i]) - Math.Log10(currHistogram[comp,j]));
                    }
                }
            }

            return -information;
        }

        unsafe private byte[,] calculateTransitionMatrix(byte[] prevBuffer, byte* buffer, int component, int bufferLen)
        {
            byte[,] matrix = new byte[256,256];

            for (int i = 0; i < bufferLen; i += 3)
            {
                int prev = prevBuffer[i + component];
                int curr = buffer[i+component];
                matrix[prev, curr]++; 
            }
            return matrix;
        }
        


        unsafe private int[,] calculateRGBHistogram(byte* current)
        {
            int[,] rgbhistogram = new int[3, 256];
            for (int i = 0; i < 256; i++)
            {
                rgbhistogram[0, i] = 0;
                rgbhistogram[1, i] = 0;
                rgbhistogram[2, i] = 0;
            }

            for (int x = 0; x < m_videoWidth; x++)
            {
                for (int y = 0; y < m_videoHeight; y++)
                {
                    byte[] curPixel = base.getPixel(current, x, y);
                    rgbhistogram[0, curPixel[0]]++;
                    rgbhistogram[1, curPixel[1]]++;
                    rgbhistogram[2, curPixel[2]]++;
                }
            }

            return rgbhistogram;
        }

        private unsafe int[][,] calculateRGBTransition(byte[] prevBuffer, byte* buffer)
        {
            int[][,] rgbTransition = new int[3][,];
            rgbTransition[0] = new int[256, 256];
            rgbTransition[1] = new int[256, 256];
            rgbTransition[2] = new int[256, 256];

            for(int x = 0; x<m_videoWidth; x++)
            {
                for(int y=0;y<m_videoHeight; y++)
                {
                    fixed (byte* prevPtr = &prevBuffer[0])
                    {
                        byte[] prevPixel = base.getPixel(prevPtr, x, y);
                        byte[] currPixel = base.getPixel(buffer, x, y);
                        
                        rgbTransition[0][prevPixel[0], currPixel[0]]++;
                        rgbTransition[1][prevPixel[1], currPixel[1]]++;
                        rgbTransition[2][prevPixel[2], currPixel[2]]++;
                    }
                }
            }
            
            return rgbTransition;
        }
    }
}
