using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Drawing;
using System.Data;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Solution.Data;
using Solution.ShotDetection;

namespace Solution.View
{
    public partial class LocalHistogramSDControl : SDUserControl
    {
        public int treshold;
        public int bins;
        public int regionsize;

        public LocalHistogramSDControl()
        {
            InitializeComponent();
        }

        public override List<Shot> DoDetect(String fileName)
        {


            if (txtTreshold.Text == "" || txtBins.Text == "" || txtRegionSize.Text == "")
            {
                MessageBox.Show("Please fill in the parameters");
                return null;
            }

            // Convert the parameters
            try
            {
                treshold = Convert.ToInt32(txtTreshold.Text);
                bins = Convert.ToInt32(txtBins.Text);
                regionsize = Convert.ToInt32(txtRegionSize.Text);
            }
            catch (FormatException)
            {
                MessageBox.Show("Could not convert parameters to integers");
                return null;
            }

            Capture capture = new LocalHistogramSDCapture(fileName, treshold, bins, regionsize);

            capture.Start();
            capture.WaitUntilDone();
            capture.FinishLastShot(); 
            capture.Dispose();

            return capture.shots;
        }

        public override List<String> GetParameters()
        {
            return new List<String>() { treshold.ToString(), bins.ToString(), regionsize.ToString() };
        }
    }
}
