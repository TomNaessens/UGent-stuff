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
    public partial class MotionEstimationSDControl : SDUserControl
    {
        public int treshold;
        public int blocksize;
        public int swsize;

        public MotionEstimationSDControl()
        {
            InitializeComponent();
        }

        public override List<Shot> DoDetect(String fileName)
        {

            if (txtTreshold.Text == "" || txtBlockSize.Text == "" || txtSWSize.Text == "")
            {
                MessageBox.Show("Please fill in the parameters");
                return null;
            }

            // Convert the parameters
            try
            {
                treshold = Convert.ToInt32(txtTreshold.Text);
                blocksize = Convert.ToInt32(txtBlockSize.Text);
                swsize = Convert.ToInt32(txtSWSize.Text);
            }
            catch (FormatException)
            {
                MessageBox.Show("Could not convert parameters to integers");
                return null;
            }

            Capture capture = new MotionEstimationSDCapture(fileName, treshold, blocksize, swsize);

            capture.Start();
            capture.WaitUntilDone();
            capture.FinishLastShot(); 
            capture.Dispose();

            return capture.shots;
        }

        public override List<String> GetParameters()
        {
            return new List<String>() { treshold.ToString(), blocksize.ToString(), swsize.ToString() };
        }
    }
}
