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
    public partial class GeneralizedSDControl : SDUserControl
    {
        public double softTresh;
        public double hardTresh;

        public GeneralizedSDControl()
        {
            InitializeComponent();
        }

        public override List<Shot> DoDetect(String fileName)
        {
            if (txtSoftCuts.Text == "" || txtHardCuts.Text == "")
            {
                MessageBox.Show("Please fill in the parameters");
                return null;
            }


            // Convert the parameters
            try
            {
                softTresh = Convert.ToDouble(txtSoftCuts.Text);
                hardTresh = Convert.ToDouble(txtHardCuts.Text);
            }
            catch (FormatException)
            {
                MessageBox.Show("Could not convert parameters to integers");
                return null;
            }

            Capture capture = new GeneralizedSDCapture(fileName, softTresh, hardTresh);

            capture.Start();
            capture.WaitUntilDone();
            capture.FinishLastShot(); 
            capture.Dispose();

            return capture.shots;
        }

        public override List<String> GetParameters()
        {
            return new List<String>() { softTresh.ToString(), hardTresh.ToString() };
        }
    }
}
