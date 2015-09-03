using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Drawing;
using System.Data;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Solution.ShotDetection;
using Solution.Data;

namespace Solution.View
{
    public partial class PixelDifferenceSDControl : SDUserControl
    {
        public int treshold2;
        public double treshold3;

        public PixelDifferenceSDControl() : base()
        {
            InitializeComponent();
        }

        public override List<Shot> DoDetect(String fileName)
        {

            if (txtTreshold2.Text == "" || txtTreshold3.Text == "")
            {
                MessageBox.Show("Please fill in the parameters");
                return null;
            }

            // Convert the parameters
            try
            {
                treshold2 = Convert.ToInt32(txtTreshold2.Text);
                treshold3 = Convert.ToDouble(txtTreshold3.Text);
            }
            catch (FormatException)
            {
                MessageBox.Show("Could not convert parameters to their types");
                return null;
            }

            Capture capture = new PixelDifferenceSDCapture(fileName, treshold2, treshold3);

            capture.Start();
            capture.WaitUntilDone();
            capture.FinishLastShot(); 
            capture.Dispose();

            return capture.shots;
        }

        public override List<String> GetParameters()
        {
            return new List<String>() { treshold2.ToString(), treshold3.ToString() };
        }
    }
}
