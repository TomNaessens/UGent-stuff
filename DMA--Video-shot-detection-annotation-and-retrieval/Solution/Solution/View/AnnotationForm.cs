using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Solution.Data;

namespace Solution.View
{
    public partial class AnnotationForm : Form
    {
        public ShotDetectionModel shotDetectionModel;
        public Shot shot;

        public AnnotationForm(ShotDetectionModel shotDetectionModel, Shot shot)
        {
            InitializeComponent();

            this.shotDetectionModel = shotDetectionModel;
            this.shot = shot;
            txtAnnotations.Text = String.Join(", ", shot.Annotations);
        }

        private void btnOK_Click(object sender, EventArgs e)
        {
            shotDetectionModel.AnnotateShot(shot, txtAnnotations.Text);
            Close();
        }
    }
}
