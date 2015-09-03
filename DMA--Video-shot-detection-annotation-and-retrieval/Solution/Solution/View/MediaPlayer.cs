using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Solution.Data;
using System.Diagnostics;

namespace Solution.View
{
    public partial class MediaPlayer : Form
    {

        VideoModel videoModel;
        ShotDetectionModel shotDetectionModel;

        public MediaPlayer()
        {
            InitializeComponent();

            videoModel = new VideoModel();

            shotDetectionModel = new ShotDetectionModel(lstShots);

            cmbMethod.DataSource = shotDetectionModel.DetectionItems;

            pnlParameters.Controls.Add(shotDetectionModel.DetectionItems[0].SDUserControl);
        }

        private void openToolStripMenuItem_Click(object sender, EventArgs e)
        {
            DialogResult dialogResult = openFileDialog.ShowDialog();
            if (dialogResult == DialogResult.OK)
            {
                String fileName = openFileDialog.FileName;

                if (videoModel.loadVideo(fileName, videoPanel))
                { // Successfull load
                    lblCurrentFile.Text = fileName;

                    btnPlay.Enabled = true;
                }
                else
                { // Error upon loading
                    lblCurrentFile.Text = "Error loading file.";

                    btnRewind.Enabled = false;
                    btnPlay.Enabled = false;
                    btnPause.Enabled = false;
                    btnStop.Enabled = false;
                }
            }
        }

        private void closeToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Dispose();
            Close();
        }

        private void btnPlay_Click(object sender, EventArgs e)
        {
            videoModel.playVideo();
            btnRewind.Enabled = true;
            btnPlay.Enabled = false;
            btnStop.Enabled = true;
            btnPause.Enabled = true;
        }


        private void btnPlayShot_Click(object sender, EventArgs e)
        {
            Shot shot = (Shot) lstShots.SelectedItem;

            if (shot != null)
            {
                videoModel.playShot(shot);

                btnStop.Enabled = true;
                btnPause.Enabled = true;
            }
        }

        private void btnPause_Click(object sender, EventArgs e)
        {
            videoModel.pauseVideo();
            btnPause.Enabled = false;
            btnPlay.Enabled = true;
        }

        private void btnStop_Click(object sender, EventArgs e)
        {
            videoModel.stopVideo(); 
            btnPlay.Enabled = true;
            btnStop.Enabled = false;
            btnPause.Enabled = false;
        }

        private void btnRewind_Click(object sender, EventArgs e)
        {
            videoModel.rewindVideo();
        }

        private void cmbMethod_SelectedIndexChanged(object sender, EventArgs e)
        {
            pnlParameters.Controls.Clear();
            pnlParameters.Controls.Add(shotDetectionModel.DetectionItems[cmbMethod.SelectedIndex].SDUserControl);
        }

        private void btnDetect_Click(object sender, EventArgs e)
        {
            if (videoModel.Filename == null)
            {
                MessageBox.Show("Open a file first!");
                return;
            }

            Cursor.Current = Cursors.WaitCursor;
            lblStatus.Text = "Detecting...";

            Stopwatch stopWatch = new Stopwatch();
            stopWatch.Start();
            List<Shot> shots = shotDetectionModel.DetectionItems[cmbMethod.SelectedIndex].SDUserControl.DoDetect(videoModel.Filename);
            stopWatch.Stop();

            lblStatus.Text = "Processing results...";
            shotDetectionModel.Shots = shots;

            shotDetectionModel.usedMethod = shotDetectionModel.DetectionItems[cmbMethod.SelectedIndex];

            shotDetectionModel.FilterList("");
            
            Cursor.Current = Cursors.Default;
            lblStatus.Text = "Done! Elapsed time: " + stopWatch.ElapsedMilliseconds + "ms";
        }

        private void btnExportFrames_Click(object sender, EventArgs e)
        {
            if (folderBrowserDialog.ShowDialog(this) == DialogResult.OK && folderBrowserDialog.SelectedPath != "")
            {
                shotDetectionModel.ExportShots(folderBrowserDialog.SelectedPath);
            }
        }

        private void btnAnnotate_Click(object sender, EventArgs e)
        {

            Shot shot = (Shot) lstShots.SelectedItem;

            if (shot != null)
            {
                AnnotationForm annotationForm = new AnnotationForm(shotDetectionModel, shot);
                annotationForm.ShowDialog(this);
            }
        }

        private void btnExportToXML_Click(object sender, EventArgs e)
        {
            if (shotDetectionModel.Shots.Count != 0)
            {
                if (saveFileDialog.ShowDialog(this) == DialogResult.OK && saveFileDialog.FileName != "")
                {
                    shotDetectionModel.ExportInfo(videoModel.Filename, saveFileDialog.FileName);
                }
            }
        }

        private void txtFilter_TextChanged(object sender, EventArgs e)
        {
            shotDetectionModel.FilterList(txtFilter.Text);
        }
    }
}
