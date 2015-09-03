namespace Solution.View
{
    partial class MediaPlayer
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.menuMain = new System.Windows.Forms.MenuStrip();
            this.fileToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
            this.openToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
            this.closeToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
            this.lblCurrentFileTitle = new System.Windows.Forms.Label();
            this.lblCurrentFile = new System.Windows.Forms.Label();
            this.openFileDialog = new System.Windows.Forms.OpenFileDialog();
            this.videoPanel = new System.Windows.Forms.Panel();
            this.btnRewind = new System.Windows.Forms.Button();
            this.btnPlay = new System.Windows.Forms.Button();
            this.btnStop = new System.Windows.Forms.Button();
            this.btnPause = new System.Windows.Forms.Button();
            this.groupBox1 = new System.Windows.Forms.GroupBox();
            this.lblStatus = new System.Windows.Forms.Label();
            this.label3 = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.btnDetect = new System.Windows.Forms.Button();
            this.pnlParameters = new System.Windows.Forms.Panel();
            this.cmbMethod = new System.Windows.Forms.ComboBox();
            this.label1 = new System.Windows.Forms.Label();
            this.btnExportFrames = new System.Windows.Forms.Button();
            this.btnExportToXML = new System.Windows.Forms.Button();
            this.folderBrowserDialog = new System.Windows.Forms.FolderBrowserDialog();
            this.groupBox2 = new System.Windows.Forms.GroupBox();
            this.btnPlayShot = new System.Windows.Forms.Button();
            this.btnAnnotate = new System.Windows.Forms.Button();
            this.lstShots = new System.Windows.Forms.ListBox();
            this.saveFileDialog = new System.Windows.Forms.SaveFileDialog();
            this.label4 = new System.Windows.Forms.Label();
            this.txtFilter = new System.Windows.Forms.TextBox();
            this.menuMain.SuspendLayout();
            this.groupBox1.SuspendLayout();
            this.groupBox2.SuspendLayout();
            this.SuspendLayout();
            // 
            // menuMain
            // 
            this.menuMain.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.fileToolStripMenuItem});
            this.menuMain.Location = new System.Drawing.Point(0, 0);
            this.menuMain.Name = "menuMain";
            this.menuMain.Size = new System.Drawing.Size(962, 24);
            this.menuMain.TabIndex = 0;
            this.menuMain.Text = "menuMain";
            // 
            // fileToolStripMenuItem
            // 
            this.fileToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.openToolStripMenuItem,
            this.closeToolStripMenuItem});
            this.fileToolStripMenuItem.Name = "fileToolStripMenuItem";
            this.fileToolStripMenuItem.Size = new System.Drawing.Size(37, 20);
            this.fileToolStripMenuItem.Text = "File";
            // 
            // openToolStripMenuItem
            // 
            this.openToolStripMenuItem.Name = "openToolStripMenuItem";
            this.openToolStripMenuItem.Size = new System.Drawing.Size(112, 22);
            this.openToolStripMenuItem.Text = "Open...";
            this.openToolStripMenuItem.Click += new System.EventHandler(this.openToolStripMenuItem_Click);
            // 
            // closeToolStripMenuItem
            // 
            this.closeToolStripMenuItem.Name = "closeToolStripMenuItem";
            this.closeToolStripMenuItem.Size = new System.Drawing.Size(112, 22);
            this.closeToolStripMenuItem.Text = "Close";
            this.closeToolStripMenuItem.Click += new System.EventHandler(this.closeToolStripMenuItem_Click);
            // 
            // lblCurrentFileTitle
            // 
            this.lblCurrentFileTitle.AutoSize = true;
            this.lblCurrentFileTitle.Location = new System.Drawing.Point(13, 28);
            this.lblCurrentFileTitle.Name = "lblCurrentFileTitle";
            this.lblCurrentFileTitle.Size = new System.Drawing.Size(60, 13);
            this.lblCurrentFileTitle.TabIndex = 1;
            this.lblCurrentFileTitle.Text = "Current file:";
            // 
            // lblCurrentFile
            // 
            this.lblCurrentFile.AutoSize = true;
            this.lblCurrentFile.Location = new System.Drawing.Point(80, 28);
            this.lblCurrentFile.Name = "lblCurrentFile";
            this.lblCurrentFile.Size = new System.Drawing.Size(233, 13);
            this.lblCurrentFile.TabIndex = 2;
            this.lblCurrentFile.Text = "To open a file, select File > Open from the menu";
            // 
            // openFileDialog
            // 
            this.openFileDialog.FileName = "openFileDialog";
            // 
            // videoPanel
            // 
            this.videoPanel.BackColor = System.Drawing.SystemColors.ActiveCaptionText;
            this.videoPanel.Location = new System.Drawing.Point(16, 59);
            this.videoPanel.Name = "videoPanel";
            this.videoPanel.Size = new System.Drawing.Size(372, 192);
            this.videoPanel.TabIndex = 3;
            // 
            // btnRewind
            // 
            this.btnRewind.Enabled = false;
            this.btnRewind.Location = new System.Drawing.Point(16, 257);
            this.btnRewind.Name = "btnRewind";
            this.btnRewind.Size = new System.Drawing.Size(66, 33);
            this.btnRewind.TabIndex = 4;
            this.btnRewind.Text = "Rewind";
            this.btnRewind.UseVisualStyleBackColor = true;
            this.btnRewind.Click += new System.EventHandler(this.btnRewind_Click);
            // 
            // btnPlay
            // 
            this.btnPlay.Enabled = false;
            this.btnPlay.Location = new System.Drawing.Point(141, 257);
            this.btnPlay.Name = "btnPlay";
            this.btnPlay.Size = new System.Drawing.Size(47, 33);
            this.btnPlay.TabIndex = 6;
            this.btnPlay.Text = "Play";
            this.btnPlay.UseVisualStyleBackColor = true;
            this.btnPlay.Click += new System.EventHandler(this.btnPlay_Click);
            // 
            // btnStop
            // 
            this.btnStop.Enabled = false;
            this.btnStop.Location = new System.Drawing.Point(247, 258);
            this.btnStop.Name = "btnStop";
            this.btnStop.Size = new System.Drawing.Size(47, 33);
            this.btnStop.TabIndex = 7;
            this.btnStop.Text = "Stop";
            this.btnStop.UseVisualStyleBackColor = true;
            this.btnStop.Click += new System.EventHandler(this.btnStop_Click);
            // 
            // btnPause
            // 
            this.btnPause.Enabled = false;
            this.btnPause.Location = new System.Drawing.Point(194, 258);
            this.btnPause.Name = "btnPause";
            this.btnPause.Size = new System.Drawing.Size(47, 33);
            this.btnPause.TabIndex = 10;
            this.btnPause.Text = "Pause";
            this.btnPause.UseVisualStyleBackColor = true;
            this.btnPause.Click += new System.EventHandler(this.btnPause_Click);
            // 
            // groupBox1
            // 
            this.groupBox1.Controls.Add(this.lblStatus);
            this.groupBox1.Controls.Add(this.label3);
            this.groupBox1.Controls.Add(this.label2);
            this.groupBox1.Controls.Add(this.btnDetect);
            this.groupBox1.Controls.Add(this.pnlParameters);
            this.groupBox1.Controls.Add(this.cmbMethod);
            this.groupBox1.Controls.Add(this.label1);
            this.groupBox1.Location = new System.Drawing.Point(394, 27);
            this.groupBox1.Name = "groupBox1";
            this.groupBox1.Size = new System.Drawing.Size(325, 277);
            this.groupBox1.TabIndex = 11;
            this.groupBox1.TabStop = false;
            this.groupBox1.Text = "ShotDetection";
            // 
            // lblStatus
            // 
            this.lblStatus.AutoSize = true;
            this.lblStatus.Location = new System.Drawing.Point(56, 228);
            this.lblStatus.Name = "lblStatus";
            this.lblStatus.Size = new System.Drawing.Size(0, 13);
            this.lblStatus.TabIndex = 6;
            // 
            // label3
            // 
            this.label3.AutoSize = true;
            this.label3.Location = new System.Drawing.Point(10, 228);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(40, 13);
            this.label3.TabIndex = 5;
            this.label3.Text = "Status:";
            // 
            // label2
            // 
            this.label2.AutoSize = true;
            this.label2.Location = new System.Drawing.Point(91, 203);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(111, 13);
            this.label2.TabIndex = 4;
            this.label2.Text = "This can take a while!";
            // 
            // btnDetect
            // 
            this.btnDetect.Location = new System.Drawing.Point(10, 198);
            this.btnDetect.Name = "btnDetect";
            this.btnDetect.Size = new System.Drawing.Size(75, 23);
            this.btnDetect.TabIndex = 3;
            this.btnDetect.Text = "Detect!";
            this.btnDetect.UseVisualStyleBackColor = true;
            this.btnDetect.Click += new System.EventHandler(this.btnDetect_Click);
            // 
            // pnlParameters
            // 
            this.pnlParameters.Location = new System.Drawing.Point(10, 44);
            this.pnlParameters.Name = "pnlParameters";
            this.pnlParameters.Size = new System.Drawing.Size(309, 147);
            this.pnlParameters.TabIndex = 2;
            // 
            // cmbMethod
            // 
            this.cmbMethod.FormattingEnabled = true;
            this.cmbMethod.Location = new System.Drawing.Point(59, 17);
            this.cmbMethod.Name = "cmbMethod";
            this.cmbMethod.Size = new System.Drawing.Size(154, 21);
            this.cmbMethod.TabIndex = 1;
            this.cmbMethod.SelectedIndexChanged += new System.EventHandler(this.cmbMethod_SelectedIndexChanged);
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.Location = new System.Drawing.Point(7, 20);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(46, 13);
            this.label1.TabIndex = 0;
            this.label1.Text = "Method:";
            // 
            // btnExportFrames
            // 
            this.btnExportFrames.Location = new System.Drawing.Point(102, 247);
            this.btnExportFrames.Name = "btnExportFrames";
            this.btnExportFrames.Size = new System.Drawing.Size(79, 23);
            this.btnExportFrames.TabIndex = 8;
            this.btnExportFrames.Text = "Export frames";
            this.btnExportFrames.UseVisualStyleBackColor = true;
            this.btnExportFrames.Click += new System.EventHandler(this.btnExportFrames_Click);
            // 
            // btnExportToXML
            // 
            this.btnExportToXML.Location = new System.Drawing.Point(6, 247);
            this.btnExportToXML.Name = "btnExportToXML";
            this.btnExportToXML.Size = new System.Drawing.Size(90, 23);
            this.btnExportToXML.TabIndex = 7;
            this.btnExportToXML.Text = "Export to XML";
            this.btnExportToXML.UseVisualStyleBackColor = true;
            this.btnExportToXML.Click += new System.EventHandler(this.btnExportToXML_Click);
            // 
            // groupBox2
            // 
            this.groupBox2.Controls.Add(this.txtFilter);
            this.groupBox2.Controls.Add(this.label4);
            this.groupBox2.Controls.Add(this.btnPlayShot);
            this.groupBox2.Controls.Add(this.btnAnnotate);
            this.groupBox2.Controls.Add(this.lstShots);
            this.groupBox2.Controls.Add(this.btnExportFrames);
            this.groupBox2.Controls.Add(this.btnExportToXML);
            this.groupBox2.Location = new System.Drawing.Point(726, 28);
            this.groupBox2.Name = "groupBox2";
            this.groupBox2.Size = new System.Drawing.Size(224, 276);
            this.groupBox2.TabIndex = 12;
            this.groupBox2.TabStop = false;
            this.groupBox2.Text = "Shots";
            // 
            // btnPlayShot
            // 
            this.btnPlayShot.Location = new System.Drawing.Point(102, 211);
            this.btnPlayShot.Name = "btnPlayShot";
            this.btnPlayShot.Size = new System.Drawing.Size(90, 23);
            this.btnPlayShot.TabIndex = 11;
            this.btnPlayShot.Text = "Play shot";
            this.btnPlayShot.UseVisualStyleBackColor = true;
            this.btnPlayShot.Click += new System.EventHandler(this.btnPlayShot_Click);
            // 
            // btnAnnotate
            // 
            this.btnAnnotate.Location = new System.Drawing.Point(6, 211);
            this.btnAnnotate.Name = "btnAnnotate";
            this.btnAnnotate.Size = new System.Drawing.Size(90, 23);
            this.btnAnnotate.TabIndex = 10;
            this.btnAnnotate.Text = "Annotate shot";
            this.btnAnnotate.UseVisualStyleBackColor = true;
            this.btnAnnotate.Click += new System.EventHandler(this.btnAnnotate_Click);
            // 
            // lstShots
            // 
            this.lstShots.FormattingEnabled = true;
            this.lstShots.Location = new System.Drawing.Point(6, 45);
            this.lstShots.Name = "lstShots";
            this.lstShots.Size = new System.Drawing.Size(212, 160);
            this.lstShots.TabIndex = 9;
            // 
            // saveFileDialog
            // 
            this.saveFileDialog.FileName = "ShotInfo.xml";
            this.saveFileDialog.Filter = "\"XML files (*.xml)|*.xml\"";
            // 
            // label4
            // 
            this.label4.AutoSize = true;
            this.label4.Location = new System.Drawing.Point(7, 19);
            this.label4.Name = "label4";
            this.label4.Size = new System.Drawing.Size(44, 13);
            this.label4.TabIndex = 12;
            this.label4.Text = "Search:";
            // 
            // txtFilter
            // 
            this.txtFilter.Location = new System.Drawing.Point(57, 16);
            this.txtFilter.Name = "txtFilter";
            this.txtFilter.Size = new System.Drawing.Size(100, 20);
            this.txtFilter.TabIndex = 13;
            this.txtFilter.TextChanged += new System.EventHandler(this.txtFilter_TextChanged);
            // 
            // MediaPlayer
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.ClientSize = new System.Drawing.Size(962, 313);
            this.Controls.Add(this.groupBox2);
            this.Controls.Add(this.groupBox1);
            this.Controls.Add(this.btnPause);
            this.Controls.Add(this.btnStop);
            this.Controls.Add(this.btnPlay);
            this.Controls.Add(this.btnRewind);
            this.Controls.Add(this.videoPanel);
            this.Controls.Add(this.lblCurrentFile);
            this.Controls.Add(this.lblCurrentFileTitle);
            this.Controls.Add(this.menuMain);
            this.MainMenuStrip = this.menuMain;
            this.Name = "MediaPlayer";
            this.Text = "MediaPlayer";
            this.menuMain.ResumeLayout(false);
            this.menuMain.PerformLayout();
            this.groupBox1.ResumeLayout(false);
            this.groupBox1.PerformLayout();
            this.groupBox2.ResumeLayout(false);
            this.groupBox2.PerformLayout();
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.MenuStrip menuMain;
        private System.Windows.Forms.ToolStripMenuItem fileToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem openToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem closeToolStripMenuItem;
        private System.Windows.Forms.Label lblCurrentFileTitle;
        private System.Windows.Forms.Label lblCurrentFile;
        private System.Windows.Forms.OpenFileDialog openFileDialog;
        private System.Windows.Forms.Panel videoPanel;
        private System.Windows.Forms.Button btnRewind;
        private System.Windows.Forms.Button btnPlay;
        private System.Windows.Forms.Button btnStop;
        private System.Windows.Forms.Button btnPause;
        private System.Windows.Forms.GroupBox groupBox1;
        private System.Windows.Forms.ComboBox cmbMethod;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Panel pnlParameters;
        private System.Windows.Forms.Label lblStatus;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Button btnDetect;
        private System.Windows.Forms.FolderBrowserDialog folderBrowserDialog;
        private System.Windows.Forms.Button btnExportFrames;
        private System.Windows.Forms.Button btnExportToXML;
        private System.Windows.Forms.GroupBox groupBox2;
        private System.Windows.Forms.ListBox lstShots;
        private System.Windows.Forms.Button btnAnnotate;
        private System.Windows.Forms.Button btnPlayShot;
        private System.Windows.Forms.SaveFileDialog saveFileDialog;
        private System.Windows.Forms.TextBox txtFilter;
        private System.Windows.Forms.Label label4;
    }
}