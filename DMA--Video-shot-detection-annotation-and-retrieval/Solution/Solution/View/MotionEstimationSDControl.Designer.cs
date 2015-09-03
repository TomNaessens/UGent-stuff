namespace Solution.View
{
    partial class MotionEstimationSDControl
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

        #region Component Designer generated code

        /// <summary> 
        /// Required method for Designer support - do not modify 
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.label1 = new System.Windows.Forms.Label();
            this.lblTreshold = new System.Windows.Forms.Label();
            this.lblBlocksize = new System.Windows.Forms.Label();
            this.label4 = new System.Windows.Forms.Label();
            this.txtTreshold = new System.Windows.Forms.TextBox();
            this.txtBlockSize = new System.Windows.Forms.TextBox();
            this.txtSWSize = new System.Windows.Forms.TextBox();
            this.SuspendLayout();
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label1.Location = new System.Drawing.Point(3, 0);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(151, 13);
            this.label1.TabIndex = 0;
            this.label1.Text = "Motion estimation method";
            // 
            // lblTreshold
            // 
            this.lblTreshold.AutoSize = true;
            this.lblTreshold.Location = new System.Drawing.Point(10, 40);
            this.lblTreshold.Name = "lblTreshold";
            this.lblTreshold.Size = new System.Drawing.Size(51, 13);
            this.lblTreshold.TabIndex = 1;
            this.lblTreshold.Text = "Treshold:";
            // 
            // lblBlocksize
            // 
            this.lblBlocksize.AutoSize = true;
            this.lblBlocksize.Location = new System.Drawing.Point(10, 66);
            this.lblBlocksize.Name = "lblBlocksize";
            this.lblBlocksize.Size = new System.Drawing.Size(55, 13);
            this.lblBlocksize.TabIndex = 2;
            this.lblBlocksize.Text = "Blocksize:";
            // 
            // label4
            // 
            this.label4.AutoSize = true;
            this.label4.Location = new System.Drawing.Point(10, 92);
            this.label4.Name = "label4";
            this.label4.Size = new System.Drawing.Size(51, 13);
            this.label4.TabIndex = 3;
            this.label4.Text = "SW Size:";
            // 
            // txtTreshold
            // 
            this.txtTreshold.Location = new System.Drawing.Point(80, 37);
            this.txtTreshold.Name = "txtTreshold";
            this.txtTreshold.Size = new System.Drawing.Size(100, 20);
            this.txtTreshold.TabIndex = 4;
            // 
            // txtBlockSize
            // 
            this.txtBlockSize.Location = new System.Drawing.Point(80, 63);
            this.txtBlockSize.Name = "txtBlockSize";
            this.txtBlockSize.Size = new System.Drawing.Size(100, 20);
            this.txtBlockSize.TabIndex = 5;
            // 
            // txtSWSize
            // 
            this.txtSWSize.Location = new System.Drawing.Point(80, 89);
            this.txtSWSize.Name = "txtSWSize";
            this.txtSWSize.Size = new System.Drawing.Size(100, 20);
            this.txtSWSize.TabIndex = 6;
            // 
            // MotionEstimationSDControl
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.Controls.Add(this.txtSWSize);
            this.Controls.Add(this.txtBlockSize);
            this.Controls.Add(this.txtTreshold);
            this.Controls.Add(this.label4);
            this.Controls.Add(this.lblBlocksize);
            this.Controls.Add(this.lblTreshold);
            this.Controls.Add(this.label1);
            this.Name = "MotionEstimationSDControl";
            this.Size = new System.Drawing.Size(225, 125);
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label lblTreshold;
        private System.Windows.Forms.Label lblBlocksize;
        private System.Windows.Forms.Label label4;
        private System.Windows.Forms.TextBox txtTreshold;
        private System.Windows.Forms.TextBox txtBlockSize;
        private System.Windows.Forms.TextBox txtSWSize;
    }
}
