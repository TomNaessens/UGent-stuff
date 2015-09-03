namespace Solution.View
{
    partial class LocalHistogramSDControl
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
            this.label2 = new System.Windows.Forms.Label();
            this.label3 = new System.Windows.Forms.Label();
            this.label4 = new System.Windows.Forms.Label();
            this.txtTreshold = new System.Windows.Forms.TextBox();
            this.txtBins = new System.Windows.Forms.TextBox();
            this.txtRegionSize = new System.Windows.Forms.TextBox();
            this.SuspendLayout();
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label1.Location = new System.Drawing.Point(3, 0);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(141, 13);
            this.label1.TabIndex = 0;
            this.label1.Text = "Local histogram method";
            // 
            // label2
            // 
            this.label2.AutoSize = true;
            this.label2.Location = new System.Drawing.Point(17, 31);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(51, 13);
            this.label2.TabIndex = 1;
            this.label2.Text = "Treshold:";
            // 
            // label3
            // 
            this.label3.AutoSize = true;
            this.label3.Location = new System.Drawing.Point(17, 57);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(37, 13);
            this.label3.TabIndex = 2;
            this.label3.Text = "#Bins:";
            // 
            // label4
            // 
            this.label4.AutoSize = true;
            this.label4.Location = new System.Drawing.Point(17, 83);
            this.label4.Name = "label4";
            this.label4.Size = new System.Drawing.Size(65, 13);
            this.label4.TabIndex = 3;
            this.label4.Text = "Region size:";
            // 
            // txtTreshold
            // 
            this.txtTreshold.Location = new System.Drawing.Point(85, 28);
            this.txtTreshold.Name = "txtTreshold";
            this.txtTreshold.Size = new System.Drawing.Size(100, 20);
            this.txtTreshold.TabIndex = 4;
            // 
            // txtBins
            // 
            this.txtBins.Location = new System.Drawing.Point(85, 54);
            this.txtBins.Name = "txtBins";
            this.txtBins.Size = new System.Drawing.Size(100, 20);
            this.txtBins.TabIndex = 5;
            // 
            // txtRegionSize
            // 
            this.txtRegionSize.Location = new System.Drawing.Point(85, 80);
            this.txtRegionSize.Name = "txtRegionSize";
            this.txtRegionSize.Size = new System.Drawing.Size(100, 20);
            this.txtRegionSize.TabIndex = 6;
            // 
            // LocalHistogramSDControl
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.Controls.Add(this.txtRegionSize);
            this.Controls.Add(this.txtBins);
            this.Controls.Add(this.txtTreshold);
            this.Controls.Add(this.label4);
            this.Controls.Add(this.label3);
            this.Controls.Add(this.label2);
            this.Controls.Add(this.label1);
            this.Name = "LocalHistogramSDControl";
            this.Size = new System.Drawing.Size(225, 125);
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Label label4;
        private System.Windows.Forms.TextBox txtTreshold;
        private System.Windows.Forms.TextBox txtBins;
        private System.Windows.Forms.TextBox txtRegionSize;
    }
}
