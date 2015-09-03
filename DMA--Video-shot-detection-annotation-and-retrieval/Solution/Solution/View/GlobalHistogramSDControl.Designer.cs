namespace Solution.View
{
    partial class GlobalHistogramSDControl
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
            this.label50 = new System.Windows.Forms.Label();
            this.label3 = new System.Windows.Forms.Label();
            this.txtTreshold = new System.Windows.Forms.TextBox();
            this.txtBins = new System.Windows.Forms.TextBox();
            this.SuspendLayout();
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label1.Location = new System.Drawing.Point(4, 4);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(146, 13);
            this.label1.TabIndex = 0;
            this.label1.Text = "Global histogram method";
            // 
            // label50
            // 
            this.label50.AutoSize = true;
            this.label50.Location = new System.Drawing.Point(4, 32);
            this.label50.Name = "label50";
            this.label50.Size = new System.Drawing.Size(51, 13);
            this.label50.TabIndex = 1;
            this.label50.Text = "Treshold:";
            // 
            // label3
            // 
            this.label3.AutoSize = true;
            this.label3.Location = new System.Drawing.Point(4, 58);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(37, 13);
            this.label3.TabIndex = 2;
            this.label3.Text = "#Bins:";
            // 
            // txtTreshold
            // 
            this.txtTreshold.Location = new System.Drawing.Point(70, 29);
            this.txtTreshold.Name = "txtTreshold";
            this.txtTreshold.Size = new System.Drawing.Size(100, 20);
            this.txtTreshold.TabIndex = 3;
            // 
            // txtBins
            // 
            this.txtBins.Location = new System.Drawing.Point(70, 55);
            this.txtBins.Name = "txtBins";
            this.txtBins.Size = new System.Drawing.Size(100, 20);
            this.txtBins.TabIndex = 4;
            // 
            // GlobalHistogramSDControl
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.Controls.Add(this.txtBins);
            this.Controls.Add(this.txtTreshold);
            this.Controls.Add(this.label3);
            this.Controls.Add(this.label50);
            this.Controls.Add(this.label1);
            this.Name = "GlobalHistogramSDControl";
            this.Size = new System.Drawing.Size(225, 125);
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label label50;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.TextBox txtTreshold;
        private System.Windows.Forms.TextBox txtBins;
    }
}
