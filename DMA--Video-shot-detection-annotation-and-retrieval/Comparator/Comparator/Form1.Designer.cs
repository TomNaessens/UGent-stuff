namespace Comparator
{
    partial class Form1
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
            this.lblRecall = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.label3 = new System.Windows.Forms.Label();
            this.label4 = new System.Windows.Forms.Label();
            this.openFileDialog = new System.Windows.Forms.OpenFileDialog();
            this.txtOwn = new System.Windows.Forms.TextBox();
            this.txtTruth = new System.Windows.Forms.TextBox();
            this.btnOwn = new System.Windows.Forms.Button();
            this.btnTruth = new System.Windows.Forms.Button();
            this.txtRecall = new System.Windows.Forms.TextBox();
            this.txtPrecision = new System.Windows.Forms.TextBox();
            this.btnCalc = new System.Windows.Forms.Button();
            this.SuspendLayout();
            // 
            // lblRecall
            // 
            this.lblRecall.AutoSize = true;
            this.lblRecall.Location = new System.Drawing.Point(13, 89);
            this.lblRecall.Name = "lblRecall";
            this.lblRecall.Size = new System.Drawing.Size(40, 13);
            this.lblRecall.TabIndex = 0;
            this.lblRecall.Text = "Recall:";
            // 
            // label2
            // 
            this.label2.AutoSize = true;
            this.label2.Location = new System.Drawing.Point(203, 89);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(53, 13);
            this.label2.TabIndex = 1;
            this.label2.Text = "Precision:";
            // 
            // label3
            // 
            this.label3.AutoSize = true;
            this.label3.Location = new System.Drawing.Point(16, 15);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(32, 13);
            this.label3.TabIndex = 2;
            this.label3.Text = "Own:";
            // 
            // label4
            // 
            this.label4.AutoSize = true;
            this.label4.Location = new System.Drawing.Point(13, 41);
            this.label4.Name = "label4";
            this.label4.Size = new System.Drawing.Size(35, 13);
            this.label4.TabIndex = 3;
            this.label4.Text = "Truth:";
            // 
            // openFileDialog
            // 
            this.openFileDialog.FileName = "openFileDialog";
            // 
            // txtOwn
            // 
            this.txtOwn.Location = new System.Drawing.Point(54, 12);
            this.txtOwn.Name = "txtOwn";
            this.txtOwn.Size = new System.Drawing.Size(439, 20);
            this.txtOwn.TabIndex = 4;
            // 
            // txtTruth
            // 
            this.txtTruth.Location = new System.Drawing.Point(54, 38);
            this.txtTruth.Name = "txtTruth";
            this.txtTruth.Size = new System.Drawing.Size(439, 20);
            this.txtTruth.TabIndex = 5;
            // 
            // btnOwn
            // 
            this.btnOwn.Location = new System.Drawing.Point(499, 10);
            this.btnOwn.Name = "btnOwn";
            this.btnOwn.Size = new System.Drawing.Size(75, 23);
            this.btnOwn.TabIndex = 6;
            this.btnOwn.Text = "Choose";
            this.btnOwn.UseVisualStyleBackColor = true;
            this.btnOwn.Click += new System.EventHandler(this.btnOwn_Click);
            // 
            // btnTruth
            // 
            this.btnTruth.Location = new System.Drawing.Point(499, 36);
            this.btnTruth.Name = "btnTruth";
            this.btnTruth.Size = new System.Drawing.Size(75, 23);
            this.btnTruth.TabIndex = 7;
            this.btnTruth.Text = "Choose";
            this.btnTruth.UseVisualStyleBackColor = true;
            this.btnTruth.Click += new System.EventHandler(this.btnTruth_Click);
            // 
            // txtRecall
            // 
            this.txtRecall.Location = new System.Drawing.Point(54, 86);
            this.txtRecall.Name = "txtRecall";
            this.txtRecall.ReadOnly = true;
            this.txtRecall.Size = new System.Drawing.Size(100, 20);
            this.txtRecall.TabIndex = 8;
            // 
            // txtPrecision
            // 
            this.txtPrecision.Location = new System.Drawing.Point(262, 86);
            this.txtPrecision.Name = "txtPrecision";
            this.txtPrecision.ReadOnly = true;
            this.txtPrecision.Size = new System.Drawing.Size(100, 20);
            this.txtPrecision.TabIndex = 9;
            // 
            // btnCalc
            // 
            this.btnCalc.Location = new System.Drawing.Point(499, 65);
            this.btnCalc.Name = "btnCalc";
            this.btnCalc.Size = new System.Drawing.Size(75, 23);
            this.btnCalc.TabIndex = 10;
            this.btnCalc.Text = "Calculate!";
            this.btnCalc.UseVisualStyleBackColor = true;
            this.btnCalc.Click += new System.EventHandler(this.btnCalc_Click);
            // 
            // Form1
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.ClientSize = new System.Drawing.Size(590, 114);
            this.Controls.Add(this.btnCalc);
            this.Controls.Add(this.txtPrecision);
            this.Controls.Add(this.txtRecall);
            this.Controls.Add(this.btnTruth);
            this.Controls.Add(this.btnOwn);
            this.Controls.Add(this.txtTruth);
            this.Controls.Add(this.txtOwn);
            this.Controls.Add(this.label4);
            this.Controls.Add(this.label3);
            this.Controls.Add(this.label2);
            this.Controls.Add(this.lblRecall);
            this.Name = "Form1";
            this.Text = "SuperDuperComparator";
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Label lblRecall;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Label label4;
        private System.Windows.Forms.OpenFileDialog openFileDialog;
        private System.Windows.Forms.TextBox txtOwn;
        private System.Windows.Forms.TextBox txtTruth;
        private System.Windows.Forms.Button btnOwn;
        private System.Windows.Forms.Button btnTruth;
        private System.Windows.Forms.TextBox txtRecall;
        private System.Windows.Forms.TextBox txtPrecision;
        private System.Windows.Forms.Button btnCalc;
    }
}

