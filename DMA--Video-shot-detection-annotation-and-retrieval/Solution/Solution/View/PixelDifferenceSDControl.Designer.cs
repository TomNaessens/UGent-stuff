namespace Solution.View
{
    partial class PixelDifferenceSDControl
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
            this.lblPixelDifferenceSD = new System.Windows.Forms.Label();
            this.label1 = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.txtTreshold2 = new System.Windows.Forms.TextBox();
            this.txtTreshold3 = new System.Windows.Forms.TextBox();
            this.label3 = new System.Windows.Forms.Label();
            this.label4 = new System.Windows.Forms.Label();
            this.SuspendLayout();
            // 
            // lblPixelDifferenceSD
            // 
            this.lblPixelDifferenceSD.AutoSize = true;
            this.lblPixelDifferenceSD.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.lblPixelDifferenceSD.Location = new System.Drawing.Point(4, 4);
            this.lblPixelDifferenceSD.Name = "lblPixelDifferenceSD";
            this.lblPixelDifferenceSD.Size = new System.Drawing.Size(140, 13);
            this.lblPixelDifferenceSD.TabIndex = 0;
            this.lblPixelDifferenceSD.Text = "Pixel difference method";
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.Location = new System.Drawing.Point(4, 33);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(60, 13);
            this.label1.TabIndex = 1;
            this.label1.Text = "Treshold 2:";
            // 
            // label2
            // 
            this.label2.AutoSize = true;
            this.label2.Location = new System.Drawing.Point(4, 59);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(60, 13);
            this.label2.TabIndex = 2;
            this.label2.Text = "Treshold 3:";
            // 
            // txtTreshold2
            // 
            this.txtTreshold2.Location = new System.Drawing.Point(78, 30);
            this.txtTreshold2.Name = "txtTreshold2";
            this.txtTreshold2.Size = new System.Drawing.Size(91, 20);
            this.txtTreshold2.TabIndex = 3;
            // 
            // txtTreshold3
            // 
            this.txtTreshold3.Location = new System.Drawing.Point(78, 56);
            this.txtTreshold3.Name = "txtTreshold3";
            this.txtTreshold3.Size = new System.Drawing.Size(91, 20);
            this.txtTreshold3.TabIndex = 4;
            // 
            // label3
            // 
            this.label3.AutoSize = true;
            this.label3.Location = new System.Drawing.Point(175, 33);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(24, 13);
            this.label3.TabIndex = 5;
            this.label3.Text = "(int)";
            // 
            // label4
            // 
            this.label4.AutoSize = true;
            this.label4.Location = new System.Drawing.Point(175, 59);
            this.label4.Name = "label4";
            this.label4.Size = new System.Drawing.Size(45, 13);
            this.label4.TabIndex = 6;
            this.label4.Text = "(double)";
            // 
            // PixelDifferenceSDControl
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.Controls.Add(this.label4);
            this.Controls.Add(this.label3);
            this.Controls.Add(this.txtTreshold3);
            this.Controls.Add(this.txtTreshold2);
            this.Controls.Add(this.label2);
            this.Controls.Add(this.label1);
            this.Controls.Add(this.lblPixelDifferenceSD);
            this.Name = "PixelDifferenceSDControl";
            this.Size = new System.Drawing.Size(225, 125);
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Label lblPixelDifferenceSD;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.TextBox txtTreshold2;
        private System.Windows.Forms.TextBox txtTreshold3;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Label label4;
    }
}
