using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Drawing;
using System.Data;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Solution.Data;

namespace Solution.View
{
    public abstract partial class SDUserControl : UserControl
    {
        public SDUserControl() : base()
        {
            InitializeComponent();
        }

        public abstract List<Shot> DoDetect(String fileName);
        public abstract List<String> GetParameters();
    }
}
