using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows.Forms;

namespace Solution.View
{
    public class DetectionItem
    {
        public string Text { get; set; }
        public object Value { get; set; }
        public int MethodNumber { get; set; }
        public SDUserControl SDUserControl;

        public DetectionItem(String Text, String Value, SDUserControl SDUserControl, int MethodNumber)
        {
            this.Text = Text;
            this.Value = Value;
            this.SDUserControl = SDUserControl;
            this.MethodNumber = MethodNumber;
        }

        public override string ToString()
        {
            return Text;
        }
    }
}
