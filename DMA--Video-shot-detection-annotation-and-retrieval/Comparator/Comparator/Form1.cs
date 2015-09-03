using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Xml;

namespace Comparator
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
        }

        private void btnOwn_Click(object sender, EventArgs e)
        {
            DialogResult dialogResult = openFileDialog.ShowDialog();
            if (dialogResult == DialogResult.OK)
            {
                txtOwn.Text = openFileDialog.FileName;
            }
        }

        private void btnTruth_Click(object sender, EventArgs e)
        {

            DialogResult dialogResult = openFileDialog.ShowDialog();
            if (dialogResult == DialogResult.OK)
            {
                txtTruth.Text = openFileDialog.FileName;
            }
        }

        private void btnCalc_Click(object sender, EventArgs e)
        {
            if (txtOwn.Text == "" || txtTruth.Text == "")
            {
                return;
            }

            List<int> ownList = new List<int>();
            List<int> truthList = new List<int>();

            XmlDocument own = new XmlDocument();
            own.Load(txtOwn.Text);
            XmlNodeList ownNodes = own.SelectNodes("//shot");
            
            foreach(XmlNode node in ownNodes)
            {
                ownList.Add(Convert.ToInt32(node.Attributes["startFrame"].Value));
            }

            XmlDocument truth = new XmlDocument();
            truth.Load(txtTruth.Text);
            XmlNodeList truthNodes = truth.SelectNodes("//shot");

            foreach (XmlNode node in truthNodes)
            {
                truthList.Add(Convert.ToInt32(node.InnerText.Split('-')[0]));
            }

            calculate(ownList, truthList);
        }

        private void calculate(List<int> ownList, List<int> truthList)
        {
            int truePos = 0;
            int falsePos = 0;

            foreach (int i in ownList)
            {
                if (truthList.Remove(i))
                {
                    truePos++;
                }
                else
                {
                    falsePos++;
                }
            }

            int falseNeg = truthList.Count;
            double recall = ((double)truePos) / (truePos + falseNeg);
            double precision = ((double)truePos) / (truePos + falsePos);

            txtRecall.Text = recall.ToString();
            txtPrecision.Text = precision.ToString();
        }
    }
}
