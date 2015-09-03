using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Solution.Data;
using System.Xml;
using System.IO;

namespace Solution.View
{
    // Contains the data about the different methods: Name, value and the usercontrol
    public class ShotDetectionModel
    {
        public DetectionItem[] DetectionItems;
        public List<Shot> Shots;
        public List<Shot> FilteredShots;
        public ListBox lstShots;

        public DetectionItem usedMethod;

        public ShotDetectionModel(ListBox lstShots)
        {
            this.lstShots = lstShots;

            // Fill the DetectionItems array
            DetectionItems = new DetectionItem[5];
            DetectionItems[0] = new DetectionItem("PixelDifferenceSD", "PixelDifferenceSD", new PixelDifferenceSDControl(), 1);
            DetectionItems[1] = new DetectionItem("MotionEstimationSD", "MotionEstimationSD", new MotionEstimationSDControl(), 2);
            DetectionItems[2] = new DetectionItem("GlobalHistogramSD", "GlobalHistogramSD", new GlobalHistogramSDControl(), 3);
            DetectionItems[3] = new DetectionItem("LocalHistogramSD", "LocalHistogramSD", new LocalHistogramSDControl(), 4);
            DetectionItems[4] = new DetectionItem("GeneralizedSD", "GeneralizedSD", new GeneralizedSDControl(), 5);
        }

        public void AnnotateShot(Shot shot, String annotations)
        {
            shot.Annotations = annotations.Split(',').Select(p => p.Trim()).ToList<String>();
            lstShots.DataSource = null;
            lstShots.DataSource = Shots;
        }

        public void ExportShots(String path)
        {
            foreach (Shot shot in Shots)
            {
                String filename = path + "\\Frame" + shot.StartFrame + ".png";
                shot.Bitmap.Save(filename, System.Drawing.Imaging.ImageFormat.Png);
            }
        }

        public void ExportInfo(String filename, String filepath)
        {
            try
            {
                XmlDocument xmlDocument = new XmlDocument();

                // Create the root
                XmlElement root = xmlDocument.CreateElement("ShotDetection");
                root.SetAttribute("file", Path.GetFileName(filename));
                xmlDocument.AppendChild(root);

                // Add the parameters
                XmlElement method = xmlDocument.CreateElement("method");
                method.SetAttribute("nr", usedMethod.MethodNumber.ToString());

                int i = 1;
                foreach(String value in usedMethod.SDUserControl.GetParameters())
                {
                    XmlElement param = xmlDocument.CreateElement("param" + i);
                    param.InnerText = value;
                    method.AppendChild(param);
                    i++;
                }
                root.AppendChild(method);

                // Add the shots
                XmlElement shots = xmlDocument.CreateElement("shots");
                method.SetAttribute("nr", usedMethod.MethodNumber.ToString());

                foreach (Shot shot in Shots)
                {
                    XmlElement shotElement = xmlDocument.CreateElement("shot");
                    shotElement.SetAttribute("startFrame", shot.StartFrame.ToString());
                    shotElement.SetAttribute("endFrame", shot.EndFrame.ToString());

                    foreach (String annotation in shot.Annotations)
                    {
                        XmlElement annotationElement = xmlDocument.CreateElement("annotation");
                        annotationElement.InnerText = annotation;

                        shotElement.AppendChild(annotationElement);
                    }

                    shots.AppendChild(shotElement);
                }
                root.AppendChild(shots);

                xmlDocument.Save(filepath);
            }
            catch (XmlException)
            {
                MessageBox.Show("An error occured when exporting the shotinfo.");
            }
        }

        public void FilterList(String text)
        {
            FilteredShots = new List<Shot>();

            if (text == "")
            {
                FilteredShots = Shots;
            }
            else
            {
                foreach(Shot shot in Shots)
                {
                    foreach (String annotation in shot.Annotations)
                    {
                        if(annotation.Contains(text))
                        {
                            FilteredShots.Add(shot);
                            break;
                        }
                    }
                }
            }
            lstShots.DataSource = null;
            lstShots.DataSource = FilteredShots;
        }
    }
}
