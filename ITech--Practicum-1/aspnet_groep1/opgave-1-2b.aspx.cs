using System;
using System.Collections.Generic;
using System.Drawing;
using System.Drawing.Imaging;
using System.Linq;
using System.Web;
using System.Web.UI;
using System.Web.UI.WebControls;

public partial class opgave_1_2b : System.Web.UI.Page
{
    protected void Page_Load(object sender, EventArgs e)
    {
        
        // Haal de afbeelding op
        String image = (String)Session["filename"];

        // Maak de nieuwe bitmap
        Bitmap bitmap = new Bitmap(image);

        // Haal de actie op
        String action = (String)Session["action"];

        switch (action)
        {
            case "grayscale": // Grijswaarden

                // We converteren elk punt naar z'n grijswaarde
                for (int i = 0; i < bitmap.Width; i++)
                {
                    for (int j = 0; j < bitmap.Height; j++)
                    {
                        // Haal de pixel op
                        Color currentPixelColor = bitmap.GetPixel(i, j);

                        // Formule via http://en.wikipedia.org/wiki/Grayscale#Converting_color_to_grayscale
                        int gray = (int)(0.299 * currentPixelColor.R + 0.587 * currentPixelColor.G + 0.114 * currentPixelColor.B);

                        // Zet de pixel terug met z'n grijswaarde
                        bitmap.SetPixel(i, j, Color.FromArgb(gray, gray, gray));
                    }
                }

                break;

            case "scale": // Herschaling
                Double width = (Double)Session["width"];
                Double height = (Double)Session["height"];

                // Bereken de nieuwe hoogte & breedte
                int newHeight = (int)(height * bitmap.Height);
                int newWidth = (int)(width * bitmap.Width);

                // Maak een nieuwe bitmap met de nieuwe hoogte & breedte
                bitmap = new Bitmap(bitmap, newWidth, newHeight);
                break;

            case "rotate": // Rotatie
                String angle = (String)Session["angle"];

                // Over welke hoek willen we roteren?
                switch (angle)
                {
                    case "90":
                        bitmap.RotateFlip(RotateFlipType.Rotate90FlipNone);
                        break;
                    case "180":
                        bitmap.RotateFlip(RotateFlipType.Rotate180FlipNone);
                        break;
                    case "270":
                        bitmap.RotateFlip(RotateFlipType.Rotate270FlipNone);
                        break;
                }

                break;
        }

        // Zet tekst op de afbeelding
        Graphics graphics = Graphics.FromImage(bitmap);
        graphics.DrawString("Groep 1: Cynric Huys & Tom Naessens", new Font("Comic Sans", 15), Brushes.White, new Point(2, 2));

        // Zet het contenttype van de pagina op JPEG
        Response.ContentType = "image/JPEG";
        // Schrijf de JPEG naar de outputstream (aka de pagina)
        bitmap.Save(Response.OutputStream, ImageFormat.Jpeg);
    }
}
