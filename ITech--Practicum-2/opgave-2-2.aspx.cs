using System;
using System.Collections.Generic;
using System.Linq;
using System.Web;
using System.Web.UI;
using System.Web.UI.WebControls;
using System.Xml;
using System.Xml.XPath;
using be.ugent.elis.multimedialab;

public partial class opgave_2_2 : System.Web.UI.Page
{

    XmlDocument xmlDocument;
    XmlNamespaceManager xmlNamespaceManager;
    XmlNodeList xmlTrailerList;

    protected void Page_Load(object sender, EventArgs e)
    {
        // Hide het trailerpaneel
        pnlTrailer.Visible = false;

        // Build a document
        xmlDocument = new XmlDocument();
        xmlDocument.Load(Request.MapPath("opgave-2-1.xml"));

        // Let's use a NamespaceManager: we don't want to type urn:mpeg:mpeg21:2002:02-DIDL-NS every time.
        xmlNamespaceManager = new XmlNamespaceManager(xmlDocument.NameTable);
        xmlNamespaceManager.AddNamespace("urn", "urn:mpeg:mpeg21:2002:02-DIDL-NS");

        // Get the description
        Get_Description();

        // Get the amount of trailers
        Get_Trailer_Amount();

        // Refresh the trailers
        Refresh_Trailers();
    }

    private void Get_Description()
    {
        //Haal de description op: dit zit in het eerste statement van de eerste descriptor van het eerste item van de DIDL
        XmlNode xmlDescriptionNode = xmlDocument.SelectSingleNode("/urn:DIDL/urn:Item/urn:Descriptor/urn:Statement", xmlNamespaceManager);
        lblCollectionDescription.Text = xmlDescriptionNode.InnerText;
    }

    private void Get_Trailer_Amount()
    {
        /**
         * Haal de lijst van alle 'Items' die binnen een andere 'Item' tag zitten. 
         * Zo selecteren we snel een lijst van alle nodes.
         */
        xmlTrailerList = xmlDocument.SelectNodes("//urn:Item/urn:Item", xmlNamespaceManager);

        // Met count halen we nu het aantal elementen in de lijst op
        lblAmountOfTrailers.Text = xmlTrailerList.Count.ToString();
    }

    private void Refresh_Trailers()
    {
        Random random = new Random();
        int max = xmlTrailerList.Count;
        int index1, index2, index3;

        // Genereer random indexes
        index1 = random.Next(max);
        index2 = random.Next(max);
        index3 = random.Next(max);

        // Zorg ervoor dat index1 verschillend is van index2
        while (index1 == index2)
        {
            index2 = random.Next(max);
        }

        // Idem voor index3; verschillende van index1 en index2
        while (index1 == index3 || index2 == index3)
        {
            index3 = random.Next(max);
        }

        // Zet de bijhorende images
        Set_Image(index1, imgbtnCover1);
        Set_Image(index2, imgbtnCover2);
        Set_Image(index3, imgbtnCover3);

        // Zet de waarden in de hidden velden zodat we deze kunnen opvragen als de pagina herladen wordt via het Request.Form object
        hdnCover1.Value = index1.ToString();
        hdnCover2.Value = index2.ToString();
        hdnCover3.Value = index3.ToString();
    }

    private void Set_Image(int index, ImageButton imgbtn)
    {
        // Haal het juiste element uit de Nodelist
        XmlNode element = xmlTrailerList.Item(index);

        // Haal de juiste node uit het element
        XmlNode imgNode = element.SelectSingleNode("./urn:Descriptor/urn:Component/urn:Resource", xmlNamespaceManager);

        // Haal het ref attribuut uit de node en ken deze toe aan de imagebutton
        imgbtn.ImageUrl = imgNode.Attributes["ref"].Value;
    }


    private void Show_Trailer(int i)
    {
        // Switch the visibility of the panels
        pnlCoverAlbums.Visible = false;
        pnlTrailer.Visible = true;

        // Get the correct node containing the URL
        XmlNode xmlUrlNode = xmlTrailerList.Item(i).SelectSingleNode("./urn:Component/urn:Resource", xmlNamespaceManager);

        // Get the ref value of the node and pass it to the URIResolver
        URIResolver uriResolver = new URIResolver();
        String url = uriResolver.ResolveURI(xmlUrlNode.Attributes["ref"].Value);

        // Code from tips section of the assessment
        itech1.InnerHtml = "" +
            "<OBJECT ID='itech1' width='480' " +
            "height='336' CLASSID='CLSID:6BF52A52-394A-11D3-B153-00C04F79FAA6' " +
            "standby='Loading Microsoft Windows Media Player components...' " +
            "TYPE='application/x-oleobject' width='200' height='200' VIEWASTEXT>" +
            "<PARAM NAME='url' VALUE='" + url + "'>" +
            "<PARAM NAME='AutoStart' VALUE='true'>" +
            "<PARAM NAME='uiMode' VALUE='mini'>" +
            "</OBJECT>";
    }

    protected void btnBackToSelection_Click(object sender, EventArgs e)
    {
        // Switch the visibility of the panels
        pnlTrailer.Visible = false;
        pnlCoverAlbums.Visible = true;
    }


    protected void btnNewTrailers_Click(object sender, EventArgs e)
    {
        Refresh_Trailers();
    }

    protected void imgbtnCover1_Click(object sender, ImageClickEventArgs e)
    {
        Show_Trailer(Convert.ToInt32(Request.Form.Get("hdnCover1")));
    }

    protected void imgbtnCover2_Click(object sender, ImageClickEventArgs e)
    {
        Show_Trailer(Convert.ToInt32(Request.Form.Get("hdnCover2")));
    }

    protected void imgbtnCover3_Click(object sender, ImageClickEventArgs e)
    {
        Show_Trailer(Convert.ToInt32(Request.Form.Get("hdnCover3")));
    }

}
