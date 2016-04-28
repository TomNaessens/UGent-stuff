using System;
using System.Collections.Generic;
using System.Linq;
using System.Web;
using System.Web.UI;
using System.Web.UI.WebControls;
using System.Net;
using System.Xml;
using System.Globalization;

public partial class _Default : System.Web.UI.Page
{
    protected void Page_Load(object sender, EventArgs e)
    {
        //First load: load all the records
        Get_All_Results();
    }

    protected void btnZoek_OnClick(object sender, EventArgs e)
    {
        Get_Results(
            Build_Query(
                creator.Text,
                subject.Text,
                type.SelectedValue,
                coverage.Text,
                date.Text,
                description.Text,
                title.Text
            )
        );
    }

    protected void btnShowAll_OnClick(object sender, EventArgs e)
    {
        Get_All_Results();
    }

    protected void Get_All_Results()
    {
        Get_Results(Build_Query("", "", "", "", "", "", ""));
    }

    protected String Build_Query(
        String creator, String subject, String type, String coverage, String date, String description, String title)
    {
        String query = "";

        // Add prefixes to the query
        query += "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>";
        query += "PREFIX dc: <http://purl.org/dc/elements/1.1/>";
        query += "PREFIX foaf: <http://xmlns.com/foaf/0.1/>";
        query += "PREFIX dbcategory: <http://dbpedia.org/resource/Category:>";

        // Begin the select query
        query += "SELECT * ";

        // Add WHERE constraints
        query += "WHERE { ?s ?p ?o . ";
        // We only want to select images
        query += "?s rdf:type foaf:Image . ";
        // We only want dc elements
        query += "FILTER regex(str(?p), \"http://purl.org/dc/elements/1.1/\") .";

        // Add the user requests
        if (creator.Length != 0)
            // We use a regex here so the user doesn't have to enter the whole name of the creator
            query += " ?s dc:creator ?creator FILTER regex(str(?creator), \"" + creator + "\", \"i\") .";
        if (subject.Length != 0)
            query += " ?s dc:subject ?subject FILTER regex(str(?subject), \"" + subject + "\", \"i\") .";
        if (type.Length != 0)
            query += " ?s dc:type dbcategory:" + type + " .";
        if (coverage.Length != 0)
            query += " ?s dc:coverage ?coverage FILTER regex(str(?coverage), \"" + coverage + "\", \"i\") .";
        if (date.Length != 0)
            query += " ?s dc:date ?date FILTER regex(str(?date), \"" + date + "\", \"i\") .";
        if (description.Length != 0)
            query += " ?s dc:description ?description FILTER regex(str(?description), \"" + description + "\", \"i\") .";
        if (title.Length != 0)
            query += " ?s dc:title ?title FILTER regex(str(?title), \"" + title + "\", \"i\") .";

        // Close the WHERE clause
        query += "}";

        return query;
    }

    protected void Get_Results(String query)
    {
        // Create a new webclient
        WebClient webClient = new WebClient();

        // Build the URL: we encode the URL here to correctly replace " " with "%20" etc.
        String url = "http://localhost:11001/sparql/query?format=xml&query=" + Server.UrlEncode(query);
        
        // Retrieve the result into a String using DownloadString
        String queryResult = "";
        try
        {
            queryResult = webClient.DownloadString(url);
        }
        catch (WebException e)
        {
            // What happens if the Sparqserver isn't available?!
            divResults.InnerHtml += @"
                <div class='alert'>
                    <button type='button' class='close' data-dismiss='alert'>&times;</button>
                    <strong>Woops!</strong> Kon geen verbinding maken met de SparQL server!
                </div>";
            return;
        }

        // Create a new XmlDocument
        XmlDocument xmlDocument = new XmlDocument();
        // Load the obtained XML in the XmlDocument
        xmlDocument.LoadXml(queryResult);

        // Add the sparql-result namespace
        XmlNamespaceManager xmlNameSpaceManager = new XmlNamespaceManager(xmlDocument.NameTable);
        xmlNameSpaceManager.AddNamespace("s", "http://www.w3.org/2005/sparql-results#");
        
        // Get all the results from the xmlDocument
        XmlNodeList xmlNodeList = xmlDocument.SelectNodes("/s:sparql/s:results/s:result", xmlNameSpaceManager);

        // Create a dictionary that maps the S's to the P's & O's.
        Dictionary<String, List<PandO>> sToPandO = new Dictionary<string,List<PandO>>();

        // Iterate over all results
        foreach (XmlNode xmlNode in xmlNodeList)
        {

            /** 
             * Get the innertext of each of the bindings: the name of its child node varies, so 
             * we can use child::node() to get this node. <3 XPath
             **/
            String s = xmlNode.SelectSingleNode("s:binding[@name='s']/child::node()", xmlNameSpaceManager).InnerText;
            String p = xmlNode.SelectSingleNode("s:binding[@name='p']/child::node()", xmlNameSpaceManager).InnerText;
            String o = xmlNode.SelectSingleNode("s:binding[@name='o']/child::node()", xmlNameSpaceManager).InnerText;

            /**
             * We now test if the dictionary already contains a list for the given s.
             * If not, we create a new list
             **/
            List<PandO> pandO;
            if (!sToPandO.TryGetValue(s, out pandO))
            {
                pandO = new List<PandO>();
            }

            // We add a new PandO object to the list
            pandO.Add(new PandO(p, o));
            // And readd the list to the dictionary for the given key on position s.
            sToPandO[s] = pandO;
        }

        // Last but not least, create the fancy gallery:
        Create_Fancy_Gallery(sToPandO);
            
    }
    
    public void Create_Fancy_Gallery(Dictionary<String, List<PandO>> sToPandO)
    {
        // Clear the resulting div
        divResults.InnerHtml = "";

        // Show an error if the map is empty!
        if (sToPandO.Keys.Count == 0)
        {
            divResults.InnerHtml += @"
                <div class='alert'>
                    <button type='button' class='close' data-dismiss='alert'>&times;</button>
                    <strong>Woops!</strong> Geen resultaten gevonden!
                </div>";
            return;
        }

        // Add all the found results nicely.
        foreach (string key in sToPandO.Keys)
        {
            // Open the container
            divResults.InnerHtml += @"
            <div class='well'>
                <div class='container-fluid'>
                  <div class='row-fluid'>
                    <div class='span7'>
                        <a href='" + key + "'><img src='" + key + @"'/></a>
                    </div>
                    <div class='span5'>
                        <table class='table table-striped'>";

            // Add the properties
            foreach (PandO pandO in sToPandO[key])
            {
                divResults.InnerHtml +=
                           @"<tr>
                                  <th>" + pandO.getP() + @"</th>
                                  <td>" + pandO.getO() + @"</td>
                              </tr>";
            }
                            
            // Close the table
            divResults.InnerHtml += @"
                        </table>
                    </div>
                  </div>
                </div>
            </div>
            ";
        }

    }

    /**
     * Represents a tuple of P and O
     **/
    public class PandO
    {
        private String p;
        private String o;

        public PandO(String p, String o)
        {
            this.p = p;
            this.o = o;
        }

        public String getP() 
        {
            /**
             * We only want the last part of the URL, so we substring that part out. 
             * We also like the first letter of the word in caps, so we TitleCase it.
             * Sauce: http://stackoverflow.com/a/4135491/1068495
             **/
            return CultureInfo.CurrentCulture.TextInfo.ToTitleCase(p.Substring(p.LastIndexOf('/') + 1));
        }


        public String getO()
        {
            // Let's displays URL's the way they should be: In an <a>!
            if (Uri.IsWellFormedUriString(o, UriKind.Absolute))
            {
                return "<a href=" + o + " target='_blank'>" + o + "</a>";
            }
            return o;
        }
    }

}
