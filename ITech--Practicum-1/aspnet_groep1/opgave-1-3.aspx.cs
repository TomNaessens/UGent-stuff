using System;
using System.Collections.Generic;
using System.Linq;
using System.Web;
using System.Web.UI;
using System.Web.UI.WebControls;
using System.Data;
using System.Data.SqlClient;

public partial class _Default : System.Web.UI.Page
{
    string connectionString = "Server=VSTUDENT.ELIS.UGENT.BE;Integrated Security=false;Database=itech1;user id=itech1;password=Jit@Reawt4";
    
    protected void Page_Load(object sender, EventArgs e)
    {
        // Hide all errors
        lblEmptyError.Visible = false;
        lblConnError.Visible = false;
        lblInsertError.Visible = false;

        // Zet de kleuren voor de errormeldingen
        pnlError.BackColor = System.Drawing.Color.Red;
        pnlError.ForeColor = System.Drawing.Color.White;

        try
        {
            SqlConnection cnn = new SqlConnection(connectionString);
            SqlDataAdapter cmd = new SqlDataAdapter("SELECT * FROM [MuziekCataloog]", cnn);
            DataSet ds = new DataSet();

            cmd.Fill(ds);
            GridView1.DataBind();
        }
        catch (SqlException ex)
        {
            lblConnError.Visible = true;
            pnlResult.Visible = false;
            pnlAdd.Visible = false;
            lblConnError.Text = "<h2>Fout opgetreden bij het verbinden met de database:</h2>" + ex;
        }
    }

    protected void btnInsert_Click(object sender, EventArgs e)
    {
        // Voeg een record toe in de database:
        Insert_Artist(
            System.Convert.ToInt32(txtTracknummer.Text),
            txtTitel.Text,
            txtUitvoerder.Text,
            txtAlbum.Text,
            System.Convert.ToInt32(txtJaar.Text)
            );
    }

    protected void Insert_Artist(int TrackNr, String Titel, String Uitvoerder, String Album, int Jaar)
    {
        // Aanmaken connectie
        SqlConnection sqlConn = new SqlConnection(connectionString);

        // Selectstring
        string selectSqlString = String.Format("SELECT * FROM MuziekCataloog WHERE TrackNr = '{0}' AND "
                                                                                 + "Titel = '{1}' AND "
                                                                                 + "Uitvoerder = '{2}' AND "
                                                                                 + "Album = '{3}' AND "
                                                                                 + "Jaar = '{4}'",
                                                                           TrackNr, Titel, Uitvoerder, Album, Jaar);

        // Maak een command van de selectstring
        SqlCommand selectCmd = new SqlCommand(selectSqlString, sqlConn);

        try
        {
            sqlConn.Open(); // Open connectie.
            Object result = selectCmd.ExecuteScalar(); // Voer de selectquery uit
            sqlConn.Close();
            if (result != null) // Krijgen we een resultaat? Dan bestaat het record al: toon een foutmelding
            {
                throw new Exception("Ingevoegd record bestaat al.");
            }

            // Als we hier raken bestaat het record nog niet: voeg alle insertparamters toe:
            MuziekCataloog.InsertParameters.Add("Tracknr", TrackNr + "");
            MuziekCataloog.InsertParameters.Add("Titel", Titel);
            MuziekCataloog.InsertParameters.Add("Uitvoerder", Uitvoerder);
            MuziekCataloog.InsertParameters.Add("Album", Album);
            MuziekCataloog.InsertParameters.Add("Jaar", Jaar + "");
            MuziekCataloog.Insert(); // Insert de parameters in de datasource - de datasource zal hier zelf ook de SQL updaten

            // Error mag weg
            lblInsertError.Text = "";

            // Leeg alle velden in het invulformulier
            txtTracknummer.Text = "";
            txtTitel.Text = "";
            txtUitvoerder.Text = "";
            txtAlbum.Text = "";
            txtJaar.Text = "";
        }
        catch (SqlException e)
        {
            lblInsertError.Visible = true;
            lblInsertError.Text = "Kon nieuw record niet invullen: SQL databank niet beschikbaar.<br />Error:" + e;
        }
        catch (Exception e)
        {
            lblInsertError.Visible = true;
            lblInsertError.Text = e.Message;
        }

    }

    protected void GridView_RowUpdated(object sender, GridViewUpdatedEventArgs e)
    {
        if (e.Exception != null)
        {
            lblConnError.Text = "Fout opgetreden bij het verbinden met de database:<br />" + e;
            e.ExceptionHandled = true;
        }
    }

    protected void GridView_Init(object sender, EventArgs e)
    {
        /**
         * Lege methode: in de 'normale' init functie van GridView probeert deze al een verbinding met de
         * databank op te stellen. Daarbij kunnen we geen error opvangen. Dus we overschrijven deze 
         * implementatie met 'niets'.
         * In de Page_Load voegen we echter zelf onze DataSource toe aan de gridview, zodat we bij een 
         * error wel de verbindingsfout kunnen opvangen.
         */
    }
}