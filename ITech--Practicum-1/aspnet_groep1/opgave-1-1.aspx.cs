using System;
using System.Collections.Generic;
using System.Linq;
using System.Web;
using System.Web.UI;
using System.Web.UI.WebControls;

public partial class _Default : System.Web.UI.Page 
{
    protected void Page_Load(object sender, EventArgs e)
    {
        // We zetten de visibility op false; 
        tblResultTable.Visible = false;
    }

    protected void btnMaakTabel_Click(object sender, EventArgs e)
    {
        // We zetten de visibility op true; 
        tblResultTable.Visible = true;

        // Roepen de functie aan met de geparste elementen
        try
        {
            maakTabel(
                Convert.ToInt32(txtAantalRijen.Text),
                Convert.ToInt32(txtAantalKolommen.Text),
                slctEvenAchtergrond.SelectedValue,
                slctOnevenAchtergrond.SelectedValue,
                Convert.ToInt32(txtDikteRand.Text),
                Convert.ToInt32(txtBreedteTabel.Text));
        }
        catch (FormatException parseE)
        {
            
        }
    }

    private void maakTabel(int aantalRijen, int aantalKolommen, 
        string achtergrondkleurEvenKolommen, string achtergrondkleurOnevenKolommen, 
        int dikteRand, int breedteTabel)
    {
        for (int rij = 1; rij <= aantalRijen; rij++)
        {
            TableRow tableRow = new TableRow();

            for (int kolom = 1; kolom <= aantalKolommen; kolom++)
            {
                TableCell tableCell = new TableCell();

                // Zet het achtergrondkleur goed
                String color = achtergrondkleurOnevenKolommen;
                if (kolom % 2 == 0)
                {
                    color = achtergrondkleurEvenKolommen;
                }

                // BackColor moet een kleur zijn, dus we converteren de string naar een kleur
                tableCell.BackColor = System.Drawing.Color.FromName(color);

                // Hint uit de opgave: lege cellen moeten zichtbaar zijn
                tableCell.Text = "&nbsp;";

                // Voeg de nieuwe cell toe aan de row
                tableRow.Cells.Add(tableCell);

            }
            // Voeg de nieuwe row toe aan de tabel
            tblResultTable.Rows.Add(tableRow);
        }

        tblResultTable.Width = Unit.Percentage(breedteTabel);
        tblResultTable.BorderWidth = Unit.Pixel(dikteRand);

    }
}
