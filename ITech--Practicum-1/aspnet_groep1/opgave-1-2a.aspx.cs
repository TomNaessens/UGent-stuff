using System;
using System.Collections.Generic;
using System.Linq;
using System.Web;
using System.Web.UI;
using System.Web.UI.WebControls;

public partial class opgave_1_2a : System.Web.UI.Page 
{
    protected void Page_Load(object sender, EventArgs e)
    {

    }
    protected void btnScale_Click(object sender, EventArgs e)
    {
        // Toon het juiste paneel
        divScale.Visible = true;
        divRotate.Visible = false;
    }
    protected void btnRotation_Click(object sender, EventArgs e)
    {
        // Toon het juiste paneel
        divRotate.Visible = true;
        divScale.Visible = false;
    }
    protected void btnGrayscale_Click(object sender, EventArgs e)
    {
        setPath();
        Session["action"] = "grayscale";
        Response.Redirect("opgave-1-2b.aspx");
    }
    protected void btnDoScale_Click(object sender, EventArgs e)
    {
        setPath();
        Session["action"] = "scale";
        Session["width"] = Convert.ToDouble(txtBreedte.Text);
        Session["height"] = Convert.ToDouble(txtHoogte.Text);
        Response.Redirect("opgave-1-2b.aspx");
    }
    protected void btnDoRotate_Click(object sender, EventArgs e)
    {
        setPath();
        Session["action"] = "rotate";
        Session["angle"] = RotationAngle.SelectedValue;
        Response.Redirect("opgave-1-2b.aspx");
    }

    protected void setPath()
    {
        // Steek de filename in de sessie
        Session["filename"] = Server.MapPath(txtFile.Text);
    }
}
