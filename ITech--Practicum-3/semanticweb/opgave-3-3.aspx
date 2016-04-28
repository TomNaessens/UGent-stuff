<%@ Page Language="C#" AutoEventWireup="true" CodeFile="opgave-3-3.aspx.cs" Inherits="_Default" %>

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head runat="server">
    <title></title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link href="css/bootstrap.min.css" rel="stylesheet" media="screen">
    
    <style>
        body 
        {
            margin: 20px;
        }
        
        img 
        {
            border: 1px solid black;
        }
    </style>
</head>
<body>
    <form class="form-horizontal" id="searchForm" runat="server">
    
    <!-- Search & show all buttons -->
    <div class="btn-group">
        <a href="#zoekModal" role="button" class="btn btn-primary" data-toggle="modal">Zoek</a>
        <asp:Button type="submit" id="btnShowAll" class="btn" runat="server" onclick="btnShowAll_OnClick" Text="Geef alles weer"></asp:Button>
    </div>
    
    <!-- Nice modal that pops up when we click the search button -->
    <div id="zoekModal" class="modal hide fade" tabindex="-1" role="dialog" aria-labelledby="myModalLabel"
        aria-hidden="true">
        <div class="modal-header">
            <a class="close" data-dismiss="modal" aria-hidden="true">
                ×</a>
            <h3 id="myModalLabel">
                Zoek</h3>
        </div>
        <div class="modal-body">
            <div class="control-group">
                <label class="control-label" for="creator">
                    Maker</label>
                <div class="controls">
                    <asp:TextBox ID="creator" runat="server"></asp:TextBox>
                </div>
            </div>
            <div class="control-group">
                <label class="control-label" for="creator">
                    Onderwerp</label>
                <div class="controls">
                    <asp:TextBox ID="subject" runat="server"></asp:TextBox>
                </div>
            </div>
            <div class="control-group">
                <label class="control-label" for="type">
                    Thema</label>
                <div class="controls">
                    <asp:DropDownList ID="type" runat="server">
                        <asp:ListItem Value=""></asp:ListItem>
                        <asp:ListItem Value="People">Mensen</asp:ListItem>
                        <asp:ListItem Value="Animals">Dieren</asp:ListItem>
                        <asp:ListItem Value="Architecture">Architectuur</asp:ListItem>
                        <asp:ListItem Value="Nature">Natuur</asp:ListItem>
                        <asp:ListItem Value="Politics">Politiek</asp:ListItem>
                        <asp:ListItem Value="Humor">Humor</asp:ListItem>
                        <asp:ListItem Value="Culture">Cultuur</asp:ListItem>
                        <asp:ListItem Value="News">Nieuws</asp:ListItem>
                    </asp:DropDownList>
                </div>
            </div>
            <div class="control-group">
                <label class="control-label" for="coverage">
                    Plaats</label>
                <div class="controls">
                    <asp:TextBox ID="coverage" runat="server"></asp:TextBox>
                </div>
            </div>
            <div class="control-group">
                <label class="control-label" for="date">
                    Datum</label>
                <div class="controls">
                    <asp:TextBox ID="date" runat="server"></asp:TextBox>
                </div>
            </div>
            <div class="control-group">
                <label class="control-label" for="description">
                    Omschrijving</label>
                <div class="controls">
                    <asp:TextBox ID="description" runat="server"></asp:TextBox>
                </div>
            </div>
            <div class="control-group">
                <label class="control-label" for="title">
                    Titel</label>
                <div class="controls">
                    <asp:TextBox ID="title" runat="server"></asp:TextBox>
                </div>
            </div>
        </div>
        <div class="modal-footer">
            <div class="btn-group">
                <input type="reset" class="btn">Wis alles</input>
                <asp:Button type="submit" id="btnZoek" class="btn btn-primary" runat="server" onclick="btnZoek_OnClick" Text="Zoek!"></asp:Button>
            </div>
        </div>
    </div>
    
    <!-- Results here! -->
    <h2>Resultaten</h2>
    <div id="divResults" runat="server"></div>
     
    <!-- Search & show all buttons -->
    <div class="btn-group">
        <a href="#zoekModal" role="button" class="btn btn-primary" data-toggle="modal">Zoek</a>
        <asp:Button type="submit" id="Button1" class="btn" runat="server" onclick="btnShowAll_OnClick" Text="Geef alles weer"></asp:Button>
    </div> 

    <!-- Bootstrap links -->
    <script src="http://code.jquery.com/jquery.js"></script>
    <script src="js/bootstrap.min.js"></script>

    </form>
</body>
</html>
