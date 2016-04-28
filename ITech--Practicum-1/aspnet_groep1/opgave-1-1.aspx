<%@ Page Language="C#" AutoEventWireup="true" CodeFile="opgave-1-1.aspx.cs" Inherits="_Default" %>

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head id="Head1" runat="server">
    <title>Maak tabel</title>
</head>
<body>
    <form id="tableForm" runat="server">
    <div>
        <table>
            <tr>
                <td>
                    Aantal rijen:
                </td>
                <td>
                    <asp:TextBox id="txtAantalRijen" runat="server">5</asp:TextBox>
                </td>
            </tr>
            <tr>
                <td>
                    Aantal kolommen:
                </td>
                <td>
                    <asp:TextBox id="txtAantalKolommen" runat="server">5</asp:TextBox>
                </td>
            </tr>
            <tr>
                <td>
                    Achtergrondkleur even kolommen:
                </td>
                <td>
                    <asp:DropDownList id="slctEvenAchtergrond" runat="server">
                        <asp:ListItem Value="red" Selected="True">Rood</asp:ListItem>
                        <asp:ListItem Value="blue">Blauw</asp:ListItem>
                        <asp:ListItem Value="black">Zwart</asp:ListItem>
                        <asp:ListItem Value="white">Wit</asp:ListItem>
                        <asp:ListItem Value="green">Groen</asp:ListItem>
                        <asp:ListItem Value="cyan">Lichtblauw</asp:ListItem>
                        <asp:ListItem Value="purple">Paars</asp:ListItem>
                    </asp:DropDownList>
                </td>
            </tr>
            <tr>
                <td>
                    Achtergrondkleur oneven kolommen:
                </td>
                <td>
                    <asp:DropDownList id="slctOnevenAchtergrond" runat="server">
                        <asp:ListItem Value="red">Rood</asp:ListItem>
                        <asp:ListItem Value="blue" Selected="True">Blauw</asp:ListItem>
                        <asp:ListItem Value="black">Zwart</asp:ListItem>
                        <asp:ListItem Value="white">Wit</asp:ListItem>
                        <asp:ListItem Value="green">Groen</asp:ListItem>
                        <asp:ListItem Value="cyan">Lichtblauw</asp:ListItem>
                        <asp:ListItem Value="purple">Paars</asp:ListItem>
                    </asp:DropDownList>
                </td>
            </tr>
            <tr>
                <td>
                    Dikte van de rand van de tabel:
                </td>
                <td>
                    <asp:TextBox id="txtDikteRand" runat="server">5</asp:TextBox>
                    (in pixels)
                </td>
            </tr>
            <tr>
                <td>
                    Breedte tabel:
                </td>
                <td>
                    <asp:TextBox ID="txtBreedteTabel" runat="server">50</asp:TextBox>
                    (in procenten)
                </td>
            </tr>
            <tr>
                <td>
                    &nbsp;
                </td>
                <td>
                    <asp:Button ID="btnMaakTabel" runat="server" Text="Maak tabel" OnClick="btnMaakTabel_Click" />
                </td>
            </tr>
        </table>
    </div>
    </form>
   
    <asp:Table ID="tblResultTable" runat="server">
    </asp:Table>
</body>
</html>