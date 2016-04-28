<%@ Page Language="C#" AutoEventWireup="true" CodeFile="opgave-1-2a.aspx.cs" Inherits="opgave_1_2a" %>

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head runat="server">
    <title></title>
</head>
<body>
    <form id="optionForm" runat="server">
    <div>
        <h1>
            Opties:</h1>
        Bestand:
        <asp:TextBox ID="txtFile" runat="server" />
        <br />
        <asp:Button ID="btnScale" Text="Herschaal" runat="server" 
            onclick="btnScale_Click" />
        <asp:Button ID="btnRotation" Text="Roteer" runat="server" 
            onclick="btnRotation_Click" />
        <asp:Button ID="btnGrayscale" Text="Grijswaarden" runat="server" 
            onclick="btnGrayscale_Click" />
    </div>
    <div id="divScale" runat="server" visible="false">
        <h1>
            Herschalingsopties:</h1>
        <table>
            <tr>
                <td>
                    Breedte:
                </td>
                <td>
                    <asp:TextBox ID="txtBreedte" runat="server"></asp:TextBox>
                </td>
            </tr>
            <tr>
                <td>
                    Hoogte:
                </td>
                <td>
                    <asp:TextBox ID="txtHoogte" runat="server"></asp:TextBox>
                </td>
            </tr>
            <tr>
                <td>
                    &nbsp;
                </td>
                <td>
                    <asp:Button ID="btnDoScale" runat="server" Text="Herschaal" 
                        onclick="btnDoScale_Click"></asp:Button>
                </td>
            </tr>
        </table>
    </div>
    <div id="divRotate" runat="server" visible="false">
        <h1>
            Rotatieopties:</h1>
        <asp:RadioButtonList ID="RotationAngle" runat="server">
            <asp:ListItem Value="90" Selected="True">90°</asp:ListItem>
            <asp:ListItem Value="180">180°</asp:ListItem>
            <asp:ListItem Value="270">270°</asp:ListItem>
        </asp:RadioButtonList>
        <asp:Button ID="btnDoRotate" runat="server" text="Roteer" 
            onclick="btnDoRotate_Click" />
    </div>
    </form>
</body>
</html>
