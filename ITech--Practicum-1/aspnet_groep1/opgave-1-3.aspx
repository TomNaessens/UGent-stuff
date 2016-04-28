<%@ Page Language="C#" AutoEventWireup="true" CodeFile="opgave-1-3.aspx.cs" Inherits="_Default" %>

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head runat="server">
    <title>Muziekdatabank</title>
</head>
<body>
    <asp:Panel ID="pnlError" runat="server">
        <asp:Label ID="lblConnError" runat="server"></asp:Label>
        <asp:Label ID="lblEmptyError" runat="server"></asp:Label>
        <asp:Label ID="lblInsertError" runat="server"></asp:Label>
    </asp:Panel>
    <form id="addForm" runat="server">
    <asp:Panel ID="pnlResult" runat="server">
        <h1>
            Databank:</h1>
        <asp:GridView ID="GridView1" runat="server" AllowSorting="True" AutoGenerateColumns="False"
            CellPadding="4" DataSourceID="MuziekCataloog" DataKeyNames="id" ForeColor="#333333"
            GridLines="None" OnRowUpdated="GridView_RowUpdated" OnInit="GridView_Init">
            <RowStyle BackColor="#FFFBD6" ForeColor="#333333" />
            <Columns>
                <asp:BoundField DataField="id" HeaderText="id" InsertVisible="False" ReadOnly="True"
                    SortExpression="id" />
                <asp:BoundField DataField="Tracknr" HeaderText="Tracknr" SortExpression="Tracknr" />
                <asp:BoundField DataField="Titel" HeaderText="Titel" SortExpression="Titel" />
                <asp:HyperLinkField DataNavigateUrlFields="Uitvoerder" DataTextField="Uitvoerder" DataTextFormatString="{0}" DataNavigateUrlFormatString="http://google.com/search?q={0}" HeaderText="Uitvoerder" SortExpression="Uitvoerder" />
                <asp:BoundField DataField="Album" HeaderText="Album" SortExpression="Album" />
                <asp:BoundField DataField="Jaar" HeaderText="Jaar" SortExpression="Jaar" />
                <asp:CommandField ShowDeleteButton="True" DeleteText="Verwijder" />
            </Columns>
            <FooterStyle BackColor="#990000" Font-Bold="True" ForeColor="White" />
            <PagerStyle BackColor="#FFCC66" ForeColor="#333333" HorizontalAlign="Center" />
            <SelectedRowStyle BackColor="#FFCC66" Font-Bold="True" ForeColor="Navy" />
            <HeaderStyle BackColor="#990000" Font-Bold="True" ForeColor="White" />
            <AlternatingRowStyle BackColor="White" />
        </asp:GridView>
        <asp:SqlDataSource ID="MuziekCataloog" runat="server" ConnectionString="<%$ ConnectionStrings:itech1ConnectionString %>"
            SelectCommand="SELECT * FROM [MuziekCataloog]" 
            DeleteCommand="DELETE FROM [MuziekCataloog] WHERE [id] = @id" 
            InsertCommand="INSERT INTO [MuziekCataloog] ([Tracknr], [Titel], [Uitvoerder], [Album], [Jaar]) VALUES (@Tracknr, @Titel, @Uitvoerder, @Album, @Jaar)">
            
            <DeleteParameters>
                <asp:Parameter Name="id" Type="Int32" />
            </DeleteParameters>
            
        </asp:SqlDataSource>
    </asp:Panel>
    <asp:Panel ID="pnlAdd" runat="server">
        <h1>
            Voeg toe:</h1>
        <table style="border: 1px solid black;">
            <tr>
                <td>
                    Tracknummer:
                </td>
                <td>
                    <asp:TextBox ID="txtTracknummer" runat="server"></asp:TextBox>
                </td>
                <td>
                    <asp:RequiredFieldValidator ID="RequiredFieldValidator1" ControlToValidate="txtTrackNummer"
                        Text="Dit veld is verplicht!" runat="server" />
                </td>
            </tr>
            <tr>
                <td>
                    Titel:
                </td>
                <td>
                    <asp:TextBox ID="txtTitel" runat="server"></asp:TextBox>
                </td>
                <td>
                    <asp:RequiredFieldValidator ID="RequiredFieldValidator2" ControlToValidate="txtTitel"
                        Text="Dit veld is verplicht!" runat="server" />
                </td>
            </tr>
            <tr>
                <td>
                    Uitvoerder:
                </td>
                <td>
                    <asp:TextBox ID="txtUitvoerder" runat="server"></asp:TextBox>
                </td>
                <td>
                    <asp:RequiredFieldValidator ID="RequiredFieldValidator3" ControlToValidate="txtUitvoerder"
                        Text="Dit veld is verplicht!" runat="server" />
                </td>
            </tr>
            <tr>
                <td>
                    Album:
                </td>
                <td>
                    <asp:TextBox ID="txtAlbum" runat="server"></asp:TextBox>
                </td>
                <td>
                    <asp:RequiredFieldValidator ID="RequiredFieldValidator4" ControlToValidate="txtAlbum"
                        Text="Dit veld is verplicht!" runat="server" />
                </td>
            </tr>
            <tr>
                <td>
                    Jaar:
                </td>
                <td>
                    <asp:TextBox ID="txtJaar" runat="server"></asp:TextBox>
                </td>
                <td>
                    <asp:RequiredFieldValidator ID="RequiredFieldValidator5" ControlToValidate="txtJaar"
                        Text="Dit veld is verplicht!" runat="server" />
                </td>
            </tr>
            <tr>
                <td>
                    &nbsp;
                </td>
                <td>
                    <asp:Button ID="btnInsert" runat="server" Text="Voeg toe" OnClick="btnInsert_Click" />
                </td>
            </tr>
        </table>
    </asp:Panel>
    </form>
</body>
</html>
