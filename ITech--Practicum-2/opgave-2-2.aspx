<%@ Page Language="C#" AutoEventWireup="true" CodeFile="opgave-2-2.aspx.cs" Inherits="opgave_2_2" %>

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">

<html xmlns="http://www.w3.org/1999/xhtml">
<head runat="server">
    <title></title>
</head>
<body>
<center>
    <form id="frmMain" runat="server">
    <asp:Panel ID="pnlCoverAlbums" runat="server">
        Informatie:<br />
        <asp:Label ID="lblCollectionDescription" runat="server"></asp:Label><br />
        Aantal trailers: <asp:Label ID="lblAmountOfTrailers" runat="server"></asp:Label>
        <br />
        <br />
        <asp:ImageButton ID="imgbtnCover1" runat="server" onclick="imgbtnCover1_Click" />
        <asp:ImageButton ID="imgbtnCover2" runat="server" onclick="imgbtnCover2_Click" />
        <asp:ImageButton ID="imgbtnCover3" runat="server" onclick="imgbtnCover3_Click" />
        <asp:HiddenField ID="hdnCover1" runat="server" />
        <asp:HiddenField ID="hdnCover2" runat="server" />
        <asp:HiddenField ID="hdnCover3" runat="server" />
        <br />
        <br />
        <asp:Button ID="btnNewTrailers" runat="server" Text="Nieuwe covers" 
            onclick="btnNewTrailers_Click" />
    </asp:Panel>
    
    <asp:Panel ID="pnlTrailer" runat="server">
        <div id="itech1" runat="server"></div>
        <asp:Button ID="btnBackToSelection" runat="server" Text="Terug naar selectie" 
            onclick="btnBackToSelection_Click" />
    </asp:Panel>
    </form>
</center>
</body>
</html>
