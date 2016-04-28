<?xml version='1.0'?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns="http://www.w3.org/TR/REC-html40" xmlns:xsv="http://www.w3.org/2000/05/xsv" version="1.0">
 <!-- $Id: xsv.xsl,v 1.11 2001/11/20 08:49:39 ht Exp $ -->
 <!-- Stylesheet for XSV output:  this version for IE5 + MSXML3 of 2000-05 -->
 
 <xsl:output method="html" indent="yes"/>

 <!-- The real stylesheet starts here -->
 <xsl:template match="/">
  <HTML>
   <HEAD>
    <TITLE>
     Schema validation report for
	<xsl:value-of select="xsv:xsv/@target"/>
    </TITLE>
    <STYLE>P.nas { margin-left: 1em; color: red; margin-top: 0px}
           P.sdf { margin-bottom: 0px }
           .node { font-weight: bold }
    </STYLE>
   </HEAD>
   <BODY>
    <xsl:apply-templates/>
   </BODY>
  </HTML>
 </xsl:template>
 
 <xsl:template match="xsv:xsv">
  <H3>Schema validating with <xsl:value-of select="@version"/></H3>
  <xsl:if test="@crash">
    <P><STRONG>Schema validator crashed</STRONG><BR/>
The maintainers of XSV will be notified, you don't need to
send mail about this unless you have extra information to provide.
If there are Schema errors reported below, try correcting
them and re-running the validation.</P>
  </xsl:if>
  <UL>
    <xsl:apply-templates select="@target"/>
    <xsl:apply-templates select="@docElt"/>
    <xsl:apply-templates select="@validation"/>
    <xsl:apply-templates select="@schemaLocs"/>
    <xsl:apply-templates select="@schemaDocs"/>
    <xsl:apply-templates select="@schemaErrors"/>
    <xsl:apply-templates select="@instanceAssessed"/>
  </UL>
  <HR/>
  <xsl:if test="xsv:XMLMessages">
  <xsl:apply-templates select="xsv:XMLMessages"/>
  </xsl:if>
  
  <xsl:if test="xsv:schemaDocAttempt">
   <H3>Schema resources involved</H3>
   <xsl:apply-templates select="xsv:schemaDocAttempt"/>
   <HR/>
  </xsl:if>
  <xsl:if test="xsv:schemaWarning">
   <H3>Schema representation Warnings</H3>
   <xsl:if test="xsv:schemaWarning[@phase='schema']">
    <H4>Detected during schema construction</H4>
    <xsl:for-each select="xsv:schemaWarning[@phase='schema']">
     <xsl:call-template name="warn"/>
    </xsl:for-each>
   </xsl:if>
   <xsl:if test="xsv:schemaWarning[@phase='instance']">
    <H4>Detected during instance validation</H4>
    <xsl:for-each select="xsv:schemaWarning[@phase='instance']">
     <xsl:call-template name="warn"/>
    </xsl:for-each>
   </xsl:if>
  </xsl:if>
  <xsl:if test="xsv:schemaError">
   <H3>Schema representation errors</H3>
  <xsl:if test="xsv:schemaError[@phase='schema']">
    <H4>Detected during schema construction</H4>
    <xsl:for-each select="xsv:schemaError[@phase='schema']">
     <xsl:call-template name="error"/>
    </xsl:for-each>
   </xsl:if>
   <xsl:if test="xsv:schemaError[@phase='instance']">
    <H4>Detected during instance validation</H4>
    <xsl:for-each select="xsv:schemaError[@phase='instance']">
     <xsl:call-template name="error"/>
    </xsl:for-each>
   </xsl:if>
  </xsl:if>
  <xsl:if test="xsv:invalid|xsv:warning">
   <H3>Problems with the schema-validity of the target</H3> 
  <xsl:apply-templates select="xsv:invalid|xsv:warning"/>
  </xsl:if>
 </xsl:template>
 
 <xsl:template match="@*">
  <LI>
<STRONG>
<xsl:value-of select="name()"/>
</STRONG>: <xsl:value-of select="."/></LI>
 </xsl:template>
 
 <xsl:template match="@schemaDocs|@docElt">
  <LI>
<STRONG>
<xsl:value-of select="name()"/>
</STRONG>: <CODE><xsl:value-of select="."/></CODE></LI>
 </xsl:template>
 
  <xsl:template match="@target">
  <LI><STRONG>Target</STRONG>: <CODE><xsl:value-of select="."/></CODE>
   <xsl:if test="../@realName"><BR/>&#160;&#160;&#160;(<xsl:apply-templates select="../@realName"/>
   <xsl:apply-templates select="../@size"/>
   <xsl:apply-templates select="../@modDate"/>
   <xsl:apply-templates select="../@server"/>)</xsl:if></LI>
 </xsl:template>
 
 <xsl:template match="@realName">Real name: <xsl:value-of select="."/></xsl:template>
  
 <xsl:template match="@size">
  <BR/>&#160;&#160;&#160;&#160;Length: <xsl:value-of select="."/> bytes
 </xsl:template>
  
 <xsl:template match="@modDate">
  <BR/>&#160;&#160;&#160;&#160;Last Modified: <xsl:value-of select="."/>
 </xsl:template>
  
 <xsl:template match="@server">
  <BR/>&#160;&#160;&#160;&#160;Server: <xsl:value-of select="."/>
 </xsl:template>
 
 <xsl:template match="@schemaErrors">
  <xsl:variable name="val" select="."/>
  <LI>The schema(s) used for schema-validation had
  <xsl:choose>
   <xsl:when test="$val=0">no</xsl:when>
   <xsl:when test="$val=-1">no</xsl:when>
   <xsl:otherwise><xsl:value-of select="$val"/></xsl:otherwise>
  </xsl:choose> error<xsl:choose>
   <xsl:when test="$val=1"></xsl:when>
   <xsl:otherwise>s</xsl:otherwise>
  </xsl:choose>
</LI>
 </xsl:template>
 
 <xsl:template match="@instanceAssessed">
  <xsl:variable name="val" select="."/>
  <LI>
   <xsl:choose>
   <xsl:when test="$val='false'"><xsl:text>The target was not assessed</xsl:text></xsl:when>
    <xsl:otherwise><xsl:apply-templates select="../@instanceErrors"/></xsl:otherwise>
  </xsl:choose></LI>
 </xsl:template>
 
  <xsl:template match="@instanceErrors">
  <xsl:variable name="val" select="."/>
   <xsl:choose>
   <xsl:when test="$val=0">No schema-validity problems were</xsl:when>
   <xsl:when test="$val=1">1 schema-validity problem was</xsl:when>
    <xsl:otherwise><xsl:value-of select="$val"/> schema-validity problems were</xsl:otherwise>
  </xsl:choose> found in the target
 </xsl:template>
 
 <xsl:template match="@validation[.='lax']">
  <LI>No declaration for document root found, validation was lax</LI>
 </xsl:template>
 
 <xsl:template match="@validation[.='strict']">
  <LI>Validation was strict, starting with type <CODE><xsl:value-of select="../@rootType"/></CODE></LI>
 </xsl:template>
 
 <xsl:template match="xsv:XMLMessages">
  <H3>Low-level XML well-formedness and/or validity processing output</H3>
  <P>
  <PRE><xsl:apply-templates/></PRE>
  </P>
  <HR/>
 </xsl:template>
 
 <xsl:template match="xsv:schemaDocAttempt">
  <xsl:call-template name="resourceAttempt">
   <xsl:with-param name="rtype"><xsl:value-of select="@source"></xsl:value-of></xsl:with-param>
  </xsl:call-template>
 </xsl:template> 

 <xsl:template name="resourceAttempt">
  <xsl:param name="rtype"/>
  <P CLASS="sdf">Attempt to load a schema document from
<xsl:choose>
 <xsl:when test="@trueURI"><CODE><xsl:value-of select="@trueURI"/></CODE> (via <CODE><xsl:value-of select="@URI"/></CODE>)</xsl:when>
 <xsl:otherwise><CODE><xsl:value-of select="@URI"/></CODE></xsl:otherwise>
</xsl:choose>
 (source: <CODE><xsl:value-of select="@source"/></CODE>) for
   <xsl:choose><xsl:when test="@namespace"><CODE><xsl:value-of select="@namespace"/></CODE></xsl:when>
    <xsl:otherwise>no namespace</xsl:otherwise>
   </xsl:choose>,
   <xsl:choose>
    <xsl:when test="@outcome='success'"> succeeded</xsl:when>
    <xsl:when test="@outcome='redundant'"> skipped, already loaded</xsl:when>
    <xsl:when test="@outcome='skipped'"> skipped, other docs already loaded for
this namespace: <xsl:value-of select="@otherLocs"/></xsl:when>
    <xsl:when test="@outcome='failure'"> failed:</xsl:when>
   </xsl:choose>
</P>
  <xsl:apply-templates select="xsv:notASchema"/>
 </xsl:template>
 
 <xsl:template match="xsv:notASchema">
  <P CLASS="nas">
   <xsl:apply-templates/>
  </P>
 </xsl:template>

 <xsl:template match="xsv:invalid" name="error">
  <P><SPAN STYLE="color: red"><xsl:value-of select="@resource"/>:<xsl:value-of select="@line"/>:<xsl:value-of select="@char"/></SPAN>: <SPAN STYLE="color: blue">Invalid<xsl:if test="@code">&#160;per&#160;<A>
<xsl:choose><xsl:when test="contains(@code,'.')"><xsl:attribute name="HREF">http://www.w3.org/TR/xmlschema-1/#<xsl:value-of select="substring-before(@code,'.')"/></xsl:attribute></xsl:when><xsl:otherwise><xsl:attribute name="HREF">http://www.w3.org/TR/xmlschema-1/#<xsl:value-of select="@code"/></xsl:attribute></xsl:otherwise></xsl:choose>
<xsl:value-of select="@code"/></A></xsl:if></SPAN>: <xsl:apply-templates/></P>
  <!-- would like to use whole code, but the clauses don't have IDs yet -->
 </xsl:template>
 
 <xsl:template match="xsv:warning" name="warn">
  <P><SPAN STYLE="color: green"><xsl:value-of select="@resource"/>:<xsl:value-of select="@line"/>:<xsl:value-of select="@char"/></SPAN>: <SPAN STYLE="color: blue">Warning</SPAN>: <xsl:value-of select="."/></P>
 </xsl:template>
 
 <xsl:template match="xsv:fsm">
  <DIV>
   <H4>Finite State Machine for content model</H4>
   <DL><xsl:apply-templates/></DL>
  </DIV>
 </xsl:template>
 
 <xsl:template match="xsv:node">
  <DT CLASS="node"><xsl:value-of select="@id"/>
<xsl:if test="@final">*</xsl:if></DT>
  <DD><xsl:apply-templates/></DD>
 </xsl:template>
  
 <xsl:template match="xsv:edge">
  <xsl:value-of select="@label"/>&#160;->&#160;<SPAN CLASS="node"><xsl:value-of select="@dest"/></SPAN><BR/>
 </xsl:template>
</xsl:stylesheet>
