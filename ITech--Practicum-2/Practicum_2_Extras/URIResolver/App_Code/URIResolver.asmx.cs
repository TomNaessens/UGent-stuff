using System;
using System.Collections;
using System.ComponentModel;
using System.Data;
using System.Diagnostics;
using System.Web;
using System.Web.Services;

namespace URIResolver
{
	/// <summary>
	/// Summary description for URIResolver.
	/// </summary>
	[WebService(Namespace="urn:be:ugent:mmlab:uriresolver")]
	public class URIResolver : System.Web.Services.WebService
	{
		private Hashtable uriTable = new Hashtable();
		private Random generator = new Random();

		public URIResolver()
		{
			//CODEGEN: This call is required by the ASP.NET Web Services Designer
			InitializeComponent();
			InitialzeURITable();
		}

		#region Component Designer generated code
		
		//Required by the Web Services Designer 
		private IContainer components = null;
				
		/// <summary>
		/// Required method for Designer support - do not modify
		/// the contents of this method with the code editor.
		/// </summary>
		private void InitializeComponent()
		{

		}

		/// <summary>
		/// Clean up any resources being used.
		/// </summary>
		protected override void Dispose( bool disposing )
		{
			if(disposing && components != null)
			{
				components.Dispose();
			}
			base.Dispose(disposing);		
		}
		
		#endregion

		#region .Helper Functions

		private void InitialzeURITable()
		{
			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:black_hawk_down", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/black_hawk_down_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/black_hawk_down_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:brotherhood_of_the_wolf", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/brotherhood_of_the_wolf_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/brotherhood_of_the_wolf_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:charlie_chocolate", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/charlie_chocolate_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/charlie_chocolate_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:constantine", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/constantine_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/constantine_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:corpse_bride", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/corpse_bride_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/corpse_bride_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:day_after_tomorrow", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/day_after_tomorrow_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/day_after_tomorrow_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:finding_neverland", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/finding_neverland_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/finding_neverland_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:flying_daggers", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/flying_daggers_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/flying_daggers_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:harry_potter_azkaban", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/harry_potter_azkaban_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/harry_potter_azkaban_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:ice_age", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/ice_age_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/ice_age_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:kingdom_of_heaven", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/kingdom_of_heaven_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/kingdom_of_heaven_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:monsters_inc", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/monsters_inc_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/monsters_inc_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:return_of_the_king", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/return_of_the_king_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/return_of_the_king_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:sin_city", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/sin_city_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/sin_city_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:the_aviator", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/the_aviator_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/the_aviator_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:the_merchant_of_venice", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/the_merchant_of_venice_m480.wmv", 
                                      "mms://multimedialab.elis.ugent.be/trailers/the_merchant_of_venice_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:the_new_world", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/the_new_world_m480.wmv",
                                      "mms://multimedialab.elis.ugent.be/trailers/the_new_world_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:underworld", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/underworld_m480.wmv",
                                      "mms://multimedialab.elis.ugent.be/trailers/underworld_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:van_helsing", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/van_helsing_m480.wmv",
                                      "mms://multimedialab.elis.ugent.be/trailers/van_helsing_m480.wmv"});

			uriTable.Add("urn:mpeg:mpeg21:be:ugent:mmlab:trailers:war_of_the_worlds", 
				new string[2]{"mms://vbuxtehude.elis.ugent.be/trailers/war_of_the_worlds_m480.wmv",
                                      "mms://multimedialab.elis.ugent.be/trailers/war_of_the_worlds_m480.wmv"});
		}

		#endregion

		#region .Web Methods

		[WebMethod]
		public string ResolveURI(string uri)
		{
			if ( uriTable.Contains(uri) )
			{
				return ((string [])uriTable[uri])[generator.Next(0,2)];
			}
			else 
				return null;
		}

		#endregion

	}

}
