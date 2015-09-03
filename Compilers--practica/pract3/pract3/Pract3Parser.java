// Generated from Pract3.g4 by ANTLR 4.5

  // import java packages
  import java.lang.String;
  import java.util.Set;
  import java.util.HashSet;
  import java.util.Arrays;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class Pract3Parser extends Parser {
	static { RuntimeMetaData.checkVersion("4.5", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		WS=1, BOOK_KEY=2, ARTICLE_KEY=3, INPROCEEDINGS_KEY=4, UNDEFINED_KEY=5, 
		AUTHOR_KEY=6, TITLE_KEY=7, YEAR_KEY=8, PUBLISHER_KEY=9, JOURNAL_KEY=10, 
		PAGES_KEY=11, VOLUME_KEY=12, NUMBER_KEY=13, MONTH_KEY=14, ISSN_KEY=15, 
		DOI_KEY=16, ADDRESS_KEY=17, URL_KEY=18, BOOKTITLE_KEY=19, FS=20, RS=21, 
		EQ=22, QM=23, LB=24, RB=25, LCB=26, RCB=27, NUMBER=28, WORD=29;
	public static final int
		RULE_bibtex = 0, RULE_string = 1, RULE_address = 2, RULE_entry = 3, RULE_book = 4, 
		RULE_article = 5, RULE_inproceedings = 6, RULE_undefined = 7, RULE_book_type_value = 8, 
		RULE_book_fields = 9, RULE_book_field = 10, RULE_article_type_value = 11, 
		RULE_article_fields = 12, RULE_article_field = 13, RULE_inproceedings_type_value = 14, 
		RULE_inproceedings_fields = 15, RULE_inproceedings_field = 16, RULE_ig_type_value = 17, 
		RULE_ig_fields = 18, RULE_ig_field = 19, RULE_author_field = 20, RULE_title_field = 21, 
		RULE_publisher_field = 22, RULE_pages_field = 23, RULE_volume_field = 24, 
		RULE_number_field = 25, RULE_journal_field = 26, RULE_booktitle_field = 27, 
		RULE_year_field = 28, RULE_month_field = 29, RULE_issn_field = 30, RULE_doi_field = 31, 
		RULE_address_field = 32, RULE_url_field = 33, RULE_any_value = 34, RULE_text_value = 35, 
		RULE_numeric_value = 36, RULE_month_value = 37, RULE_month = 38, RULE_numeric_range = 39, 
		RULE_issn_range = 40, RULE_address_value = 41;
	public static final String[] ruleNames = {
		"bibtex", "string", "address", "entry", "book", "article", "inproceedings", 
		"undefined", "book_type_value", "book_fields", "book_field", "article_type_value", 
		"article_fields", "article_field", "inproceedings_type_value", "inproceedings_fields", 
		"inproceedings_field", "ig_type_value", "ig_fields", "ig_field", "author_field", 
		"title_field", "publisher_field", "pages_field", "volume_field", "number_field", 
		"journal_field", "booktitle_field", "year_field", "month_field", "issn_field", 
		"doi_field", "address_field", "url_field", "any_value", "text_value", 
		"numeric_value", "month_value", "month", "numeric_range", "issn_range", 
		"address_value"
	};

	private static final String[] _LITERAL_NAMES = {
		null, null, "'@book'", "'@article'", "'@inproceedings'", null, "'author'", 
		"'title'", "'year'", "'publisher'", "'journal'", "'pages'", "'volume'", 
		"'number'", "'month'", "'issn'", "'doi'", "'address'", "'url'", "'booktitle'", 
		"','", "'-'", "'='", "'\"'", "'('", "')'", "'{'", "'}'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "WS", "BOOK_KEY", "ARTICLE_KEY", "INPROCEEDINGS_KEY", "UNDEFINED_KEY", 
		"AUTHOR_KEY", "TITLE_KEY", "YEAR_KEY", "PUBLISHER_KEY", "JOURNAL_KEY", 
		"PAGES_KEY", "VOLUME_KEY", "NUMBER_KEY", "MONTH_KEY", "ISSN_KEY", "DOI_KEY", 
		"ADDRESS_KEY", "URL_KEY", "BOOKTITLE_KEY", "FS", "RS", "EQ", "QM", "LB", 
		"RB", "LCB", "RCB", "NUMBER", "WORD"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Pract3.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }


	  // Keep a list of valid months, more explanation is given in the setMonth() method why
	  // we choose this approach
	  public final static Set validMonths = new HashSet(Arrays.asList(new String[] {
	    "January", "Februari", "March", "April", "May", "June",
	    "Juli", "August", "September", "October", "November", "December",
	    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
	    "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12"
	  }));

	  // Accession number of the records
	  public static int rec_accession = 1; // Record counter

	  // Information about the record being processed
	  public static int current_ref_type = -1; // Type of the current record
	  public static String current_year = "";  // Year of the current record
	  public static String current_month = ""; // Month of the current record

	  public static boolean labelSet;
	  public static boolean authorSet;
	  public static boolean titleSet;
	  public static boolean yearSet;
	  public static boolean publisherSet;
	  public static boolean journalSet;
	  public static boolean volumeSet;
	  public static boolean numberSet;
	  public static boolean pagesSet;
	  public static boolean booktitleSet;

	  // EndNote XML print methods
	  public static void xmlout(String x, String y) { System.out.println("<"+x+">"+y+"</"+x+">");}
	  public static void xmlb(String x)             { System.out.println("<" +x+">");}
	  public static void xmle(String x)             { System.out.println("</"+x+">");}

	  // Begins a record with an ID
	  public static void printBeginRecord(int id) {
	    // Start of a new record: unset all the varibales
	    resetSetters();
	    resetCurrent();

	    // Start a new record entry
	    xmlb("record");
	    xmlout("rec-number", "" + rec_accession);
	    rec_accession++;

	    // Set the current ref type
	    current_ref_type = id;
	  }

	  // Ends a record
	  public static void printEndRecord() {
	    // Now we've parsed all information, we'll have to do some additional work:
	    //
	    // Check wether all mandatory fields exist
	    switch (current_ref_type) {
	      case 6: // Book
	        if (!(labelSet && authorSet && titleSet && yearSet && publisherSet)) {
	          System.err.println("Please set all mandatory book fields");
	        }
	        break;
	      case 17: // Article: special case with the (volume and number) or year here
	        if (!(labelSet && authorSet && titleSet && journalSet && pagesSet && ((volumeSet && numberSet) || yearSet))) {
	          System.err.println("Please set all mandatory article fields");
	        }
	        break;
	      case 47: // Inproceedings
	        if (!(labelSet && authorSet && titleSet && booktitleSet && yearSet)) {
	          System.err.println("Please set all mandatory inproceedings fields");
	        }
	        break;
	      default:
	        // This should not happen
	        System.err.println("This ref type was not recognized and should have been ignored" + current_ref_type);
	    }

	    // Print the dates
	    printDates();

	    xmle("record");
	  }

	  // Prints the ref-type
	  public static void printLabel(String l) {
	    System.out.println("<ref-type name=\"" + l + "\">" + current_ref_type + "</ref-type>");
	  }

	  // Prints the authors
	  public static void printAuthors(String as) {
	    String[] authors = as.split(" and | AND ");

	    xmlb("contributors");
	    xmlb("authors");

	    for(String author : authors) {
	        xmlout("author", author);
	    }

	    xmle("authors");
	    xmle("contributors");
	  }

	  // Print the title
	  public static void printTitle(String t) {
	    xmlb("titles");
	    xmlout("title", t);
	    xmle("titles");
	  }

	  // Print the volume
	  public static void printVolume(String v) {
	    xmlout("volume", v);
	  }

	  // Print the number
	  public static void printNumber(String n) {
	    xmlout("number", n);
	  }

	  // Print the pages
	  public static void printPages(String begin, String end) {
	    int b = Integer.parseInt(begin);
	    int e = Integer.parseInt(end);

	    if (b > e) {
	      System.err.println("Beginning of page range is bigger than ending.");
	    } else {
	      xmlout("pages", b + "--" + e);
	    }
	  }

	  // Print the publisher
	  public static void printPublisher(String p) {
	    xmlout("publisher", p);
	  }

	  // Print the dates
	  public static void printDates() {
	    if(!"".equals(current_month) || !"".equals(current_year)) {
	      xmlb("dates");
	      if(!"".equals(current_year)) {
	        xmlout("year", current_year);
	      }
	      if(!"".equals(current_month)) {
	        xmlout("month", current_month);
	      }
	      xmle("dates");
	    }
	  }

	  // Sets the year variable
	  public static void setYear(String y) {
	    yearSet = true;
	    current_year = y;
	  }

	  // Sets the month variable
	  // This needs some explanation: It should be possible to check the validity of
	  // the formatting of the months in the language by checking if the value is one of
	  // January .. December, Jan .. Dec or 1..12. But this approach prohibited two things:
	  // If the month was misspelled (Ian instead of Jan for example), it wouldn't trigger
	  // any error as it matched the ig_field (which ignores fields who shouldn't be in the
	  // BibTex type. So it was not possible to trigger a custom error.
	  // Instead, we'll match any WORD or NUMBER, parse it within Java and trigger an error
	  // if the value isn't an allowed value.
	  public static void setMonth(String m) {
	    // If the validMonths set contains m, all is good, proceed:
	    if(validMonths.contains(m)) {
	      current_month = m;
	    } else { // Else, find out which format the user used and trigger an appropriate warning
	      // Check if we have a number
	      int month_number;
	      try {
	        month_number = Integer.parseInt(m);
	      } catch(NumberFormatException e) {
	        // We don't have a number, so it's probably a string:
	        if(m.length() == 3) { // Did the user mistype a 3-letter abbreviation?
	          System.err.println("It seems like you entered a wrong 3-letter abbreviation. Please use "
	                           + "one of the following: Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec. "
	                           + "Full month names and numbers (1..12) are also allowed.");
	        } else { // Or did he perhaps mistype the full name?
	          System.err.println("It seems like you entered an unexisting month name. "
	                           + "Abbreviated month names and numbers (1..12) are also allowed.");
	        }
	        return;
	      }
	      // We have a number, but why is it wrong?
	      System.err.println("Please provide a valid number for the month field between 1 and 12. "
	                      + "Full month names and 3-letter abbreviatons are also allowed.");
	    }
	  }

	  // Set and unset the set variables methods
	  public static void setLabel()     { labelSet     = true; }
	  public static void setAuthor()    { authorSet    = true; }
	  public static void setTitle()     { titleSet     = true; }
	  public static void setPublisher() { publisherSet = true; }
	  public static void setJournal()   { journalSet   = true; }
	  public static void setVolume()    { volumeSet    = true; }
	  public static void setNumber()    { numberSet    = true; }
	  public static void setPages()     { pagesSet     = true; }
	  public static void setBooktitle() { booktitleSet = true; }

	  public static void resetSetters() {
	    labelSet     = false;
	    authorSet    = false;
	    titleSet     = false;
	    yearSet      = false;
	    publisherSet = false;
	    volumeSet    = false;
	    numberSet    = false;
	    journalSet   = false;
	    pagesSet     = false;
	    booktitleSet = false;
	  }

	  // Reset the current variables
	  public static void resetCurrent() {
	    current_ref_type = -1;
	    current_year = "";
	    current_month = "";
	  }

	public Pract3Parser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class BibtexContext extends ParserRuleContext {
		public TerminalNode EOF() { return getToken(Pract3Parser.EOF, 0); }
		public List<EntryContext> entry() {
			return getRuleContexts(EntryContext.class);
		}
		public EntryContext entry(int i) {
			return getRuleContext(EntryContext.class,i);
		}
		public BibtexContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bibtex; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterBibtex(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitBibtex(this);
		}
	}

	public final BibtexContext bibtex() throws RecognitionException {
		BibtexContext _localctx = new BibtexContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_bibtex);
		System.out.println("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n<xml>\r\n<records>");
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(87);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << BOOK_KEY) | (1L << ARTICLE_KEY) | (1L << INPROCEEDINGS_KEY) | (1L << UNDEFINED_KEY))) != 0)) {
				{
				{
				setState(84);
				entry();
				}
				}
				setState(89);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(90);
			match(EOF);
			}
			System.out.println("</records>\r\n</xml>");
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StringContext extends ParserRuleContext {
		public List<TerminalNode> WORD() { return getTokens(Pract3Parser.WORD); }
		public TerminalNode WORD(int i) {
			return getToken(Pract3Parser.WORD, i);
		}
		public StringContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_string; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterString(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitString(this);
		}
	}

	public final StringContext string() throws RecognitionException {
		StringContext _localctx = new StringContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_string);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(92);
			match(WORD);
			setState(96);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==WORD) {
				{
				{
				setState(93);
				match(WORD);
				}
				}
				setState(98);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AddressContext extends ParserRuleContext {
		public List<StringContext> string() {
			return getRuleContexts(StringContext.class);
		}
		public StringContext string(int i) {
			return getRuleContext(StringContext.class,i);
		}
		public List<TerminalNode> FS() { return getTokens(Pract3Parser.FS); }
		public TerminalNode FS(int i) {
			return getToken(Pract3Parser.FS, i);
		}
		public AddressContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_address; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterAddress(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitAddress(this);
		}
	}

	public final AddressContext address() throws RecognitionException {
		AddressContext _localctx = new AddressContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_address);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(99);
			string();
			setState(104);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==FS) {
				{
				{
				setState(100);
				match(FS);
				setState(101);
				string();
				}
				}
				setState(106);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EntryContext extends ParserRuleContext {
		public BookContext book() {
			return getRuleContext(BookContext.class,0);
		}
		public ArticleContext article() {
			return getRuleContext(ArticleContext.class,0);
		}
		public InproceedingsContext inproceedings() {
			return getRuleContext(InproceedingsContext.class,0);
		}
		public UndefinedContext undefined() {
			return getRuleContext(UndefinedContext.class,0);
		}
		public EntryContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_entry; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterEntry(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitEntry(this);
		}
	}

	public final EntryContext entry() throws RecognitionException {
		EntryContext _localctx = new EntryContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_entry);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(111);
			switch (_input.LA(1)) {
			case BOOK_KEY:
				{
				setState(107);
				book();
				}
				break;
			case ARTICLE_KEY:
				{
				setState(108);
				article();
				}
				break;
			case INPROCEEDINGS_KEY:
				{
				setState(109);
				inproceedings();
				}
				break;
			case UNDEFINED_KEY:
				{
				setState(110);
				undefined();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BookContext extends ParserRuleContext {
		public TerminalNode BOOK_KEY() { return getToken(Pract3Parser.BOOK_KEY, 0); }
		public Book_type_valueContext book_type_value() {
			return getRuleContext(Book_type_valueContext.class,0);
		}
		public BookContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_book; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterBook(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitBook(this);
		}
	}

	public final BookContext book() throws RecognitionException {
		BookContext _localctx = new BookContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_book);
		try {
			enterOuterAlt(_localctx, 1);
			{
			printBeginRecord(6);
			setState(114);
			match(BOOK_KEY);
			setState(115);
			book_type_value();
			printEndRecord();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArticleContext extends ParserRuleContext {
		public TerminalNode ARTICLE_KEY() { return getToken(Pract3Parser.ARTICLE_KEY, 0); }
		public Article_type_valueContext article_type_value() {
			return getRuleContext(Article_type_valueContext.class,0);
		}
		public ArticleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_article; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterArticle(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitArticle(this);
		}
	}

	public final ArticleContext article() throws RecognitionException {
		ArticleContext _localctx = new ArticleContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_article);
		try {
			enterOuterAlt(_localctx, 1);
			{
			printBeginRecord(17);
			setState(119);
			match(ARTICLE_KEY);
			setState(120);
			article_type_value();
			printEndRecord();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class InproceedingsContext extends ParserRuleContext {
		public TerminalNode INPROCEEDINGS_KEY() { return getToken(Pract3Parser.INPROCEEDINGS_KEY, 0); }
		public Inproceedings_type_valueContext inproceedings_type_value() {
			return getRuleContext(Inproceedings_type_valueContext.class,0);
		}
		public InproceedingsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_inproceedings; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterInproceedings(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitInproceedings(this);
		}
	}

	public final InproceedingsContext inproceedings() throws RecognitionException {
		InproceedingsContext _localctx = new InproceedingsContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_inproceedings);
		try {
			enterOuterAlt(_localctx, 1);
			{
			printBeginRecord(47);
			setState(124);
			match(INPROCEEDINGS_KEY);
			setState(125);
			inproceedings_type_value();
			printEndRecord();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UndefinedContext extends ParserRuleContext {
		public TerminalNode UNDEFINED_KEY() { return getToken(Pract3Parser.UNDEFINED_KEY, 0); }
		public Ig_type_valueContext ig_type_value() {
			return getRuleContext(Ig_type_valueContext.class,0);
		}
		public UndefinedContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_undefined; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterUndefined(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitUndefined(this);
		}
	}

	public final UndefinedContext undefined() throws RecognitionException {
		UndefinedContext _localctx = new UndefinedContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_undefined);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(128);
			match(UNDEFINED_KEY);
			setState(129);
			ig_type_value();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Book_type_valueContext extends ParserRuleContext {
		public Token l;
		public TerminalNode LB() { return getToken(Pract3Parser.LB, 0); }
		public TerminalNode FS() { return getToken(Pract3Parser.FS, 0); }
		public Book_fieldsContext book_fields() {
			return getRuleContext(Book_fieldsContext.class,0);
		}
		public TerminalNode RB() { return getToken(Pract3Parser.RB, 0); }
		public TerminalNode WORD() { return getToken(Pract3Parser.WORD, 0); }
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Book_type_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_book_type_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterBook_type_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitBook_type_value(this);
		}
	}

	public final Book_type_valueContext book_type_value() throws RecognitionException {
		Book_type_valueContext _localctx = new Book_type_valueContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_book_type_value);
		try {
			setState(145);
			switch (_input.LA(1)) {
			case LB:
				enterOuterAlt(_localctx, 1);
				{
				setState(131);
				match(LB);
				setState(132);
				((Book_type_valueContext)_localctx).l = match(WORD);
				setLabel(); printLabel((((Book_type_valueContext)_localctx).l!=null?((Book_type_valueContext)_localctx).l.getText():null));
				setState(134);
				match(FS);
				setState(135);
				book_fields();
				setState(136);
				match(RB);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(138);
				match(LCB);
				setState(139);
				((Book_type_valueContext)_localctx).l = match(WORD);
				setLabel(); printLabel((((Book_type_valueContext)_localctx).l!=null?((Book_type_valueContext)_localctx).l.getText():null));
				setState(141);
				match(FS);
				setState(142);
				book_fields();
				setState(143);
				match(RCB);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Book_fieldsContext extends ParserRuleContext {
		public List<Book_fieldContext> book_field() {
			return getRuleContexts(Book_fieldContext.class);
		}
		public Book_fieldContext book_field(int i) {
			return getRuleContext(Book_fieldContext.class,i);
		}
		public List<TerminalNode> FS() { return getTokens(Pract3Parser.FS); }
		public TerminalNode FS(int i) {
			return getToken(Pract3Parser.FS, i);
		}
		public Book_fieldsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_book_fields; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterBook_fields(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitBook_fields(this);
		}
	}

	public final Book_fieldsContext book_fields() throws RecognitionException {
		Book_fieldsContext _localctx = new Book_fieldsContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_book_fields);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(147);
			book_field();
			setState(152);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==FS) {
				{
				{
				setState(148);
				match(FS);
				setState(149);
				book_field();
				}
				}
				setState(154);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Book_fieldContext extends ParserRuleContext {
		public Author_fieldContext author_field() {
			return getRuleContext(Author_fieldContext.class,0);
		}
		public Title_fieldContext title_field() {
			return getRuleContext(Title_fieldContext.class,0);
		}
		public Year_fieldContext year_field() {
			return getRuleContext(Year_fieldContext.class,0);
		}
		public Publisher_fieldContext publisher_field() {
			return getRuleContext(Publisher_fieldContext.class,0);
		}
		public Ig_fieldContext ig_field() {
			return getRuleContext(Ig_fieldContext.class,0);
		}
		public Book_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_book_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterBook_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitBook_field(this);
		}
	}

	public final Book_fieldContext book_field() throws RecognitionException {
		Book_fieldContext _localctx = new Book_fieldContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_book_field);
		try {
			setState(160);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(155);
				author_field();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(156);
				title_field();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(157);
				year_field();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(158);
				publisher_field();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(159);
				ig_field();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Article_type_valueContext extends ParserRuleContext {
		public Token l;
		public TerminalNode LB() { return getToken(Pract3Parser.LB, 0); }
		public TerminalNode FS() { return getToken(Pract3Parser.FS, 0); }
		public Article_fieldsContext article_fields() {
			return getRuleContext(Article_fieldsContext.class,0);
		}
		public TerminalNode RB() { return getToken(Pract3Parser.RB, 0); }
		public TerminalNode WORD() { return getToken(Pract3Parser.WORD, 0); }
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Article_type_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_article_type_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterArticle_type_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitArticle_type_value(this);
		}
	}

	public final Article_type_valueContext article_type_value() throws RecognitionException {
		Article_type_valueContext _localctx = new Article_type_valueContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_article_type_value);
		try {
			setState(176);
			switch (_input.LA(1)) {
			case LB:
				enterOuterAlt(_localctx, 1);
				{
				setState(162);
				match(LB);
				setState(163);
				((Article_type_valueContext)_localctx).l = match(WORD);
				setLabel(); printLabel((((Article_type_valueContext)_localctx).l!=null?((Article_type_valueContext)_localctx).l.getText():null));
				setState(165);
				match(FS);
				setState(166);
				article_fields();
				setState(167);
				match(RB);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(169);
				match(LCB);
				setState(170);
				((Article_type_valueContext)_localctx).l = match(WORD);
				setLabel(); printLabel((((Article_type_valueContext)_localctx).l!=null?((Article_type_valueContext)_localctx).l.getText():null));
				setState(172);
				match(FS);
				setState(173);
				article_fields();
				setState(174);
				match(RCB);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Article_fieldsContext extends ParserRuleContext {
		public List<Article_fieldContext> article_field() {
			return getRuleContexts(Article_fieldContext.class);
		}
		public Article_fieldContext article_field(int i) {
			return getRuleContext(Article_fieldContext.class,i);
		}
		public List<TerminalNode> FS() { return getTokens(Pract3Parser.FS); }
		public TerminalNode FS(int i) {
			return getToken(Pract3Parser.FS, i);
		}
		public Article_fieldsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_article_fields; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterArticle_fields(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitArticle_fields(this);
		}
	}

	public final Article_fieldsContext article_fields() throws RecognitionException {
		Article_fieldsContext _localctx = new Article_fieldsContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_article_fields);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(178);
			article_field();
			setState(183);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==FS) {
				{
				{
				setState(179);
				match(FS);
				setState(180);
				article_field();
				}
				}
				setState(185);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Article_fieldContext extends ParserRuleContext {
		public Author_fieldContext author_field() {
			return getRuleContext(Author_fieldContext.class,0);
		}
		public Title_fieldContext title_field() {
			return getRuleContext(Title_fieldContext.class,0);
		}
		public Journal_fieldContext journal_field() {
			return getRuleContext(Journal_fieldContext.class,0);
		}
		public Pages_fieldContext pages_field() {
			return getRuleContext(Pages_fieldContext.class,0);
		}
		public Volume_fieldContext volume_field() {
			return getRuleContext(Volume_fieldContext.class,0);
		}
		public Number_fieldContext number_field() {
			return getRuleContext(Number_fieldContext.class,0);
		}
		public Year_fieldContext year_field() {
			return getRuleContext(Year_fieldContext.class,0);
		}
		public Ig_fieldContext ig_field() {
			return getRuleContext(Ig_fieldContext.class,0);
		}
		public Article_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_article_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterArticle_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitArticle_field(this);
		}
	}

	public final Article_fieldContext article_field() throws RecognitionException {
		Article_fieldContext _localctx = new Article_fieldContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_article_field);
		try {
			setState(194);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(186);
				author_field();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(187);
				title_field();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(188);
				journal_field();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(189);
				pages_field();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(190);
				volume_field();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(191);
				number_field();
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(192);
				year_field();
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				setState(193);
				ig_field();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Inproceedings_type_valueContext extends ParserRuleContext {
		public Token l;
		public TerminalNode LB() { return getToken(Pract3Parser.LB, 0); }
		public TerminalNode FS() { return getToken(Pract3Parser.FS, 0); }
		public Inproceedings_fieldsContext inproceedings_fields() {
			return getRuleContext(Inproceedings_fieldsContext.class,0);
		}
		public TerminalNode RB() { return getToken(Pract3Parser.RB, 0); }
		public TerminalNode WORD() { return getToken(Pract3Parser.WORD, 0); }
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Inproceedings_type_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_inproceedings_type_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterInproceedings_type_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitInproceedings_type_value(this);
		}
	}

	public final Inproceedings_type_valueContext inproceedings_type_value() throws RecognitionException {
		Inproceedings_type_valueContext _localctx = new Inproceedings_type_valueContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_inproceedings_type_value);
		try {
			setState(210);
			switch (_input.LA(1)) {
			case LB:
				enterOuterAlt(_localctx, 1);
				{
				setState(196);
				match(LB);
				setState(197);
				((Inproceedings_type_valueContext)_localctx).l = match(WORD);
				setLabel(); printLabel((((Inproceedings_type_valueContext)_localctx).l!=null?((Inproceedings_type_valueContext)_localctx).l.getText():null));
				setState(199);
				match(FS);
				setState(200);
				inproceedings_fields();
				setState(201);
				match(RB);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(203);
				match(LCB);
				setState(204);
				((Inproceedings_type_valueContext)_localctx).l = match(WORD);
				setLabel(); printLabel((((Inproceedings_type_valueContext)_localctx).l!=null?((Inproceedings_type_valueContext)_localctx).l.getText():null));
				setState(206);
				match(FS);
				setState(207);
				inproceedings_fields();
				setState(208);
				match(RCB);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Inproceedings_fieldsContext extends ParserRuleContext {
		public List<Inproceedings_fieldContext> inproceedings_field() {
			return getRuleContexts(Inproceedings_fieldContext.class);
		}
		public Inproceedings_fieldContext inproceedings_field(int i) {
			return getRuleContext(Inproceedings_fieldContext.class,i);
		}
		public List<TerminalNode> FS() { return getTokens(Pract3Parser.FS); }
		public TerminalNode FS(int i) {
			return getToken(Pract3Parser.FS, i);
		}
		public Inproceedings_fieldsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_inproceedings_fields; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterInproceedings_fields(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitInproceedings_fields(this);
		}
	}

	public final Inproceedings_fieldsContext inproceedings_fields() throws RecognitionException {
		Inproceedings_fieldsContext _localctx = new Inproceedings_fieldsContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_inproceedings_fields);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(212);
			inproceedings_field();
			setState(217);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==FS) {
				{
				{
				setState(213);
				match(FS);
				setState(214);
				inproceedings_field();
				}
				}
				setState(219);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Inproceedings_fieldContext extends ParserRuleContext {
		public Author_fieldContext author_field() {
			return getRuleContext(Author_fieldContext.class,0);
		}
		public Title_fieldContext title_field() {
			return getRuleContext(Title_fieldContext.class,0);
		}
		public Booktitle_fieldContext booktitle_field() {
			return getRuleContext(Booktitle_fieldContext.class,0);
		}
		public Year_fieldContext year_field() {
			return getRuleContext(Year_fieldContext.class,0);
		}
		public Month_fieldContext month_field() {
			return getRuleContext(Month_fieldContext.class,0);
		}
		public Pages_fieldContext pages_field() {
			return getRuleContext(Pages_fieldContext.class,0);
		}
		public Ig_fieldContext ig_field() {
			return getRuleContext(Ig_fieldContext.class,0);
		}
		public Inproceedings_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_inproceedings_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterInproceedings_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitInproceedings_field(this);
		}
	}

	public final Inproceedings_fieldContext inproceedings_field() throws RecognitionException {
		Inproceedings_fieldContext _localctx = new Inproceedings_fieldContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_inproceedings_field);
		try {
			setState(227);
			switch ( getInterpreter().adaptivePredict(_input,12,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(220);
				author_field();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(221);
				title_field();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(222);
				booktitle_field();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(223);
				year_field();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(224);
				month_field();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(225);
				pages_field();
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(226);
				ig_field();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Ig_type_valueContext extends ParserRuleContext {
		public TerminalNode LB() { return getToken(Pract3Parser.LB, 0); }
		public TerminalNode WORD() { return getToken(Pract3Parser.WORD, 0); }
		public TerminalNode FS() { return getToken(Pract3Parser.FS, 0); }
		public Ig_fieldsContext ig_fields() {
			return getRuleContext(Ig_fieldsContext.class,0);
		}
		public TerminalNode RB() { return getToken(Pract3Parser.RB, 0); }
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Ig_type_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ig_type_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterIg_type_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitIg_type_value(this);
		}
	}

	public final Ig_type_valueContext ig_type_value() throws RecognitionException {
		Ig_type_valueContext _localctx = new Ig_type_valueContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_ig_type_value);
		try {
			setState(241);
			switch (_input.LA(1)) {
			case LB:
				enterOuterAlt(_localctx, 1);
				{
				setState(229);
				match(LB);
				setState(230);
				match(WORD);
				setState(231);
				match(FS);
				setState(232);
				ig_fields();
				setState(233);
				match(RB);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(235);
				match(LCB);
				setState(236);
				match(WORD);
				setState(237);
				match(FS);
				setState(238);
				ig_fields();
				setState(239);
				match(RCB);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Ig_fieldsContext extends ParserRuleContext {
		public List<Ig_fieldContext> ig_field() {
			return getRuleContexts(Ig_fieldContext.class);
		}
		public Ig_fieldContext ig_field(int i) {
			return getRuleContext(Ig_fieldContext.class,i);
		}
		public List<TerminalNode> FS() { return getTokens(Pract3Parser.FS); }
		public TerminalNode FS(int i) {
			return getToken(Pract3Parser.FS, i);
		}
		public Ig_fieldsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ig_fields; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterIg_fields(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitIg_fields(this);
		}
	}

	public final Ig_fieldsContext ig_fields() throws RecognitionException {
		Ig_fieldsContext _localctx = new Ig_fieldsContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_ig_fields);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(243);
			ig_field();
			setState(248);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==FS) {
				{
				{
				setState(244);
				match(FS);
				setState(245);
				ig_field();
				}
				}
				setState(250);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Ig_fieldContext extends ParserRuleContext {
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Any_valueContext any_value() {
			return getRuleContext(Any_valueContext.class,0);
		}
		public TerminalNode AUTHOR_KEY() { return getToken(Pract3Parser.AUTHOR_KEY, 0); }
		public TerminalNode TITLE_KEY() { return getToken(Pract3Parser.TITLE_KEY, 0); }
		public TerminalNode PUBLISHER_KEY() { return getToken(Pract3Parser.PUBLISHER_KEY, 0); }
		public TerminalNode JOURNAL_KEY() { return getToken(Pract3Parser.JOURNAL_KEY, 0); }
		public List<TerminalNode> PAGES_KEY() { return getTokens(Pract3Parser.PAGES_KEY); }
		public TerminalNode PAGES_KEY(int i) {
			return getToken(Pract3Parser.PAGES_KEY, i);
		}
		public TerminalNode VOLUME_KEY() { return getToken(Pract3Parser.VOLUME_KEY, 0); }
		public TerminalNode NUMBER_KEY() { return getToken(Pract3Parser.NUMBER_KEY, 0); }
		public TerminalNode YEAR_KEY() { return getToken(Pract3Parser.YEAR_KEY, 0); }
		public TerminalNode MONTH_KEY() { return getToken(Pract3Parser.MONTH_KEY, 0); }
		public TerminalNode ISSN_KEY() { return getToken(Pract3Parser.ISSN_KEY, 0); }
		public TerminalNode DOI_KEY() { return getToken(Pract3Parser.DOI_KEY, 0); }
		public TerminalNode ADDRESS_KEY() { return getToken(Pract3Parser.ADDRESS_KEY, 0); }
		public TerminalNode URL_KEY() { return getToken(Pract3Parser.URL_KEY, 0); }
		public TerminalNode BOOKTITLE_KEY() { return getToken(Pract3Parser.BOOKTITLE_KEY, 0); }
		public Ig_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ig_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterIg_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitIg_field(this);
		}
	}

	public final Ig_fieldContext ig_field() throws RecognitionException {
		Ig_fieldContext _localctx = new Ig_fieldContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_ig_field);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(251);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << AUTHOR_KEY) | (1L << TITLE_KEY) | (1L << YEAR_KEY) | (1L << PUBLISHER_KEY) | (1L << JOURNAL_KEY) | (1L << PAGES_KEY) | (1L << VOLUME_KEY) | (1L << NUMBER_KEY) | (1L << MONTH_KEY) | (1L << ISSN_KEY) | (1L << DOI_KEY) | (1L << ADDRESS_KEY) | (1L << URL_KEY) | (1L << BOOKTITLE_KEY))) != 0)) ) {
			_errHandler.recoverInline(this);
			} else {
				consume();
			}
			setState(252);
			match(EQ);
			setState(253);
			any_value();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Author_fieldContext extends ParserRuleContext {
		public Text_valueContext text_value;
		public TerminalNode AUTHOR_KEY() { return getToken(Pract3Parser.AUTHOR_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Author_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_author_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterAuthor_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitAuthor_field(this);
		}
	}

	public final Author_fieldContext author_field() throws RecognitionException {
		Author_fieldContext _localctx = new Author_fieldContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_author_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(255);
			match(AUTHOR_KEY);
			setState(256);
			match(EQ);
			setState(257);
			((Author_fieldContext)_localctx).text_value = text_value();
			setAuthor();    printAuthors(((Author_fieldContext)_localctx).text_value.text);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Title_fieldContext extends ParserRuleContext {
		public Text_valueContext text_value;
		public TerminalNode TITLE_KEY() { return getToken(Pract3Parser.TITLE_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Title_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_title_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterTitle_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitTitle_field(this);
		}
	}

	public final Title_fieldContext title_field() throws RecognitionException {
		Title_fieldContext _localctx = new Title_fieldContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_title_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(260);
			match(TITLE_KEY);
			setState(261);
			match(EQ);
			setState(262);
			((Title_fieldContext)_localctx).text_value = text_value();
			setTitle();     printTitle(((Title_fieldContext)_localctx).text_value.text);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Publisher_fieldContext extends ParserRuleContext {
		public Text_valueContext text_value;
		public TerminalNode PUBLISHER_KEY() { return getToken(Pract3Parser.PUBLISHER_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Publisher_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_publisher_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterPublisher_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitPublisher_field(this);
		}
	}

	public final Publisher_fieldContext publisher_field() throws RecognitionException {
		Publisher_fieldContext _localctx = new Publisher_fieldContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_publisher_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(265);
			match(PUBLISHER_KEY);
			setState(266);
			match(EQ);
			setState(267);
			((Publisher_fieldContext)_localctx).text_value = text_value();
			setPublisher(); printPublisher(((Publisher_fieldContext)_localctx).text_value.text);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Pages_fieldContext extends ParserRuleContext {
		public Numeric_rangeContext numeric_range;
		public TerminalNode PAGES_KEY() { return getToken(Pract3Parser.PAGES_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Numeric_rangeContext numeric_range() {
			return getRuleContext(Numeric_rangeContext.class,0);
		}
		public Pages_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_pages_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterPages_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitPages_field(this);
		}
	}

	public final Pages_fieldContext pages_field() throws RecognitionException {
		Pages_fieldContext _localctx = new Pages_fieldContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_pages_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(270);
			match(PAGES_KEY);
			setState(271);
			match(EQ);
			setState(272);
			((Pages_fieldContext)_localctx).numeric_range = numeric_range();
			setPages();     printPages(((Pages_fieldContext)_localctx).numeric_range.begin, ((Pages_fieldContext)_localctx).numeric_range.end);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Volume_fieldContext extends ParserRuleContext {
		public Numeric_valueContext numeric_value;
		public TerminalNode VOLUME_KEY() { return getToken(Pract3Parser.VOLUME_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Numeric_valueContext numeric_value() {
			return getRuleContext(Numeric_valueContext.class,0);
		}
		public Volume_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_volume_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterVolume_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitVolume_field(this);
		}
	}

	public final Volume_fieldContext volume_field() throws RecognitionException {
		Volume_fieldContext _localctx = new Volume_fieldContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_volume_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(275);
			match(VOLUME_KEY);
			setState(276);
			match(EQ);
			setState(277);
			((Volume_fieldContext)_localctx).numeric_value = numeric_value();
			setVolume();    printVolume(((Volume_fieldContext)_localctx).numeric_value.number);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Number_fieldContext extends ParserRuleContext {
		public Numeric_valueContext numeric_value;
		public TerminalNode NUMBER_KEY() { return getToken(Pract3Parser.NUMBER_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Numeric_valueContext numeric_value() {
			return getRuleContext(Numeric_valueContext.class,0);
		}
		public Number_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_number_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterNumber_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitNumber_field(this);
		}
	}

	public final Number_fieldContext number_field() throws RecognitionException {
		Number_fieldContext _localctx = new Number_fieldContext(_ctx, getState());
		enterRule(_localctx, 50, RULE_number_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(280);
			match(NUMBER_KEY);
			setState(281);
			match(EQ);
			setState(282);
			((Number_fieldContext)_localctx).numeric_value = numeric_value();
			setNumber();    printNumber(((Number_fieldContext)_localctx).numeric_value.number);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Journal_fieldContext extends ParserRuleContext {
		public TerminalNode JOURNAL_KEY() { return getToken(Pract3Parser.JOURNAL_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Journal_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_journal_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterJournal_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitJournal_field(this);
		}
	}

	public final Journal_fieldContext journal_field() throws RecognitionException {
		Journal_fieldContext _localctx = new Journal_fieldContext(_ctx, getState());
		enterRule(_localctx, 52, RULE_journal_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(285);
			match(JOURNAL_KEY);
			setState(286);
			match(EQ);
			setState(287);
			text_value();
			setJournal();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Booktitle_fieldContext extends ParserRuleContext {
		public TerminalNode BOOKTITLE_KEY() { return getToken(Pract3Parser.BOOKTITLE_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Booktitle_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_booktitle_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterBooktitle_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitBooktitle_field(this);
		}
	}

	public final Booktitle_fieldContext booktitle_field() throws RecognitionException {
		Booktitle_fieldContext _localctx = new Booktitle_fieldContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_booktitle_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(290);
			match(BOOKTITLE_KEY);
			setState(291);
			match(EQ);
			setState(292);
			text_value();
			setBooktitle();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Year_fieldContext extends ParserRuleContext {
		public Numeric_valueContext numeric_value;
		public TerminalNode YEAR_KEY() { return getToken(Pract3Parser.YEAR_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Numeric_valueContext numeric_value() {
			return getRuleContext(Numeric_valueContext.class,0);
		}
		public Year_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_year_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterYear_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitYear_field(this);
		}
	}

	public final Year_fieldContext year_field() throws RecognitionException {
		Year_fieldContext _localctx = new Year_fieldContext(_ctx, getState());
		enterRule(_localctx, 56, RULE_year_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(295);
			match(YEAR_KEY);
			setState(296);
			match(EQ);
			setState(297);
			((Year_fieldContext)_localctx).numeric_value = numeric_value();
			setYear(((Year_fieldContext)_localctx).numeric_value.number);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Month_fieldContext extends ParserRuleContext {
		public Month_valueContext month_value;
		public TerminalNode MONTH_KEY() { return getToken(Pract3Parser.MONTH_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Month_valueContext month_value() {
			return getRuleContext(Month_valueContext.class,0);
		}
		public Month_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_month_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterMonth_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitMonth_field(this);
		}
	}

	public final Month_fieldContext month_field() throws RecognitionException {
		Month_fieldContext _localctx = new Month_fieldContext(_ctx, getState());
		enterRule(_localctx, 58, RULE_month_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(300);
			match(MONTH_KEY);
			setState(301);
			match(EQ);
			setState(302);
			((Month_fieldContext)_localctx).month_value = month_value();
			setMonth(((Month_fieldContext)_localctx).month_value.text);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Issn_fieldContext extends ParserRuleContext {
		public TerminalNode ISSN_KEY() { return getToken(Pract3Parser.ISSN_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Issn_rangeContext issn_range() {
			return getRuleContext(Issn_rangeContext.class,0);
		}
		public Issn_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_issn_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterIssn_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitIssn_field(this);
		}
	}

	public final Issn_fieldContext issn_field() throws RecognitionException {
		Issn_fieldContext _localctx = new Issn_fieldContext(_ctx, getState());
		enterRule(_localctx, 60, RULE_issn_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(305);
			match(ISSN_KEY);
			setState(306);
			match(EQ);
			setState(307);
			issn_range();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Doi_fieldContext extends ParserRuleContext {
		public TerminalNode DOI_KEY() { return getToken(Pract3Parser.DOI_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Doi_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_doi_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterDoi_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitDoi_field(this);
		}
	}

	public final Doi_fieldContext doi_field() throws RecognitionException {
		Doi_fieldContext _localctx = new Doi_fieldContext(_ctx, getState());
		enterRule(_localctx, 62, RULE_doi_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(309);
			match(DOI_KEY);
			setState(310);
			match(EQ);
			setState(311);
			text_value();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Address_fieldContext extends ParserRuleContext {
		public TerminalNode ADDRESS_KEY() { return getToken(Pract3Parser.ADDRESS_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Address_valueContext address_value() {
			return getRuleContext(Address_valueContext.class,0);
		}
		public Address_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_address_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterAddress_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitAddress_field(this);
		}
	}

	public final Address_fieldContext address_field() throws RecognitionException {
		Address_fieldContext _localctx = new Address_fieldContext(_ctx, getState());
		enterRule(_localctx, 64, RULE_address_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(313);
			match(ADDRESS_KEY);
			setState(314);
			match(EQ);
			setState(315);
			address_value();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Url_fieldContext extends ParserRuleContext {
		public TerminalNode URL_KEY() { return getToken(Pract3Parser.URL_KEY, 0); }
		public TerminalNode EQ() { return getToken(Pract3Parser.EQ, 0); }
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Url_fieldContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_url_field; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterUrl_field(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitUrl_field(this);
		}
	}

	public final Url_fieldContext url_field() throws RecognitionException {
		Url_fieldContext _localctx = new Url_fieldContext(_ctx, getState());
		enterRule(_localctx, 66, RULE_url_field);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(317);
			match(URL_KEY);
			setState(318);
			match(EQ);
			setState(319);
			text_value();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Any_valueContext extends ParserRuleContext {
		public Text_valueContext text_value() {
			return getRuleContext(Text_valueContext.class,0);
		}
		public Numeric_valueContext numeric_value() {
			return getRuleContext(Numeric_valueContext.class,0);
		}
		public Month_valueContext month_value() {
			return getRuleContext(Month_valueContext.class,0);
		}
		public Numeric_rangeContext numeric_range() {
			return getRuleContext(Numeric_rangeContext.class,0);
		}
		public Issn_rangeContext issn_range() {
			return getRuleContext(Issn_rangeContext.class,0);
		}
		public Address_valueContext address_value() {
			return getRuleContext(Address_valueContext.class,0);
		}
		public Any_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_any_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterAny_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitAny_value(this);
		}
	}

	public final Any_valueContext any_value() throws RecognitionException {
		Any_valueContext _localctx = new Any_valueContext(_ctx, getState());
		enterRule(_localctx, 68, RULE_any_value);
		try {
			setState(327);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(321);
				text_value();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(322);
				numeric_value();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(323);
				month_value();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(324);
				numeric_range();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(325);
				issn_range();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(326);
				address_value();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Text_valueContext extends ParserRuleContext {
		public String text;
		public StringContext string;
		public List<TerminalNode> QM() { return getTokens(Pract3Parser.QM); }
		public TerminalNode QM(int i) {
			return getToken(Pract3Parser.QM, i);
		}
		public StringContext string() {
			return getRuleContext(StringContext.class,0);
		}
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Text_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_text_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterText_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitText_value(this);
		}
	}

	public final Text_valueContext text_value() throws RecognitionException {
		Text_valueContext _localctx = new Text_valueContext(_ctx, getState());
		enterRule(_localctx, 70, RULE_text_value);
		try {
			setState(339);
			switch (_input.LA(1)) {
			case QM:
				enterOuterAlt(_localctx, 1);
				{
				setState(329);
				match(QM);
				setState(330);
				((Text_valueContext)_localctx).string = string();
				setState(331);
				match(QM);
				((Text_valueContext)_localctx).text =  (((Text_valueContext)_localctx).string!=null?_input.getText(((Text_valueContext)_localctx).string.start,((Text_valueContext)_localctx).string.stop):null);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(334);
				match(LCB);
				setState(335);
				((Text_valueContext)_localctx).string = string();
				setState(336);
				match(RCB);
				((Text_valueContext)_localctx).text =  (((Text_valueContext)_localctx).string!=null?_input.getText(((Text_valueContext)_localctx).string.start,((Text_valueContext)_localctx).string.stop):null);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Numeric_valueContext extends ParserRuleContext {
		public String number;
		public Token NUMBER;
		public List<TerminalNode> QM() { return getTokens(Pract3Parser.QM); }
		public TerminalNode QM(int i) {
			return getToken(Pract3Parser.QM, i);
		}
		public TerminalNode NUMBER() { return getToken(Pract3Parser.NUMBER, 0); }
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Numeric_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_numeric_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterNumeric_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitNumeric_value(this);
		}
	}

	public final Numeric_valueContext numeric_value() throws RecognitionException {
		Numeric_valueContext _localctx = new Numeric_valueContext(_ctx, getState());
		enterRule(_localctx, 72, RULE_numeric_value);
		try {
			setState(351);
			switch (_input.LA(1)) {
			case QM:
				enterOuterAlt(_localctx, 1);
				{
				setState(341);
				match(QM);
				setState(342);
				((Numeric_valueContext)_localctx).NUMBER = match(NUMBER);
				setState(343);
				match(QM);
				((Numeric_valueContext)_localctx).number =  (((Numeric_valueContext)_localctx).NUMBER!=null?((Numeric_valueContext)_localctx).NUMBER.getText():null);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(345);
				match(LCB);
				setState(346);
				((Numeric_valueContext)_localctx).NUMBER = match(NUMBER);
				setState(347);
				match(RCB);
				((Numeric_valueContext)_localctx).number =  (((Numeric_valueContext)_localctx).NUMBER!=null?((Numeric_valueContext)_localctx).NUMBER.getText():null);
				}
				break;
			case NUMBER:
				enterOuterAlt(_localctx, 3);
				{
				setState(349);
				((Numeric_valueContext)_localctx).NUMBER = match(NUMBER);
				((Numeric_valueContext)_localctx).number =  (((Numeric_valueContext)_localctx).NUMBER!=null?((Numeric_valueContext)_localctx).NUMBER.getText():null);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Month_valueContext extends ParserRuleContext {
		public String text;
		public MonthContext month;
		public Token NUMBER;
		public List<TerminalNode> QM() { return getTokens(Pract3Parser.QM); }
		public TerminalNode QM(int i) {
			return getToken(Pract3Parser.QM, i);
		}
		public MonthContext month() {
			return getRuleContext(MonthContext.class,0);
		}
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public TerminalNode NUMBER() { return getToken(Pract3Parser.NUMBER, 0); }
		public Month_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_month_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterMonth_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitMonth_value(this);
		}
	}

	public final Month_valueContext month_value() throws RecognitionException {
		Month_valueContext _localctx = new Month_valueContext(_ctx, getState());
		enterRule(_localctx, 74, RULE_month_value);
		try {
			setState(365);
			switch (_input.LA(1)) {
			case QM:
				enterOuterAlt(_localctx, 1);
				{
				setState(353);
				match(QM);
				setState(354);
				((Month_valueContext)_localctx).month = month();
				setState(355);
				match(QM);
				((Month_valueContext)_localctx).text =  (((Month_valueContext)_localctx).month!=null?_input.getText(((Month_valueContext)_localctx).month.start,((Month_valueContext)_localctx).month.stop):null);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(358);
				match(LCB);
				setState(359);
				((Month_valueContext)_localctx).month = month();
				setState(360);
				match(RCB);
				((Month_valueContext)_localctx).text =  (((Month_valueContext)_localctx).month!=null?_input.getText(((Month_valueContext)_localctx).month.start,((Month_valueContext)_localctx).month.stop):null);
				}
				break;
			case NUMBER:
				enterOuterAlt(_localctx, 3);
				{
				setState(363);
				((Month_valueContext)_localctx).NUMBER = match(NUMBER);
				((Month_valueContext)_localctx).text =  (((Month_valueContext)_localctx).NUMBER!=null?((Month_valueContext)_localctx).NUMBER.getText():null);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MonthContext extends ParserRuleContext {
		public TerminalNode NUMBER() { return getToken(Pract3Parser.NUMBER, 0); }
		public TerminalNode WORD() { return getToken(Pract3Parser.WORD, 0); }
		public MonthContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_month; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterMonth(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitMonth(this);
		}
	}

	public final MonthContext month() throws RecognitionException {
		MonthContext _localctx = new MonthContext(_ctx, getState());
		enterRule(_localctx, 76, RULE_month);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(367);
			_la = _input.LA(1);
			if ( !(_la==NUMBER || _la==WORD) ) {
			_errHandler.recoverInline(this);
			} else {
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Numeric_rangeContext extends ParserRuleContext {
		public String begin;
		public String end;
		public Token l;
		public Token r;
		public List<TerminalNode> QM() { return getTokens(Pract3Parser.QM); }
		public TerminalNode QM(int i) {
			return getToken(Pract3Parser.QM, i);
		}
		public List<TerminalNode> RS() { return getTokens(Pract3Parser.RS); }
		public TerminalNode RS(int i) {
			return getToken(Pract3Parser.RS, i);
		}
		public List<TerminalNode> NUMBER() { return getTokens(Pract3Parser.NUMBER); }
		public TerminalNode NUMBER(int i) {
			return getToken(Pract3Parser.NUMBER, i);
		}
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Numeric_rangeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_numeric_range; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterNumeric_range(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitNumeric_range(this);
		}
	}

	public final Numeric_rangeContext numeric_range() throws RecognitionException {
		Numeric_rangeContext _localctx = new Numeric_rangeContext(_ctx, getState());
		enterRule(_localctx, 78, RULE_numeric_range);
		try {
			setState(383);
			switch (_input.LA(1)) {
			case QM:
				enterOuterAlt(_localctx, 1);
				{
				setState(369);
				match(QM);
				setState(370);
				((Numeric_rangeContext)_localctx).l = match(NUMBER);
				setState(371);
				match(RS);
				setState(372);
				match(RS);
				setState(373);
				((Numeric_rangeContext)_localctx).r = match(NUMBER);
				setState(374);
				match(QM);
				((Numeric_rangeContext)_localctx).begin =  (((Numeric_rangeContext)_localctx).l!=null?((Numeric_rangeContext)_localctx).l.getText():null); ((Numeric_rangeContext)_localctx).end =  (((Numeric_rangeContext)_localctx).r!=null?((Numeric_rangeContext)_localctx).r.getText():null);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(376);
				match(LCB);
				setState(377);
				((Numeric_rangeContext)_localctx).l = match(NUMBER);
				setState(378);
				match(RS);
				setState(379);
				match(RS);
				setState(380);
				((Numeric_rangeContext)_localctx).r = match(NUMBER);
				setState(381);
				match(RCB);
				((Numeric_rangeContext)_localctx).begin =  (((Numeric_rangeContext)_localctx).l!=null?((Numeric_rangeContext)_localctx).l.getText():null); ((Numeric_rangeContext)_localctx).end =  (((Numeric_rangeContext)_localctx).r!=null?((Numeric_rangeContext)_localctx).r.getText():null);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Issn_rangeContext extends ParserRuleContext {
		public String begin;
		public String end;
		public Token l;
		public Token r;
		public List<TerminalNode> QM() { return getTokens(Pract3Parser.QM); }
		public TerminalNode QM(int i) {
			return getToken(Pract3Parser.QM, i);
		}
		public TerminalNode RS() { return getToken(Pract3Parser.RS, 0); }
		public List<TerminalNode> NUMBER() { return getTokens(Pract3Parser.NUMBER); }
		public TerminalNode NUMBER(int i) {
			return getToken(Pract3Parser.NUMBER, i);
		}
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Issn_rangeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_issn_range; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterIssn_range(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitIssn_range(this);
		}
	}

	public final Issn_rangeContext issn_range() throws RecognitionException {
		Issn_rangeContext _localctx = new Issn_rangeContext(_ctx, getState());
		enterRule(_localctx, 80, RULE_issn_range);
		try {
			setState(397);
			switch (_input.LA(1)) {
			case QM:
				enterOuterAlt(_localctx, 1);
				{
				setState(385);
				match(QM);
				setState(386);
				((Issn_rangeContext)_localctx).l = match(NUMBER);
				setState(387);
				match(RS);
				setState(388);
				((Issn_rangeContext)_localctx).r = match(NUMBER);
				setState(389);
				match(QM);
				((Issn_rangeContext)_localctx).begin =  (((Issn_rangeContext)_localctx).l!=null?((Issn_rangeContext)_localctx).l.getText():null); ((Issn_rangeContext)_localctx).end =  (((Issn_rangeContext)_localctx).r!=null?((Issn_rangeContext)_localctx).r.getText():null);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(391);
				match(LCB);
				setState(392);
				((Issn_rangeContext)_localctx).l = match(NUMBER);
				setState(393);
				match(RS);
				setState(394);
				((Issn_rangeContext)_localctx).r = match(NUMBER);
				setState(395);
				match(RCB);
				((Issn_rangeContext)_localctx).begin =  (((Issn_rangeContext)_localctx).l!=null?((Issn_rangeContext)_localctx).l.getText():null); ((Issn_rangeContext)_localctx).end =  (((Issn_rangeContext)_localctx).r!=null?((Issn_rangeContext)_localctx).r.getText():null);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Address_valueContext extends ParserRuleContext {
		public String val;
		public AddressContext address;
		public List<TerminalNode> QM() { return getTokens(Pract3Parser.QM); }
		public TerminalNode QM(int i) {
			return getToken(Pract3Parser.QM, i);
		}
		public AddressContext address() {
			return getRuleContext(AddressContext.class,0);
		}
		public TerminalNode LCB() { return getToken(Pract3Parser.LCB, 0); }
		public TerminalNode RCB() { return getToken(Pract3Parser.RCB, 0); }
		public Address_valueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_address_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).enterAddress_value(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof Pract3Listener ) ((Pract3Listener)listener).exitAddress_value(this);
		}
	}

	public final Address_valueContext address_value() throws RecognitionException {
		Address_valueContext _localctx = new Address_valueContext(_ctx, getState());
		enterRule(_localctx, 82, RULE_address_value);
		try {
			setState(409);
			switch (_input.LA(1)) {
			case QM:
				enterOuterAlt(_localctx, 1);
				{
				setState(399);
				match(QM);
				setState(400);
				((Address_valueContext)_localctx).address = address();
				setState(401);
				match(QM);
				((Address_valueContext)_localctx).val =  (((Address_valueContext)_localctx).address!=null?_input.getText(((Address_valueContext)_localctx).address.start,((Address_valueContext)_localctx).address.stop):null);
				}
				break;
			case LCB:
				enterOuterAlt(_localctx, 2);
				{
				setState(404);
				match(LCB);
				setState(405);
				((Address_valueContext)_localctx).address = address();
				setState(406);
				match(RCB);
				((Address_valueContext)_localctx).val =  (((Address_valueContext)_localctx).address!=null?_input.getText(((Address_valueContext)_localctx).address.start,((Address_valueContext)_localctx).address.stop):null);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3\37\u019e\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\3"+
		"\2\7\2X\n\2\f\2\16\2[\13\2\3\2\3\2\3\3\3\3\7\3a\n\3\f\3\16\3d\13\3\3\4"+
		"\3\4\3\4\7\4i\n\4\f\4\16\4l\13\4\3\5\3\5\3\5\3\5\5\5r\n\5\3\6\3\6\3\6"+
		"\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\n\3\n\3"+
		"\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\5\n\u0094\n\n\3\13\3\13"+
		"\3\13\7\13\u0099\n\13\f\13\16\13\u009c\13\13\3\f\3\f\3\f\3\f\3\f\5\f\u00a3"+
		"\n\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u00b3"+
		"\n\r\3\16\3\16\3\16\7\16\u00b8\n\16\f\16\16\16\u00bb\13\16\3\17\3\17\3"+
		"\17\3\17\3\17\3\17\3\17\3\17\5\17\u00c5\n\17\3\20\3\20\3\20\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\5\20\u00d5\n\20\3\21\3\21"+
		"\3\21\7\21\u00da\n\21\f\21\16\21\u00dd\13\21\3\22\3\22\3\22\3\22\3\22"+
		"\3\22\3\22\5\22\u00e6\n\22\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\23"+
		"\3\23\3\23\3\23\5\23\u00f4\n\23\3\24\3\24\3\24\7\24\u00f9\n\24\f\24\16"+
		"\24\u00fc\13\24\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\26\3\26\3\27\3\27"+
		"\3\27\3\27\3\27\3\30\3\30\3\30\3\30\3\30\3\31\3\31\3\31\3\31\3\31\3\32"+
		"\3\32\3\32\3\32\3\32\3\33\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\34"+
		"\3\35\3\35\3\35\3\35\3\35\3\36\3\36\3\36\3\36\3\36\3\37\3\37\3\37\3\37"+
		"\3\37\3 \3 \3 \3 \3!\3!\3!\3!\3\"\3\"\3\"\3\"\3#\3#\3#\3#\3$\3$\3$\3$"+
		"\3$\3$\5$\u014a\n$\3%\3%\3%\3%\3%\3%\3%\3%\3%\3%\5%\u0156\n%\3&\3&\3&"+
		"\3&\3&\3&\3&\3&\3&\3&\5&\u0162\n&\3\'\3\'\3\'\3\'\3\'\3\'\3\'\3\'\3\'"+
		"\3\'\3\'\3\'\5\'\u0170\n\'\3(\3(\3)\3)\3)\3)\3)\3)\3)\3)\3)\3)\3)\3)\3"+
		")\3)\5)\u0182\n)\3*\3*\3*\3*\3*\3*\3*\3*\3*\3*\3*\3*\5*\u0190\n*\3+\3"+
		"+\3+\3+\3+\3+\3+\3+\3+\3+\5+\u019c\n+\3+\2\2,\2\4\6\b\n\f\16\20\22\24"+
		"\26\30\32\34\36 \"$&(*,.\60\62\64\668:<>@BDFHJLNPRT\2\4\3\2\b\25\3\2\36"+
		"\37\u019f\2Y\3\2\2\2\4^\3\2\2\2\6e\3\2\2\2\bq\3\2\2\2\ns\3\2\2\2\fx\3"+
		"\2\2\2\16}\3\2\2\2\20\u0082\3\2\2\2\22\u0093\3\2\2\2\24\u0095\3\2\2\2"+
		"\26\u00a2\3\2\2\2\30\u00b2\3\2\2\2\32\u00b4\3\2\2\2\34\u00c4\3\2\2\2\36"+
		"\u00d4\3\2\2\2 \u00d6\3\2\2\2\"\u00e5\3\2\2\2$\u00f3\3\2\2\2&\u00f5\3"+
		"\2\2\2(\u00fd\3\2\2\2*\u0101\3\2\2\2,\u0106\3\2\2\2.\u010b\3\2\2\2\60"+
		"\u0110\3\2\2\2\62\u0115\3\2\2\2\64\u011a\3\2\2\2\66\u011f\3\2\2\28\u0124"+
		"\3\2\2\2:\u0129\3\2\2\2<\u012e\3\2\2\2>\u0133\3\2\2\2@\u0137\3\2\2\2B"+
		"\u013b\3\2\2\2D\u013f\3\2\2\2F\u0149\3\2\2\2H\u0155\3\2\2\2J\u0161\3\2"+
		"\2\2L\u016f\3\2\2\2N\u0171\3\2\2\2P\u0181\3\2\2\2R\u018f\3\2\2\2T\u019b"+
		"\3\2\2\2VX\5\b\5\2WV\3\2\2\2X[\3\2\2\2YW\3\2\2\2YZ\3\2\2\2Z\\\3\2\2\2"+
		"[Y\3\2\2\2\\]\7\2\2\3]\3\3\2\2\2^b\7\37\2\2_a\7\37\2\2`_\3\2\2\2ad\3\2"+
		"\2\2b`\3\2\2\2bc\3\2\2\2c\5\3\2\2\2db\3\2\2\2ej\5\4\3\2fg\7\26\2\2gi\5"+
		"\4\3\2hf\3\2\2\2il\3\2\2\2jh\3\2\2\2jk\3\2\2\2k\7\3\2\2\2lj\3\2\2\2mr"+
		"\5\n\6\2nr\5\f\7\2or\5\16\b\2pr\5\20\t\2qm\3\2\2\2qn\3\2\2\2qo\3\2\2\2"+
		"qp\3\2\2\2r\t\3\2\2\2st\b\6\1\2tu\7\4\2\2uv\5\22\n\2vw\b\6\1\2w\13\3\2"+
		"\2\2xy\b\7\1\2yz\7\5\2\2z{\5\30\r\2{|\b\7\1\2|\r\3\2\2\2}~\b\b\1\2~\177"+
		"\7\6\2\2\177\u0080\5\36\20\2\u0080\u0081\b\b\1\2\u0081\17\3\2\2\2\u0082"+
		"\u0083\7\7\2\2\u0083\u0084\5$\23\2\u0084\21\3\2\2\2\u0085\u0086\7\32\2"+
		"\2\u0086\u0087\7\37\2\2\u0087\u0088\b\n\1\2\u0088\u0089\7\26\2\2\u0089"+
		"\u008a\5\24\13\2\u008a\u008b\7\33\2\2\u008b\u0094\3\2\2\2\u008c\u008d"+
		"\7\34\2\2\u008d\u008e\7\37\2\2\u008e\u008f\b\n\1\2\u008f\u0090\7\26\2"+
		"\2\u0090\u0091\5\24\13\2\u0091\u0092\7\35\2\2\u0092\u0094\3\2\2\2\u0093"+
		"\u0085\3\2\2\2\u0093\u008c\3\2\2\2\u0094\23\3\2\2\2\u0095\u009a\5\26\f"+
		"\2\u0096\u0097\7\26\2\2\u0097\u0099\5\26\f\2\u0098\u0096\3\2\2\2\u0099"+
		"\u009c\3\2\2\2\u009a\u0098\3\2\2\2\u009a\u009b\3\2\2\2\u009b\25\3\2\2"+
		"\2\u009c\u009a\3\2\2\2\u009d\u00a3\5*\26\2\u009e\u00a3\5,\27\2\u009f\u00a3"+
		"\5:\36\2\u00a0\u00a3\5.\30\2\u00a1\u00a3\5(\25\2\u00a2\u009d\3\2\2\2\u00a2"+
		"\u009e\3\2\2\2\u00a2\u009f\3\2\2\2\u00a2\u00a0\3\2\2\2\u00a2\u00a1\3\2"+
		"\2\2\u00a3\27\3\2\2\2\u00a4\u00a5\7\32\2\2\u00a5\u00a6\7\37\2\2\u00a6"+
		"\u00a7\b\r\1\2\u00a7\u00a8\7\26\2\2\u00a8\u00a9\5\32\16\2\u00a9\u00aa"+
		"\7\33\2\2\u00aa\u00b3\3\2\2\2\u00ab\u00ac\7\34\2\2\u00ac\u00ad\7\37\2"+
		"\2\u00ad\u00ae\b\r\1\2\u00ae\u00af\7\26\2\2\u00af\u00b0\5\32\16\2\u00b0"+
		"\u00b1\7\35\2\2\u00b1\u00b3\3\2\2\2\u00b2\u00a4\3\2\2\2\u00b2\u00ab\3"+
		"\2\2\2\u00b3\31\3\2\2\2\u00b4\u00b9\5\34\17\2\u00b5\u00b6\7\26\2\2\u00b6"+
		"\u00b8\5\34\17\2\u00b7\u00b5\3\2\2\2\u00b8\u00bb\3\2\2\2\u00b9\u00b7\3"+
		"\2\2\2\u00b9\u00ba\3\2\2\2\u00ba\33\3\2\2\2\u00bb\u00b9\3\2\2\2\u00bc"+
		"\u00c5\5*\26\2\u00bd\u00c5\5,\27\2\u00be\u00c5\5\66\34\2\u00bf\u00c5\5"+
		"\60\31\2\u00c0\u00c5\5\62\32\2\u00c1\u00c5\5\64\33\2\u00c2\u00c5\5:\36"+
		"\2\u00c3\u00c5\5(\25\2\u00c4\u00bc\3\2\2\2\u00c4\u00bd\3\2\2\2\u00c4\u00be"+
		"\3\2\2\2\u00c4\u00bf\3\2\2\2\u00c4\u00c0\3\2\2\2\u00c4\u00c1\3\2\2\2\u00c4"+
		"\u00c2\3\2\2\2\u00c4\u00c3\3\2\2\2\u00c5\35\3\2\2\2\u00c6\u00c7\7\32\2"+
		"\2\u00c7\u00c8\7\37\2\2\u00c8\u00c9\b\20\1\2\u00c9\u00ca\7\26\2\2\u00ca"+
		"\u00cb\5 \21\2\u00cb\u00cc\7\33\2\2\u00cc\u00d5\3\2\2\2\u00cd\u00ce\7"+
		"\34\2\2\u00ce\u00cf\7\37\2\2\u00cf\u00d0\b\20\1\2\u00d0\u00d1\7\26\2\2"+
		"\u00d1\u00d2\5 \21\2\u00d2\u00d3\7\35\2\2\u00d3\u00d5\3\2\2\2\u00d4\u00c6"+
		"\3\2\2\2\u00d4\u00cd\3\2\2\2\u00d5\37\3\2\2\2\u00d6\u00db\5\"\22\2\u00d7"+
		"\u00d8\7\26\2\2\u00d8\u00da\5\"\22\2\u00d9\u00d7\3\2\2\2\u00da\u00dd\3"+
		"\2\2\2\u00db\u00d9\3\2\2\2\u00db\u00dc\3\2\2\2\u00dc!\3\2\2\2\u00dd\u00db"+
		"\3\2\2\2\u00de\u00e6\5*\26\2\u00df\u00e6\5,\27\2\u00e0\u00e6\58\35\2\u00e1"+
		"\u00e6\5:\36\2\u00e2\u00e6\5<\37\2\u00e3\u00e6\5\60\31\2\u00e4\u00e6\5"+
		"(\25\2\u00e5\u00de\3\2\2\2\u00e5\u00df\3\2\2\2\u00e5\u00e0\3\2\2\2\u00e5"+
		"\u00e1\3\2\2\2\u00e5\u00e2\3\2\2\2\u00e5\u00e3\3\2\2\2\u00e5\u00e4\3\2"+
		"\2\2\u00e6#\3\2\2\2\u00e7\u00e8\7\32\2\2\u00e8\u00e9\7\37\2\2\u00e9\u00ea"+
		"\7\26\2\2\u00ea\u00eb\5&\24\2\u00eb\u00ec\7\33\2\2\u00ec\u00f4\3\2\2\2"+
		"\u00ed\u00ee\7\34\2\2\u00ee\u00ef\7\37\2\2\u00ef\u00f0\7\26\2\2\u00f0"+
		"\u00f1\5&\24\2\u00f1\u00f2\7\35\2\2\u00f2\u00f4\3\2\2\2\u00f3\u00e7\3"+
		"\2\2\2\u00f3\u00ed\3\2\2\2\u00f4%\3\2\2\2\u00f5\u00fa\5(\25\2\u00f6\u00f7"+
		"\7\26\2\2\u00f7\u00f9\5(\25\2\u00f8\u00f6\3\2\2\2\u00f9\u00fc\3\2\2\2"+
		"\u00fa\u00f8\3\2\2\2\u00fa\u00fb\3\2\2\2\u00fb\'\3\2\2\2\u00fc\u00fa\3"+
		"\2\2\2\u00fd\u00fe\t\2\2\2\u00fe\u00ff\7\30\2\2\u00ff\u0100\5F$\2\u0100"+
		")\3\2\2\2\u0101\u0102\7\b\2\2\u0102\u0103\7\30\2\2\u0103\u0104\5H%\2\u0104"+
		"\u0105\b\26\1\2\u0105+\3\2\2\2\u0106\u0107\7\t\2\2\u0107\u0108\7\30\2"+
		"\2\u0108\u0109\5H%\2\u0109\u010a\b\27\1\2\u010a-\3\2\2\2\u010b\u010c\7"+
		"\13\2\2\u010c\u010d\7\30\2\2\u010d\u010e\5H%\2\u010e\u010f\b\30\1\2\u010f"+
		"/\3\2\2\2\u0110\u0111\7\r\2\2\u0111\u0112\7\30\2\2\u0112\u0113\5P)\2\u0113"+
		"\u0114\b\31\1\2\u0114\61\3\2\2\2\u0115\u0116\7\16\2\2\u0116\u0117\7\30"+
		"\2\2\u0117\u0118\5J&\2\u0118\u0119\b\32\1\2\u0119\63\3\2\2\2\u011a\u011b"+
		"\7\17\2\2\u011b\u011c\7\30\2\2\u011c\u011d\5J&\2\u011d\u011e\b\33\1\2"+
		"\u011e\65\3\2\2\2\u011f\u0120\7\f\2\2\u0120\u0121\7\30\2\2\u0121\u0122"+
		"\5H%\2\u0122\u0123\b\34\1\2\u0123\67\3\2\2\2\u0124\u0125\7\25\2\2\u0125"+
		"\u0126\7\30\2\2\u0126\u0127\5H%\2\u0127\u0128\b\35\1\2\u01289\3\2\2\2"+
		"\u0129\u012a\7\n\2\2\u012a\u012b\7\30\2\2\u012b\u012c\5J&\2\u012c\u012d"+
		"\b\36\1\2\u012d;\3\2\2\2\u012e\u012f\7\20\2\2\u012f\u0130\7\30\2\2\u0130"+
		"\u0131\5L\'\2\u0131\u0132\b\37\1\2\u0132=\3\2\2\2\u0133\u0134\7\21\2\2"+
		"\u0134\u0135\7\30\2\2\u0135\u0136\5R*\2\u0136?\3\2\2\2\u0137\u0138\7\22"+
		"\2\2\u0138\u0139\7\30\2\2\u0139\u013a\5H%\2\u013aA\3\2\2\2\u013b\u013c"+
		"\7\23\2\2\u013c\u013d\7\30\2\2\u013d\u013e\5T+\2\u013eC\3\2\2\2\u013f"+
		"\u0140\7\24\2\2\u0140\u0141\7\30\2\2\u0141\u0142\5H%\2\u0142E\3\2\2\2"+
		"\u0143\u014a\5H%\2\u0144\u014a\5J&\2\u0145\u014a\5L\'\2\u0146\u014a\5"+
		"P)\2\u0147\u014a\5R*\2\u0148\u014a\5T+\2\u0149\u0143\3\2\2\2\u0149\u0144"+
		"\3\2\2\2\u0149\u0145\3\2\2\2\u0149\u0146\3\2\2\2\u0149\u0147\3\2\2\2\u0149"+
		"\u0148\3\2\2\2\u014aG\3\2\2\2\u014b\u014c\7\31\2\2\u014c\u014d\5\4\3\2"+
		"\u014d\u014e\7\31\2\2\u014e\u014f\b%\1\2\u014f\u0156\3\2\2\2\u0150\u0151"+
		"\7\34\2\2\u0151\u0152\5\4\3\2\u0152\u0153\7\35\2\2\u0153\u0154\b%\1\2"+
		"\u0154\u0156\3\2\2\2\u0155\u014b\3\2\2\2\u0155\u0150\3\2\2\2\u0156I\3"+
		"\2\2\2\u0157\u0158\7\31\2\2\u0158\u0159\7\36\2\2\u0159\u015a\7\31\2\2"+
		"\u015a\u0162\b&\1\2\u015b\u015c\7\34\2\2\u015c\u015d\7\36\2\2\u015d\u015e"+
		"\7\35\2\2\u015e\u0162\b&\1\2\u015f\u0160\7\36\2\2\u0160\u0162\b&\1\2\u0161"+
		"\u0157\3\2\2\2\u0161\u015b\3\2\2\2\u0161\u015f\3\2\2\2\u0162K\3\2\2\2"+
		"\u0163\u0164\7\31\2\2\u0164\u0165\5N(\2\u0165\u0166\7\31\2\2\u0166\u0167"+
		"\b\'\1\2\u0167\u0170\3\2\2\2\u0168\u0169\7\34\2\2\u0169\u016a\5N(\2\u016a"+
		"\u016b\7\35\2\2\u016b\u016c\b\'\1\2\u016c\u0170\3\2\2\2\u016d\u016e\7"+
		"\36\2\2\u016e\u0170\b\'\1\2\u016f\u0163\3\2\2\2\u016f\u0168\3\2\2\2\u016f"+
		"\u016d\3\2\2\2\u0170M\3\2\2\2\u0171\u0172\t\3\2\2\u0172O\3\2\2\2\u0173"+
		"\u0174\7\31\2\2\u0174\u0175\7\36\2\2\u0175\u0176\7\27\2\2\u0176\u0177"+
		"\7\27\2\2\u0177\u0178\7\36\2\2\u0178\u0179\7\31\2\2\u0179\u0182\b)\1\2"+
		"\u017a\u017b\7\34\2\2\u017b\u017c\7\36\2\2\u017c\u017d\7\27\2\2\u017d"+
		"\u017e\7\27\2\2\u017e\u017f\7\36\2\2\u017f\u0180\7\35\2\2\u0180\u0182"+
		"\b)\1\2\u0181\u0173\3\2\2\2\u0181\u017a\3\2\2\2\u0182Q\3\2\2\2\u0183\u0184"+
		"\7\31\2\2\u0184\u0185\7\36\2\2\u0185\u0186\7\27\2\2\u0186\u0187\7\36\2"+
		"\2\u0187\u0188\7\31\2\2\u0188\u0190\b*\1\2\u0189\u018a\7\34\2\2\u018a"+
		"\u018b\7\36\2\2\u018b\u018c\7\27\2\2\u018c\u018d\7\36\2\2\u018d\u018e"+
		"\7\35\2\2\u018e\u0190\b*\1\2\u018f\u0183\3\2\2\2\u018f\u0189\3\2\2\2\u0190"+
		"S\3\2\2\2\u0191\u0192\7\31\2\2\u0192\u0193\5\6\4\2\u0193\u0194\7\31\2"+
		"\2\u0194\u0195\b+\1\2\u0195\u019c\3\2\2\2\u0196\u0197\7\34\2\2\u0197\u0198"+
		"\5\6\4\2\u0198\u0199\7\35\2\2\u0199\u019a\b+\1\2\u019a\u019c\3\2\2\2\u019b"+
		"\u0191\3\2\2\2\u019b\u0196\3\2\2\2\u019cU\3\2\2\2\30Ybjq\u0093\u009a\u00a2"+
		"\u00b2\u00b9\u00c4\u00d4\u00db\u00e5\u00f3\u00fa\u0149\u0155\u0161\u016f"+
		"\u0181\u018f\u019b";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}